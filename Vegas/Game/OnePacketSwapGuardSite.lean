/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketAcceptedInjective
import Vegas.Game.OnePacketSwapInputs

/-! # The swap guard along a replayed history

Fix two intended points `p` and `q` one player `who` observes alike, and a
native history whose intended replay ends at `p`. Take the swap between `p` and
`q` at the table of handles accepted at the end of the history. The swap guard
holds at the end of the history (`Vegas.swapGuardState_of_replay`) when every
ready resolve event belongs to `who`:

* the inputs are allowed, since the initial handles are compatible with the swap
  (`Vegas.initialHandlesCompatible_betweenHandlePairs`);
* accepted commitments are compatible, since the table is injective;
* a completed reveal reads a commitment both points reveal alike, and a ready
  reveal of `who` reads a commitment `who` sees, so every ready or completed
  reveal is fixed (`Vegas.bindingCellsAgree_of_replay`);
* an owned evidence request in recall opens a ready or completed reveal whose
  binding is the only field accepting the requested handle, so the request is
  fixed.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- **Initial binding inputs keep their initial handles** along every history. -/
theorem accepted_initial_of_trace {control : (application setup runtime leaks).Control}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    {input : (graph setup).InputId} {owner : Player} {payload : L.Ty}
    (layoutEq : (graph setup).inputLayout input = .binding owner payload) :
    control.execution.application.accepted (.inl input) = some (owner, .initial input) := by
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have grows := acceptedGrows_step (runtime := runtime) (setup := setup) leaks
  have invariant : (application setup runtime leaks).Invariant
      (fun state => state.accepted (.inl input) = some (owner, .initial input)) :=
    ⟨fun state who material held => grows.submit state who material _ _ held,
      fun state message next held handled => grows.handle state message next handled _ _ held,
      fun state command next held reached => grows.environment state command next reached _ _
        held⟩
  refine invariant.history (initialLaw setup) horizon scheduler (fun state member => ?_) rawTrace
  rw [initialLaw, serviceInitialLaw, PMF.support_map] at member
  obtain ⟨_, _, rfl⟩ := member
  exact State.initial_accepted_binding _ input owner payload layoutEq

variable [DecidableEq (CellTy Player L)] {p q : ProtocolState setup.program}
  {publicAgree : PublicCellsAgree setup p q} {succeed : CommitmentCellsSucceed setup p q}

omit [Fintype Player] in
/-- **Initial handles are compatible with the swap** at an injective table
accepting every initial binding input's handle. -/
theorem initialHandlesCompatible_betweenHandlePairs {table : AcceptedHandles (graph setup)}
    (injective : AcceptedInjective table)
    (initialAccepted : ∀ input owner payload,
      (graph setup).inputLayout input = .binding owner payload →
        table (.inl input) = some (owner, .initial input)) :
    (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
      (betweenHandlePairs setup p q table)).InitialHandlesCompatible := by
  apply HiddenSwap.initialHandlesCompatible_ofPairs
  intro input owner payload layoutEq
  have handleEq := betweenHandlePairs_of_accepted (first := p) (second := q) injective
    (initialAccepted input owner payload layoutEq)
  have fieldEq : (graph setup).layout (.inl input) = .binding owner payload := layoutEq
  have kind := cellField_eq_binding ((layout_fieldCell setup (.inl input)).symm.trans fieldEq)
  have cell : fieldCell setup (.inl input) =
      ((fieldCell setup (.inl input)).1, .commitment owner payload) := Prod.ext rfl kind
  generalize (fieldCell setup (.inl input)).1 = name at cell
  rw [cell] at handleEq
  have pairEq := betweenPair_eq (first := p) (second := q) cell fieldEq
  change (betweenPairs publicAgree succeed).pair (.inl input) = _ at pairEq
  cases foundFirst : ProtocolState.cell? setup.program p name (.commitment owner payload) with
  | none =>
      rw [foundFirst] at pairEq
      simp only [commitmentRawPair, foundFirst] at handleEq
      exact Or.inl ⟨pairEq.trans (transportPair_none _), handleEq⟩
  | some firstValue =>
      cases foundSecond : ProtocolState.cell? setup.program q name
          (.commitment owner payload) with
      | none =>
          rw [foundFirst, foundSecond] at pairEq
          simp only [commitmentRawPair, foundFirst, foundSecond] at handleEq
          exact Or.inl ⟨pairEq.trans (transportPair_none _), handleEq⟩
      | some secondValue =>
          rw [foundFirst, foundSecond] at pairEq
          by_cases same : firstValue = secondValue
          · subst same
            simp only [cellPair, ↓reduceIte] at pairEq
            refine Or.inl ⟨pairEq.trans (transportPair_none _), ?_⟩
            rw [handleEq]
            cases firstValue <;> simp [commitmentRawPair, foundFirst, foundSecond]
          · obtain ⟨firstOk, secondOk⟩ := succeed name owner payload firstValue secondValue
              foundFirst foundSecond same
            cases firstValue with
            | failure => exact (firstOk rfl).elim
            | success left =>
                cases secondValue with
                | failure => exact (secondOk rfl).elim
                | success right =>
                    have distinct : left ≠ right := fun equal => same (by rw [equal])
                    simp only [cellPair, same, ↓reduceIte, transportPair_some] at pairEq
                    refine Or.inr ⟨left, right, pairEq, ?_⟩
                    rw [handleEq]
                    simp only [commitmentRawPair, foundFirst, foundSecond, distinct,
                      ↓reduceIte]

/-- **Ready or completed reveals read agreeing commitments.** Along a native
history replaying an intended history that ends at `p`, every completed resolve
event reads a commitment both points reveal alike, and every ready resolve event
of `who` reads a commitment `who` sees. -/
theorem bindingCellsAgree_of_replay (wellFormed : setup.WellFormed)
    {first second : setup.intendedProtocol.History} (firstState : first.state = some p)
    (secondState : second.state = some q) (who : Player)
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program q)
    {control : (application setup runtime leaks).Control}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (replayed : intendedHistory? setup runtime leaks bounds horizon scheduler trace = some first)
    (readyOwn : ∀ event, control.execution.application.config.cut.Ready event →
      ∀ owner payload binding checks outputEq codeEq,
        nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
          owner = who)
    {event : (graph setup).EventId}
    (active : control.execution.application.config.cut.Ready event ∨
      event ∈ control.execution.application.config.cut.completed)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq) :
    ProtocolState.cell? setup.program p (fieldCell setup binding.field).1
        (.commitment owner payload) =
      ProtocolState.cell? setup.program q (fieldCell setup binding.field).1
        (.commitment owner payload) := by
  rcases active with ready | completed
  · have ownerEq := readyOwn event ready owner payload binding checks outputEq codeEq view
    subst ownerEq
    exact visibleCellsAgree_of_observe sameView _
      (show (cellField (CellTy.commitment owner payload)).VisibleTo owner from rfl)
  · have decoded : decodedPoint setup control.execution.application.config = some p := by
      rw [← firstState, intendedHistory?_state (runtime := runtime) trace replayed]
      rfl
    exact revealedCellsAgree_of_observe wellFormed firstState secondState who sameView
      (decodedPoint_revealedInto decoded completed outputEq codeEq)

/-- **The swap guard at the end of a replayed history.** Along a native history
replaying an intended history that ends at `p`, the swap between `p` and a point
`q` that `who` observes alike, at the table of handles accepted at the end, is
guarded at the end, provided every ready resolve event there belongs to
`who`. -/
theorem swapGuardState_of_replay (wellFormed : setup.WellFormed)
    {first second : setup.intendedProtocol.History} (firstState : first.state = some p)
    (secondState : second.state = some q) (who : Player)
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program q)
    {control : (application setup runtime leaks).Control}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (replayed : intendedHistory? setup runtime leaks bounds horizon scheduler trace = some first)
    (readyOwn : ∀ event, control.execution.application.config.cut.Ready event →
      ∀ owner payload binding checks outputEq codeEq,
        nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
          owner = who)
    {table : AcceptedHandles (graph setup)}
    (tableEq : control.execution.application.accepted = table) :
    SwapGuardState setup runtime (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
        (betweenHandlePairs setup p q table))
      (swapAllowed (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
        (betweenHandlePairs setup p q table))) (some control) := by
  subst tableEq
  have injective := acceptedInjective_of_trace (runtime := runtime) bounds trace
  have agree := fun event active owner payload binding checks outputEq codeEq view =>
    bindingCellsAgree_of_replay (runtime := runtime) (event := event) (owner := owner) (payload :=
      payload)
      (binding := binding) (checks := checks) (outputEq := outputEq) (codeEq := codeEq)
      wellFormed firstState secondState who sameView trace replayed readyOwn active view
  refine ⟨?_, fun event candidate accepted =>
    bindCompatible_betweenHandlePairs injective accepted, fun event active =>
    revealFixed_between injective _ (fun _ _ held => held) event (agree event active),
    fun player recalled member submission sent => ?_, HiddenSwap.expired_ofPairs _ _ _⟩
  · exact inputs_mem_swapAllowed (runtime := runtime) firstState secondState _
      (initialHandlesCompatible_betweenHandlePairs injective
        (fun _ _ _ layoutEq => accepted_initial_of_trace (runtime := runtime) trace layoutEq))
      trace replayed
  · cases owned : submission.evidence with
    | none | forward => trivial
    | owned fact =>
        change EventGraph.pairSwap (betweenHandlePairs setup p q
          control.execution.application.accepted fact.handle) fact.raw = fact.raw
        obtain ⟨event, owner, payload, binding, checks, outputEq, codeEq, view, active,
          onlyField⟩ := certificate_field (runtime := runtime) bounds trace player recalled member
            submission sent
            fact owned
        by_cases found : ∃ field, control.execution.application.accepted field =
            some fact.handle
        · obtain ⟨field, accepted⟩ := found
          cases onlyField field accepted
          obtain ⟨name, _, _, cell⟩ := fieldCell_resolveBinding outputEq codeEq
          have same := agree event active owner payload binding checks outputEq codeEq view
          rw [cell] at same
          rw [betweenHandlePairs_of_accepted injective accepted, cell,
            commitmentRawPair_eq_none_of_agree same]
          rfl
        · unfold betweenHandlePairs
          simp only [found, ↓reduceDIte]
          rfl

end Vegas
