/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSwapGuardSite
import Vegas.Game.OnePacketPublishedBindings
import Vegas.Game.OnePacketProjectedDecision
import Vegas.Source.CellSwapDebt

/-! # The swap guard toward a forced witness

Fix a native history `h` and an intended history `second`, with decoded point
`p` of `h` and state `q` of `second`, that one player `who` observes alike, and
take the swap between `p` and `q` at the table of handles accepted at the end of
`h`. Unlike `Vegas.swapGuardState_of_replay`, `h` need not replay an intended
history.

* The inputs of `h` are those of a setup draw whose cells its decoded point
  finds (`Vegas.decoded_initialCellsAt`), and `q` finds the cells of a supported
  setup draw (`Vegas.exists_initialCellsAt`), so they are allowed when the
  initial handles are compatible with the swap
  (`Vegas.inputs_mem_swapAllowed_of_drawn`).
* A completed reveal publishes a value at `q`, hence at `p`, where the revealed
  commitment then holds that value, since publications carry their bindings or
  fail; a ready reveal is `who`'s own. So `p` and `q` agree on every binding a
  ready or completed reveal reads (`Vegas.bindingCellsAgree_of_decoded`), and
  the swap guard holds at the end of `h`
  (`Vegas.swapGuardState_of_decoded`).
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The current context of a program with distinct names has distinct names. -/
theorem nodup_currentConfig : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (Γ.map Prod.fst).Nodup →
    (state : ProtocolState program) → ((currentConfig program state).1.map Prod.fst).Nodup
  | _, _, .ret _, unique, _ => unique
  | _, _, .sample _ fresh _ next, unique, state => by
      cases state with
      | inl _ => exact unique
      | inr rest => exact nodup_currentConfig next (List.nodup_cons.mpr ⟨fresh, unique⟩) rest
  | _, _, .commit _ _ fresh _ next, unique, state => by
      cases state with
      | inl _ => exact unique
      | inr rest => exact nodup_currentConfig next (List.nodup_cons.mpr ⟨fresh, unique⟩) rest
  | _, _, .reveal _ _ _ fresh _ _ next, unique, state => by
      cases state with
      | inl _ => exact unique
      | inr rest => exact nodup_currentConfig next (List.nodup_cons.mpr ⟨fresh, unique⟩) rest

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem config_revealedInto_iff {Γ : SourceCtx Player L} {revelations : Revelations Γ}
    {left right : Config Player L Γ} (leftEq : @left.revelations = @revelations)
    (rightEq : @right.revelations = @revelations) {owner : Player} {payload : L.Ty}
    {name published : VarId} :
    left.RevealedInto owner payload name published ↔
      right.RevealedInto owner payload name published := by
  obtain ⟨leftState, leftRegistry, leftRevelations, leftHistory⟩ := left
  obtain ⟨rightState, rightRegistry, rightRevelations, rightHistory⟩ := right
  dsimp only at leftEq rightEq
  subst leftEq rightEq
  exact Iff.rfl

/-- **Revelation records are static**: points at the same position carrying the
publication status of their program point record the same revelations. -/
theorem revealedInto_iff_of_staticAt {owner : Player} {payload : L.Ty} {name published : VarId} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (registry : Registry Γ) →
    (revelations : Revelations Γ) → (left right : ProtocolState program) →
    StaticAt program registry revelations left → StaticAt program registry revelations right →
    SameShape program left right →
      (RevealedInto program left owner payload name published ↔
        RevealedInto program right owner payload name published)
  | _, _, .ret _, _, _, _, _, leftStatic, rightStatic, _ =>
      config_revealedInto_iff leftStatic.2 rightStatic.2
  | _, _, .sample _ _ _ next, _, _, left, right, leftStatic, rightStatic, shape => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_revealedInto_iff leftStatic.2 rightStatic.2
          | inr _ => exact shape.elim
      | inr first =>
          cases right with
          | inl _ => exact shape.elim
          | inr second =>
              exact revealedInto_iff_of_staticAt next _ _ first second leftStatic rightStatic shape
  | _, _, .commit _ _ _ _ next, _, _, left, right, leftStatic, rightStatic, shape => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_revealedInto_iff leftStatic.2 rightStatic.2
          | inr _ => exact shape.elim
      | inr first =>
          cases right with
          | inl _ => exact shape.elim
          | inr second =>
              exact revealedInto_iff_of_staticAt next _ _ first second leftStatic rightStatic shape
  | _, _, .reveal _ _ _ _ _ _ next, _, _, left, right, leftStatic, rightStatic, shape => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_revealedInto_iff leftStatic.2 rightStatic.2
          | inr _ => exact shape.elim
      | inr first =>
          cases right with
          | inl _ => exact shape.elim
          | inr second =>
              exact revealedInto_iff_of_staticAt next _ _ first second leftStatic rightStatic shape

end Vegas.SourceProgram.ProtocolState

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  [DecidableEq (CellTy Player L)]

/-- **The inputs of a native history** are those of a setup draw whose cells
its decoded point finds. -/
theorem decoded_initialCellsAt : ∀ {state}
    (_ : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    (control : (application setup leaks).Control), state = some control →
    ∃ initial ∈ setup.initialLaw.support,
      control.execution.application.config.inputs = setup.eventInputs initial ∧
      ∃ point, decodedPoint setup control.execution.application.config = some point ∧
        InitialCellsAt initial point
  | _, .start, _, current => by cases current
  | _, .extend (source := before) prior joint _ realized, control, current => by
      have recursive := fun next same => decoded_initialCellsAt prior next same
      subst current
      change some control ∈ ((application setup leaks).transition (initialLaw setup) horizon
        scheduler before joint).support at realized
      cases before with
      | none =>
          rw [ReactiveApplication.transition, PMF.support_map] at realized
          obtain ⟨drawn, drawnMember, drawnEq⟩ := realized
          cases Option.some.inj drawnEq
          have drawnSupport : drawn ∈ (initialLaw setup).support := drawnMember
          rw [initialLaw, serviceInitialLaw, PMF.support_map] at drawnSupport
          obtain ⟨initial, member, rfl⟩ := drawnSupport
          exact ⟨initial, member, rfl, _, decodedPoint_initial initial,
            initialCellsAt_entry initial⟩
      | some current =>
          obtain ⟨initial, member, inputsEq, point, decoded, found⟩ := recursive current rfl
          have step := transition_configStep (initialLaw setup) horizon scheduler current
            control joint realized
          have sameInputs : control.execution.application.config.inputs =
              current.execution.application.config.inputs := by
            rcases step with same | ⟨other, ready, action, completed⟩
            · rw [same]
            · rw [EventGraph.Config.step, PMF.support_map] at completed
              obtain ⟨_, _, completedEq⟩ := completed
              exact (congrArg EventGraph.Config.inputs completedEq).symm
          refine ⟨initial, member, sameInputs.trans inputsEq, ?_⟩
          rcases step with same | ⟨event, ready, action, completed⟩
          · exact ⟨point, by rw [same]; exact decoded, found⟩
          · obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
              (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler prior current rfl
            obtain ⟨before, target, beforeEq, afterEq, reached⟩ :=
              decodedPoint_step residual event ready action _ completed
            rw [decoded, Option.some.injEq] at beforeEq
            subst beforeEq
            exact ⟨target, afterEq, initialCellsAt_step reached found⟩

variable {p q : ProtocolState setup.program}
  {publicAgree : PublicCellsAgree setup p q} {succeed : CommitmentCellsSucceed setup p q}

/-- **The inputs of a native history are allowed** by the swap between its
decoded point and a point finding the cells of a supported setup draw, when the
initial handles are compatible with the swap. -/
theorem inputs_mem_swapAllowed_of_drawn
    (drawn : ∃ other ∈ setup.initialLaw.support, InitialCellsAt other q)
    (handlePairs : Handle (graph setup) → Option (Raw L × Raw L))
    (compatible : (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
      handlePairs).InitialHandlesCompatible)
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (decodedP : decodedPoint setup control.execution.application.config = some p) :
    control.execution.application.config.inputs ∈
      swapAllowed (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) := by
  obtain ⟨initial, member, inputsEq, point, pointEq, found⟩ :=
    decoded_initialCellsAt trace control rfl
  rw [decodedP, Option.some.injEq] at pointEq
  subst pointEq
  obtain ⟨other, otherMember, otherFound⟩ := drawn
  have drawnMember : ∀ draw ∈ setup.initialLaw.support,
      EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs draw) ∈
        (initialLaw setup).support := fun draw drawMember => by
    rw [initialLaw, serviceInitialLaw, PMF.support_map]
    exact ⟨draw, drawMember, rfl⟩
  refine ⟨_, drawnMember initial member, inputsEq.symm, ?_⟩
  rw [State.swap_initial _ compatible]
  have swapped : (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).inputs
      (setup.eventInputs initial) = setup.eventInputs other :=
    funext (inputs_betweenPairs found otherFound)
  rw [swapped]
  exact drawnMember other otherMember

/-- **Ready or completed reveals read agreeing commitments.** At the end of a
native history whose decoded point `p` a player `who` observes like the state
`q` of an intended history, every completed resolve event reads a commitment
both points hold alike, and so does every ready resolve event of `who`. -/
theorem bindingCellsAgree_of_decoded (wellFormed : setup.WellFormed)
    {second : setup.intendedProtocol.History} (secondState : second.state = some q)
    (who : Player)
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program q)
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (decodedP : decodedPoint setup control.execution.application.config = some p)
    (staticQ : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) q)
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
  · have revealedP := decodedPoint_revealedInto decodedP completed outputEq codeEq
    have staticP := decodedPoint_staticAt decodedP
    have intendedQ := intended_of_history wellFormed second.trace q secondState
    obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
      (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler trace control rfl
    have revealedQ := (ProtocolState.revealedInto_iff_of_staticAt setup.program _ _ p q staticP
      staticQ (ProtocolState.sameShape_of_observe_eq who setup.program p q sameView)).mp revealedP
    have bindingQ := ProtocolState.cell?_eq_of_revealedInto intendedQ revealedQ
    have publishedSame := visibleCellsAgree_of_observe sameView (eventCell setup.program event).1
      (kind := .publication payload) trivial
    obtain ⟨value, valueEq⟩ : ∃ value, ProtocolState.cell? setup.program q
        (fieldCell setup binding.field).1 (.commitment owner payload) = some (.success value) := by
      obtain ⟨source, _, _⟩ := revealedQ
      have found : ProtocolState.cell? setup.program q (fieldCell setup binding.field).1
          (.commitment owner payload) =
            some ((ProtocolState.currentConfig setup.program q).2.state.get source) := by
        rw [ProtocolState.cell?_eq_currentConfig]
        exact State.cell?_eq_of_hasVar source
          (ProtocolState.nodup_currentConfig setup.program setup.namesNodup q) _
      obtain ⟨value, success⟩ := ProtocolState.cell?_commitment_success intendedQ found
      exact ⟨value, found.trans (congrArg some success)⟩
    have publishedP : ProtocolState.cell? setup.program p (eventCell setup.program event).1
        (.publication payload) = some (.success value) := by
      rw [publishedSame, ← bindingQ, valueEq]
    obtain ⟨holdsRank, ⟨holdsResidual⟩, holds⟩ := decodedState_publishesOrFails
      (failureProfile setup.program) (bounds.onePacketMenu (runtime setup) leaks) horizon
      scheduler trace control rfl
    have publishesP : ProtocolState.PublishesOrFails setup.program p := by
      have point := holds _ holdsResidual.decode
      have samePoint := Option.some.inj ((decodedPoint_eq holdsResidual).symm.trans decodedP)
      rw [← samePoint]
      exact point
    rw [ProtocolState.cell?_eq_of_published publishesP
      (ProtocolState.nodup_currentConfig setup.program setup.namesNodup p) revealedP publishedP,
      valueEq]

/-- **The swap guard toward a point.** At the end of a native history with
decoded point `p`, the swap between `p` and a point `q` finding the cells of a
supported setup draw, at the table of handles accepted at the end, is guarded
when `p` and `q` agree on the commitment every ready or completed reveal reads. -/
theorem swapGuardState_of_agree
    (drawn : ∃ other ∈ setup.initialLaw.support, InitialCellsAt other q)
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (decodedP : decodedPoint setup control.execution.application.config = some p)
    (agree : ∀ event, (control.execution.application.config.cut.Ready event ∨
        event ∈ control.execution.application.config.cut.completed) →
      ∀ owner payload binding checks outputEq codeEq,
        nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
          ProtocolState.cell? setup.program p (fieldCell setup binding.field).1
              (.commitment owner payload) =
            ProtocolState.cell? setup.program q (fieldCell setup binding.field).1
              (.commitment owner payload))
    {table : AcceptedHandles (graph setup)}
    (tableEq : control.execution.application.accepted = table) :
    SwapGuardState setup (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
        (betweenHandlePairs setup p q table))
      (swapAllowed (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
        (betweenHandlePairs setup p q table))) (some control) := by
  subst tableEq
  have injective := acceptedInjective_of_trace bounds trace
  refine ⟨?_, fun event candidate accepted =>
    bindCompatible_betweenHandlePairs injective accepted, fun event active =>
    revealFixed_between injective _ (fun _ _ held => held) event (agree event active),
    fun player recalled member submission sent => ?_, HiddenSwap.expired_ofPairs _ _ _⟩
  · exact inputs_mem_swapAllowed_of_drawn drawn _
      (initialHandlesCompatible_betweenHandlePairs injective
        (fun _ _ _ layoutEq => accepted_initial_of_trace trace layoutEq))
      trace decodedP
  · cases owned : submission.evidence with
    | none | forward => trivial
    | owned fact =>
        change EventGraph.pairSwap (betweenHandlePairs setup p q
          control.execution.application.accepted fact.handle) fact.raw = fact.raw
        obtain ⟨event, owner, payload, binding, checks, outputEq, codeEq, view, active,
          onlyField⟩ := certificate_field bounds trace player recalled member submission sent
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

/-- **The swap guard toward an intended history.** At the end of a native
history whose decoded point `p` a player `who` observes like the state `q` of an
intended history, the swap between `p` and `q`, at the table of handles
accepted at the end, is guarded, provided every ready resolve event there
belongs to `who`. -/
theorem swapGuardState_of_decoded (wellFormed : setup.WellFormed)
    {second : setup.intendedProtocol.History} (secondState : second.state = some q)
    (who : Player)
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program q)
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (decodedP : decodedPoint setup control.execution.application.config = some p)
    (staticQ : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) q)
    (readyOwn : ∀ event, control.execution.application.config.cut.Ready event →
      ∀ owner payload binding checks outputEq codeEq,
        nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
          owner = who)
    {table : AcceptedHandles (graph setup)}
    (tableEq : control.execution.application.accepted = table) :
    SwapGuardState setup (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
        (betweenHandlePairs setup p q table))
      (swapAllowed (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
        (betweenHandlePairs setup p q table))) (some control) :=
  swapGuardState_of_agree (exists_initialCellsAt second.trace secondState) trace decodedP
    (fun event active owner payload binding checks outputEq codeEq view =>
      bindingCellsAgree_of_decoded (event := event) (owner := owner) (payload := payload)
        (binding := binding) (checks := checks) (outputEq := outputEq) (codeEq := codeEq)
        wellFormed secondState who sameView trace decodedP staticQ readyOwn active view)
    tableEq

end Vegas
