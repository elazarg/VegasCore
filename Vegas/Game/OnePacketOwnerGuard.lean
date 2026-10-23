/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketOwnerSwap
import Vegas.Game.OnePacketFailureBridge
import Vegas.Game.OnePacketDisclosureResolves
import Vegas.Game.AsyncDeviationForeign

/-! # The swap guard of the owner swap

Fix two information sites of a player `who` with the same late-delivery key, at
neither of which `who` owes a failure at the decoded point of any history, and
the owner swap between their views (`Vegas.ownerSwap`). The swap guard holds at
every history of the first site (`Vegas.ownerSwap_guard`), provided the setup
prior is closed under the swap of `who`'s inputs:

* the inputs are allowed: the initial handles of `who` keep the candidates of
  their inputs (`Vegas.initialSlots_of_trace`), so the swap of an initial state
  is the initial state of the swapped inputs;
* accepted commitments are compatible: every field accepting a handle of `who`
  stores a value whose candidate is the handle's meaning
  (`Vegas.ownBinding_candidate`), since a failed binding makes its owner owe a
  failure; so the pair at the field and the pair at the handle are the same
  transposition, or both absent (`Vegas.ownerPairs_of_accepted`);
* ready and completed reveals are fixed: a ready reveal of `who` is its turn,
  whose binding both keys deliver alike, and a completed reveal published the
  success its binding holds, or `who`'s reveal failed
  (`Vegas.RevealRecord`, `Vegas.revealRecord_history`), which is a debt;
* recalled owned requests are fixed: they name handles of the recalling player
  (`Vegas.ownedRequestsOwn_history`), and when that player is `who` the
  envelope carrying the fact is recalled at both sites, so the fact holds at
  both and the handle carries no pair.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

section Pairs

/-- A binding field of `who` is private to `who`. -/
theorem privateTo_of_binding {who : Player} {field : (graph setup).Field} {payload : L.Ty}
    (layoutEq : (graph setup).layout field = .binding who payload) : PrivateTo who field := by
  refine ⟨?_, ?_⟩
  · unfold EventGraph.fieldVisibleTo
    rw [layoutEq]
    rfl
  · unfold EventGraph.fieldPublic
    rw [layoutEq]
    exact id

omit [IExpr.ResultTypes L] in
open Classical in
private theorem pairs_of_candidateOfValue (who : Player) (payload : L.Ty) :
    ∀ (kind : EventGraph.EventField Player L) (kindEq : kind = .binding who payload)
      (left right : kind.Value),
      ((if left = right ∨ kind.IsFailure left ∨ kind.IsFailure right then none
          else some (left, right)) = none ∧
        (match State.candidateOfValue who kind left, State.candidateOfValue who kind right with
          | .openable first, .openable second =>
              if first = second then none else some (first, second)
          | _, _ => none) = none) ∨
      ∃ first second : L.Val payload,
        (if left = right ∨ kind.IsFailure left ∨ kind.IsFailure right then none
          else some (left, right)) =
          some (cast (congrArg EventGraph.EventField.Value kindEq.symm) (.success first),
            cast (congrArg EventGraph.EventField.Value kindEq.symm) (.success second)) ∧
        (match State.candidateOfValue who kind left, State.candidateOfValue who kind right with
          | .openable first, .openable second =>
              if first = second then none else some (first, second)
          | _, _ => none) = some (⟨payload, first⟩, ⟨payload, second⟩) := by
  rintro _ rfl left right
  change PublicationResult (L.Val payload) at left right
  cases left with
  | failure =>
      left
      simp [State.candidateOfValue, EventGraph.EventField.IsFailure]
  | success first =>
      cases right with
      | failure =>
          left
          simp [State.candidateOfValue, EventGraph.EventField.IsFailure]
      | success second =>
          by_cases same : first = second
          · subst same
            left
            simp [State.candidateOfValue]
          · right
            refine ⟨first, second, ?_, ?_⟩
            · simp [EventGraph.EventField.IsFailure, same]
            · simp [State.candidateOfValue, same]

/-- **Owner pairs at a binding of `who`.** When both views store a value at a
binding field of `who` and hold, at a slot, the candidate of that value, the
owner pairs carry either no pair at the field and the handle, or the two typed
successes and their raw values. -/
theorem ownerPairs_of_candidateOfValue {who : Player}
    {first second : PlayerView (graph setup)} {field : (graph setup).Field} {payload : L.Ty}
    (layoutEq : (graph setup).layout field = .binding who payload)
    {slot : CandidateSlot (graph setup)} {left right : ((graph setup).layout field).Value}
    (firstStore : first.observation.store field = some left)
    (secondStore : second.observation.store field = some right)
    (firstCandidate : first.candidates slot = State.candidateOfValue who _ left)
    (secondCandidate : second.candidates slot = State.candidateOfValue who _ right) :
    ((ownerPairs who first second).pair field = none ∧
        ownerHandlePairs who first second (who, slot) = none) ∨
      ∃ firstValue secondValue : L.Val payload,
        (ownerPairs who first second).pair field =
          some (cast (congrArg EventGraph.EventField.Value layoutEq.symm) (.success firstValue),
            cast (congrArg EventGraph.EventField.Value layoutEq.symm)
              (.success secondValue)) ∧
        ownerHandlePairs who first second (who, slot) =
          some (⟨payload, firstValue⟩, ⟨payload, secondValue⟩) := by
  have privateTo := privateTo_of_binding layoutEq
  change ownerValuePair who first second field = none ∧ _ ∨
    ∃ firstValue secondValue : L.Val payload, ownerValuePair who first second field = _ ∧ _
  unfold ownerValuePair ownerHandlePairs
  simp only [privateTo, ↓reduceIte, firstStore, secondStore, firstCandidate, secondCandidate]
  exact pairs_of_candidateOfValue who payload _ layoutEq left right

end Pairs

end Vegas

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

section Initial

omit [Fintype Player] [IExpr.ResultTypes L] in
private theorem candidateOfValue_binding_ne_fresh (owner : Player) (payload : L.Ty) :
    ∀ (kind : EventGraph.EventField Player L) (_ : kind = .binding owner payload)
      (value : kind.Value), State.candidateOfValue owner kind value ≠ .fresh := by
  rintro _ rfl value
  change PublicationResult (L.Val payload) at value
  cases value <;> simp [State.candidateOfValue]

/-- **Initial slots keep the candidates of the inputs.** Along every history of
the one-packet game, the inputs are those of a setup draw, and the candidate at
the initial slot of each binding input is the candidate of the input value. -/
theorem initialSlots_of_trace {state}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state) :
    ∀ control : (application setup leaks).Control, state = some control →
      ∃ initial ∈ setup.initialLaw.support,
        control.execution.application.config.inputs = setup.eventInputs initial ∧
        ∀ input owner payload, (graph setup).inputLayout input = .binding owner payload →
          control.execution.application.candidates.lookup (owner, .initial input) =
            State.candidateOfValue owner ((graph setup).inputLayout input)
              (control.execution.application.config.inputs input) := by
  induction trace with
  | start => intro _ initialized; cases initialized
  | @extend before after prior joint legal realized ih =>
      intro control initialized
      subst initialized
      cases before with
      | none =>
          change some control ∈ ((application setup leaks).transition (initialLaw setup)
            horizon scheduler none joint).support at realized
          rw [ReactiveApplication.transition, PMF.support_map] at realized
          obtain ⟨drawn, drawnMember, drawnEq⟩ := realized
          cases Option.some.inj drawnEq
          have drawnSupport : drawn ∈ (initialLaw setup).support := drawnMember
          rw [initialLaw, serviceInitialLaw, PMF.support_map] at drawnSupport
          obtain ⟨initial, member, rfl⟩ := drawnSupport
          refine ⟨initial, member, rfl, fun input owner payload _ => ?_⟩
          exact State.initial_candidate _ owner (.initial input)
      | some current =>
          obtain ⟨initial, member, inputsEq, candidates⟩ := ih current rfl
          have step := transition_configStep (initialLaw setup) horizon scheduler current
            control joint realized
          have kept := (keepsFixedCandidates_step (runtime setup) leaks).transition
            (initialLaw setup) horizon scheduler current control joint realized
          have sameInputs : control.execution.application.config.inputs =
              current.execution.application.config.inputs := by
            rcases step with same | ⟨other, ready, action, completed⟩
            · rw [same]
            · rw [EventGraph.Config.step, PMF.support_map] at completed
              obtain ⟨_, _, completedEq⟩ := completed
              exact (congrArg EventGraph.Config.inputs completedEq).symm
          refine ⟨initial, member, sameInputs.trans inputsEq, fun input owner payload
            layoutEq => ?_⟩
          have before := candidates input owner payload layoutEq
          rw [kept _ (by
            rw [before]
            exact candidateOfValue_binding_ne_fresh owner payload _ layoutEq _), before,
            sameInputs]

end Initial

section Clean

omit [Fintype Player] in
private theorem get?_of_store {kind : EventGraph.EventField Player L}
    (ref : EventGraph.FieldRef (graph setup).layout kind)
    {store : EventGraph.Store (graph setup).layout} {value : ((graph setup).layout ref.field).Value}
    (stored : store ref.field = some value) :
    ref.get? store = some (cast (congrArg EventGraph.EventField.Value ref.layout_eq) value) := by
  rcases ref with ⟨field, layoutEq⟩
  subst layoutEq
  simp [EventGraph.FieldRef.get?, stored]

/-- The binding invariant holds along every history of the one-packet game. -/
private theorem bindingInvariant_of_trace {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control)) :
    control.execution.application.BindingInvariant :=
  ((runtime setup).reactiveBindingInvariant leaks).history (initialLaw setup) horizon scheduler
    (fun state member => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
      exact State.initial_bindingInvariant _)
    ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
      scheduler trace)

/-- **Accepted bindings of a debt-free owner hold the candidates of their
values.** Along a history of the one-packet game at whose decoded point `who`
owes no failure, every field that accepted a handle of `who` stores a value
whose candidate is the meaning of that handle: an initial binding keeps the
candidate of its input, and a binding event stores a success, since a failed
binding makes its owner owe a failure. -/
theorem ownBinding_candidate {who : Player} {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (debtFree : ∀ point, nativeDecodedState setup leaks (some control) = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    {field : (graph setup).Field} {handle : Handle (graph setup)}
    (accepted : control.execution.application.accepted field = some handle)
    (owned : handle.1 = who) :
    ∃ value, control.execution.application.config.store field = some value ∧
      control.execution.application.candidates.lookup handle =
        State.candidateOfValue who ((graph setup).layout field) value := by
  have valid := bindingInvariant_of_trace trace
  obtain ⟨payload, layoutEq⟩ := valid.accepted_typed field handle accepted
  rw [owned] at layoutEq
  cases field with
  | inl input =>
      have inputEq : (graph setup).inputLayout input = .binding who payload := layoutEq
      have initialAccepted := accepted_initial_of_trace trace inputEq
      rw [accepted] at initialAccepted
      cases Option.some.inj initialAccepted
      obtain ⟨_, _, _, candidates⟩ := initialSlots_of_trace trace control rfl
      exact ⟨_, rfl, candidates input who payload inputEq⟩
  | inr event =>
      obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
        (valid.accepted_present _ handle accepted)
      refine ⟨value, stored, ?_⟩
      let ref : EventGraph.FieldRef (graph setup).layout (.binding who payload) :=
        ⟨.inr event, layoutEq⟩
      have read := get?_of_store ref stored
      cases result : cast (congrArg EventGraph.EventField.Value layoutEq) value with
      | success bound =>
          rw [result] at read
          obtain ⟨found, foundAccepted, _, lookupEq⟩ := valid.success_provenance ref bound read
          change control.execution.application.accepted (.inr event) = some found at foundAccepted
          rw [accepted] at foundAccepted
          cases Option.some.inj foundAccepted
          rw [lookupEq]
          exact (State.candidateOfValue_binding_success _ value who payload layoutEq bound
            result).symm
      | failure =>
          exfalso
          rw [result] at read
          obtain ⟨rank, ⟨residual⟩, record⟩ := failedBindingRecord_history
            (failureProfile setup.program) horizon scheduler
            ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
              scheduler trace)
          have done := valid.accepted_complete event handle accepted
          have owes := record event done who payload layoutEq read _ residual.decode
          exact debtFree _ (decodedPoint_eq residual) owes

end Clean

section Reveals

variable (setup leaks) in
/-- **The reveal record.** The configuration decodes at a prefix, and every
completed reveal either published the success its binding holds, or its owner's
reveal failed at the decoded point. -/
def RevealRecord (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution) : Prop :=
  ∃ rank, Nonempty (SourceResidual setup profile rank execution.application.config) ∧
    ∀ event ∈ execution.application.config.cut.completed, ∀ owner payload binding checks
      outputEq codeEq,
      nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
      ∀ result, (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
          (.publication payload)).get? execution.application.config.store = some result →
        (∃ value, result = .success value ∧
          binding.get? execution.application.config.store = some (.success value)) ∨
        DecodedHolds (ProtocolState.RevealFailed owner setup.program) rank
          execution.application.config

omit [Fintype Player] in
/-- Completing a ready event keeps every stored field. -/
private theorem store_complete_of_some {config : (graph setup).Config}
    {event : (graph setup).EventId} (ready : config.cut.Ready event)
    (action : (graph setup).Action event) (output : ((graph setup).outputLayout event).Value)
    {field : (graph setup).Field} {value : ((graph setup).layout field).Value}
    (stored : config.store field = some value) :
    (config.complete event ready action output).store field = some value := by
  cases field with
  | inl input => exact stored
  | inr other =>
      have different : other ≠ event := by
        intro same
        subst same
        apply ready.1
        rw [← config.output_available]
        change (config.store (.inr other)).isSome
        rw [stored]
        rfl
      change (config.complete event ready action output).outputs other = some value
      rw [EventGraph.Config.complete_output_of_ne _ _ _ _ _ _ different]
      exact stored

omit [Fintype Player] in
private theorem get?_complete_of_some {config : (graph setup).Config}
    {event : (graph setup).EventId} (ready : config.cut.Ready event)
    (action : (graph setup).Action event) (output : ((graph setup).outputLayout event).Value)
    {kind : EventGraph.EventField Player L} (ref : EventGraph.FieldRef (graph setup).layout kind)
    {value : kind.Value} (read : ref.get? config.store = some value) :
    ref.get? (config.complete event ready action output).store = some value := by
  rcases ref with ⟨field, layoutEq⟩
  subst layoutEq
  change config.store field = some value at read
  exact store_complete_of_some ready action output read

omit [Fintype Player] in
/-- The output a completed resolve event writes is its resolution output. -/
private theorem step_resolve_output {config next : (graph setup).Config}
    {event : (graph setup).EventId} {ready : config.cut.Ready event}
    {action : (graph setup).Action event} {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (member : next ∈ (config.step event ready action).support) :
    ∃ result, EventGraph.EventCode.resolveOutput? binding checks
        (cast (congrArg EventGraph.EventField.Action outputEq) action) config.store =
          some result ∧
      next = config.complete event ready action
        (cast (congrArg EventGraph.EventField.Value outputEq.symm) result) := by
  have available : (EventGraph.EventCode.resolveOutput? binding checks
      (cast (congrArg EventGraph.EventField.Action outputEq) action) config.store).isSome =
        true := by
    apply EventGraph.EventCode.resolveOutput?_isSome
    intro field member
    apply config.read_available ready
    rw [← EventGraph.EventCode.readFields_cast outputEq ((graph setup).nodes event), codeEq]
    exact member
  obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp available
  refine ⟨result, resolved, ?_⟩
  have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
      (cast (congrArg EventGraph.EventField.Action outputEq) action) := by
    simp only [cast_cast, cast_eq]
  have stepEq := config.step_eq_map_of_code event ready outputEq _ codeEq
    (cast (congrArg EventGraph.EventField.Action outputEq) action) (PMF.pure result)
    (by rw [EventGraph.EventCode.resolve_eval?, resolved]; rfl)
  rw [PMF.pure_map, ← actionEq] at stepEq
  rw [stepEq, PMF.mem_support_pure_iff] at member
  exact member

omit [Fintype Player] in
/-- A successful resolution output publishes the success its binding holds. -/
private theorem binding_of_resolveOutput {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)} {disclose : Bool}
    {store : EventGraph.Store (graph setup).layout} {value : L.Val payload}
    (resolved : EventGraph.EventCode.resolveOutput? binding checks disclose store =
      some (.success value)) :
    binding.get? store = some (.success value) := by
  unfold EventGraph.EventCode.resolveOutput? at resolved
  cases bound : binding.get? store with
  | none => simp [bound] at resolved
  | some found =>
      rw [bound] at resolved
      cases disclose
      · cases accepted : EventGraph.GuardCheck.allAccepted? checks store .failure with
        | none => simp [accepted] at resolved
        | some verdict =>
            simp [accepted] at resolved
      · cases accepted : EventGraph.GuardCheck.allAccepted? checks store found with
        | none => simp [accepted] at resolved
        | some verdict =>
            cases verdict
            · simp [accepted] at resolved
            · have foundEq : found = .success value := by simpa [accepted] using resolved
              exact congrArg some foundEq

omit [Fintype Player] in
/-- The reveal record holds at every legal history of the default runtime,
under arbitrary responses and every scheduler. -/
theorem revealRecord_serviceInvariant (profile : BehavioralProfile setup.program)
    (scheduler : (application setup leaks).Scheduler) :
    (application setup leaks).ServiceInvariant scheduler (RevealRecord setup leaks profile) where
  respond execution who action valid := by
    have configEq := ((runtime setup).reactive_respond_application leaks execution who action).1
    unfold RevealRecord at valid ⊢
    rw [configEq]
    exact valid
  environment execution next command valid _ reached := by
    obtain ⟨rank, ⟨residual⟩, record⟩ := valid
    rcases environmentStep_configStep setup leaks execution next command reached with
      same | ⟨completed, ready, action, member⟩
    · refine ⟨rank, ?_, ?_⟩
      · rw [same]
        exact ⟨residual⟩
      · rw [same]
        exact record
    · have rankEq : completed.val = rank :=
        (ready_iff_rank setup _ rank residual.checkpoint.ordered completed).mp ready
      obtain ⟨successor, reachedPoint⟩ := residual.step completed ready action _ member
      have advanced : next.application.config.cut.IsPrefix (rank + 1) := by
        rw [execution.application.config.step_cut completed ready action _ member]
        exact residual.checkpoint.ordered.complete_at completed ready rankEq
      refine ⟨rank + 1, ⟨successor⟩, fun other done owner payload binding checks outputEq codeEq
        view result read => ?_⟩
      rw [execution.application.config.step_cut completed ready action _ member,
        EventOrder.Cut.mem_complete] at done
      rcases done with rfl | earlier
      · obtain ⟨output, resolved, nextEq⟩ := step_resolve_output outputEq codeEq member
        have written : result = output := by
          rw [nextEq] at read
          change cast _ ((execution.application.config.complete other ready action
            (cast (congrArg EventGraph.EventField.Value outputEq.symm) output)).outputs other) =
              _ at read
          rw [EventGraph.Config.complete_output_same] at read
          have castSome {A B : Type} (same : A = B) (value : A) :
              cast (congrArg Option same) (some value) = some (cast same value) := by
            cases same
            rfl
          rw [castSome (congrArg EventGraph.EventField.Value outputEq)] at read
          have castInverse {A B : Type} (same : A = B) (value : B) :
              cast same (cast same.symm value) = value := by
            cases same
            rfl
          rw [castInverse] at read
          exact (Option.some.inj read).symm
        subst written
        cases result with
        | success value =>
            left
            refine ⟨value, rfl, ?_⟩
            rw [nextEq]
            exact get?_complete_of_some ready action _ binding
              (binding_of_resolveOutput resolved)
        | failure =>
            right
            intro state decoded
            rw [successor.decode] at decoded
            obtain rfl := Option.some.inj decoded
            subst rankEq
            have nextDecoded := successor.decode
            unfold sourceServicePrefix? serviceSourcePrefix? at nextDecoded
            have owned : (graph setup).actor? other = some owner :=
              nodeView_resolve_actor outputEq codeEq
            exact ProtocolState.revealFailed_of_decode_failure setup.program other.val
              (ContextRefs.initial setup.context (outputLayout setup.program)) []
              (Revelations.initial setup.context) (outputRef setup.program) _ _ _ other.isLt
              owner payload outputEq nextDecoded
              ((eventOwner?_eq_actor setup.program other).trans owned)
              (by
                rw [nextEq]
                change (execution.application.config.complete other ready _ _).outputs
                  other = _
                rw [EventGraph.Config.complete_output_same])
      · have different : other ≠ completed := fun same => ready.1 (same ▸ earlier)
        obtain ⟨written, writtenEq⟩ := step_complete_of_mem member
        have kept : (⟨.inr other, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
            (.publication payload)).get? execution.application.config.store = some result := by
          rw [← read]
          apply EventGraph.FieldRef.get?_congr
          change execution.application.config.outputs other =
            next.application.config.outputs other
          rw [writtenEq, EventGraph.Config.complete_output_of_ne _ _ _ _ _ _ different]
        rcases record other earlier owner payload binding checks outputEq codeEq view result
            kept with ⟨value, resultEq, bound⟩ | failed
        · left
          refine ⟨value, resultEq, ?_⟩
          rw [writtenEq]
          exact get?_complete_of_some ready action _ binding bound
        · right
          exact residual.decodedHolds_configStep (revealFailed_stepClosed owner) failed
            (Or.inr ⟨completed, ready, action, member⟩) advanced

omit [Fintype Player] in
/-- The reveal record holds along every history of the default runtime from its
initial law. -/
theorem revealRecord_history (profile : BehavioralProfile setup.program)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    RevealRecord setup leaks profile control.execution :=
  (revealRecord_serviceInvariant profile scheduler).history (initialLaw setup) horizon
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      let residual := SourceResidual.initial setup profile initial
      refine ⟨0, ⟨residual⟩, fun event completed => ?_⟩
      have below := (residual.checkpoint.ordered.2 event).mp completed
      exact absurd below (Nat.not_lt_zero _)) trace

end Reveals

section Requests

variable (setup leaks) in
/-- **Owned requests name own handles.** Every recalled transmission requesting
owned evidence requests a fact about a handle of the recalling player. -/
def OwnedRequestsOwn (execution : (application setup leaks).Execution) : Prop :=
  ∀ who, ∀ recalled ∈ execution.recall who, ∀ submission,
    recalled.action.transmission = some submission →
    ∀ fact, submission.evidence = .owned fact → fact.handle.1 = who

omit [Fintype Player] in
private theorem handle_owner_of_normalize {who : Player}
    {candidates : CandidateSlot (graph setup) → CommitmentCandidate (Raw L)}
    {known : List (Message Player (WitnessedPacket (graph setup)))}
    {fact : OpeningFact (graph setup)}
    (normal : (EvidenceRequest.owned fact).normalize who candidates known = .owned fact) :
    fact.handle.1 = who := by
  cases resolved : (EvidenceRequest.owned fact).resolve who candidates known with
  | none =>
      rw [EvidenceRequest.normalize, resolved] at normal
      cases normal
  | some found =>
      simp only [EvidenceRequest.resolve] at resolved
      split at resolved
      · rename_i owned
        exact owned.1
      · cases resolved

/-- Owned requests name own handles along every history of the one-packet
game. -/
theorem ownedRequestsOwn_history
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control)) :
    OwnedRequestsOwn setup leaks control.execution :=
  (show (bounds.onePacketMenu (runtime setup) leaks).ServiceInvariant scheduler
      (OwnedRequestsOwn setup leaks) from
    { respond := fun execution who action valid member => by
        let app := application setup leaks
        intro observer recalled entryMember submission sent fact owned
        rw [respond_recall (runtime setup) leaks] at entryMember
        split at entryMember
        · rename_i same
          subst same
          rcases List.mem_append.mp entryMember with old | new
          · exact valid observer recalled old submission sent fact owned
          · obtain rfl := List.mem_singleton.mp new
            rcases action with ⟨transmission⟩
            change transmission = some submission at sent
            subst sent
            have normal := ((bounds.menu_mem (runtime setup) leaks observer _ _ _).mp
              ((bounds.mem_onePacketActions (runtime setup) leaks observer _ _ _).mp
                member).1).2
            have normalEvidence := congrArg (fun response : app.Action =>
              response.transmission.map WitnessedSubmission.evidence) normal
            simp only [ReactiveApplication.SubmissionNormalization.action,
              Option.map_some] at normalEvidence
            have request := Option.some.inj normalEvidence
            change submission.evidence.normalize observer (submission.call.candidateAfter observer
              (fun slot => execution.application.candidates.lookup (observer, slot)))
                (ReactiveApplication.ResponseMenu.knownPackets (execution.recall observer)
                  (execution.observe app observer)) = submission.evidence at request
            rw [owned] at request
            exact handle_owner_of_normalize request
        · exact valid observer recalled entryMember submission sent fact owned
      environment := fun execution next command valid _ reached => by
        intro observer recalled member
        rw [(application setup leaks).environmentStep_recall execution next command
          reached] at member
        exact valid observer recalled member }).history
    (initialLaw setup) horizon (fun _ _ _ _ member => (List.not_mem_nil member).elim) trace

end Requests

section Guard

/-- **Owner pairs at an accepted handle.** At two histories of the one-packet
game at whose decoded points `who` owes no failure, with the same accepted
handles, a field of `who` accepting a handle carries either no pair at the field
and the handle, or the two typed successes and their raw values. -/
theorem ownerPairs_of_accepted {who : Player} {first second : (application setup leaks).Control}
    (firstTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some first))
    (secondTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some second))
    (firstDebtFree : ∀ point, nativeDecodedState setup leaks (some first) = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (secondDebtFree : ∀ point, nativeDecodedState setup leaks (some second) = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (acceptedEq : first.execution.application.accepted = second.execution.application.accepted)
    {field : (graph setup).Field} {slot : CandidateSlot (graph setup)} {payload : L.Ty}
    (layoutEq : (graph setup).layout field = .binding who payload)
    (accepted : first.execution.application.accepted field = some (who, slot)) :
    let firstView := first.execution.application.playerView who
    let secondView := second.execution.application.playerView who
    ((ownerPairs who firstView secondView).pair field = none ∧
        ownerHandlePairs who firstView secondView (who, slot) = none) ∨
      ∃ firstValue secondValue : L.Val payload,
        (ownerPairs who firstView secondView).pair field =
          some (cast (congrArg EventGraph.EventField.Value layoutEq.symm) (.success firstValue),
            cast (congrArg EventGraph.EventField.Value layoutEq.symm)
              (.success secondValue)) ∧
        ownerHandlePairs who firstView secondView (who, slot) =
          some (⟨payload, firstValue⟩, ⟨payload, secondValue⟩) := by
  intro firstView secondView
  obtain ⟨left, leftStore, leftCandidate⟩ :=
    ownBinding_candidate firstTrace firstDebtFree accepted rfl
  obtain ⟨right, rightStore, rightCandidate⟩ :=
    ownBinding_candidate secondTrace secondDebtFree (acceptedEq ▸ accepted) rfl
  have visible := (privateTo_of_binding layoutEq).1
  exact ownerPairs_of_candidateOfValue layoutEq
    ((EventGraph.playerStore_of_visible _ who _ field visible).trans leftStore)
    ((EventGraph.playerStore_of_visible _ who _ field visible).trans rightStore)
    leftCandidate rightCandidate

omit [Fintype Player] in
/-- A field that is not visible to `who` carries no owner pair. -/
theorem ownerPairs_of_not_visible {who : Player} {first second : PlayerView (graph setup)}
    {field : (graph setup).Field} (hidden : ¬ (graph setup).fieldVisibleTo who field) :
    (ownerPairs who first second).pair field = none := by
  change ownerValuePair who first second field = none
  have notPrivate : ¬ PrivateTo who field := fun privateTo => hidden privateTo.1
  unfold ownerValuePair
  simp [notPrivate]

omit [Fintype Player] in
/-- A handle of another player carries no owner pair. -/
theorem ownerHandlePairs_of_ne {who : Player} {first second : PlayerView (graph setup)}
    {handle : Handle (graph setup)} (different : handle.1 ≠ who) :
    ownerHandlePairs who first second handle = none := by
  unfold ownerHandlePairs
  simp [different]

omit [Fintype Player] in
/-- A binding field of another player is not visible to `who`. -/
theorem not_visible_of_binding {who owner : Player} {field : (graph setup).Field}
    {payload : L.Ty} (layoutEq : (graph setup).layout field = .binding owner payload)
    (different : owner ≠ who) : ¬ (graph setup).fieldVisibleTo who field := by
  unfold EventGraph.fieldVisibleTo
  rw [layoutEq]
  exact different

omit [Fintype Player] in
/-- A field both views store alike carries no owner pair. -/
theorem ownerPairs_of_store_eq {who : Player} {first second : PlayerView (graph setup)}
    {field : (graph setup).Field}
    (same : first.observation.store field = second.observation.store field) :
    (ownerPairs who first second).pair field = none := by
  change ownerValuePair who first second field = none
  unfold ownerValuePair
  split_ifs
  · rw [same]
    cases second.observation.store field with
    | none => rfl
    | some value => simp
  · rfl

omit [Fintype Player] in
/-- A slot both views hold alike carries no owner pair. -/
theorem ownerHandlePairs_of_candidates_eq {who : Player} {first second : PlayerView (graph setup)}
    {slot : CandidateSlot (graph setup)} (same : first.candidates slot = second.candidates slot) :
    ownerHandlePairs who first second (who, slot) = none := by
  unfold ownerHandlePairs
  simp only [↓reduceIte]
  rw [same]
  cases second.candidates slot with
  | openable raw => simp
  | fresh | unopenable => rfl

omit [Fintype Player] in
/-- At a reveal that is the owner's turn, the delivered value is the owner's
stored binding. -/
theorem deliveredValue_of_turn {who : Player} {view : (application setup leaks).PlayerView}
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (resolveView : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq) :
    deliveredValue setup leaks who view =
      some ⟨.binding owner payload, binding.get? view.application.observation.store⟩ := by
  unfold deliveredValue
  rw [turn]
  simp only [resolveView]

end Guard

section Main

/-- **The swap guard of the owner swap at every history of the first site.**
Take two information sites of `who` with the same late-delivery key, at neither
of which `who` owes a failure at the decoded point of any history (the negation
of `Vegas.OwingAgent` at the site's agent), and the owner swap between their
views. When the setup prior is closed under the swap of the inputs of the
first site's histories, the swap guard holds at every history of the first site. -/
theorem ownerSwap_guard {who : Player}
    {site₁ site₂ : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
    {past₁ past₂ : List (application setup leaks).PlayerEntry}
    {view₁ view₂ : (application setup leaks).PlayerView}
    (firstSite : site₁.1 = some (past₁, view₁)) (secondSite : site₂.1 = some (past₂, view₂))
    (sameKey : lateKey setup leaks who site₁.1 = lateKey setup leaks who site₂.1)
    (firstDebtFree : ∀ history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who site₁.1, ∀ point,
      nativeDecodedState setup leaks history.1.state = some point →
        ¬ ProtocolState.OwesFailure who setup.program point)
    (secondDebtFree : ∀ history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who site₂.1, ∀ point,
      nativeDecodedState setup leaks history.1.state = some point →
        ¬ ProtocolState.OwesFailure who setup.program point)
    (priorClosed : ∀ initial ∈ setup.initialLaw.support,
      (∃ history : (onePacketInformation setup leaks bounds horizon
          scheduler).InformationHistory who site₁.1, ∃ control : (application setup leaks).Control,
        history.1.state = some control ∧
          control.execution.application.config.inputs = setup.eventInputs initial) →
      ∃ other ∈ setup.initialLaw.support, setup.eventInputs other =
        (ownerSwap who view₁.application view₂.application).inputs (setup.eventInputs initial))
    (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    (member : (onePacketInformation setup leaks bounds horizon scheduler).infoOf who
      history.trace = site₁.1) :
    SwapGuardState setup (ownerSwap who view₁.application view₂.application)
      (swapAllowed (ownerSwap who view₁.application view₂.application)) history.state := by
  -- The two histories and their views.
  obtain ⟨state₁, trace₁⟩ := history
  have firstMember := member
  rw [onePacket_infoOf, firstSite] at member
  cases state₁ with
  | none => cases member
  | some control₁ =>
  obtain ⟨⟨history₂, secondMember⟩, -⟩ := site₂.2
  have secondInfo := secondMember
  rw [onePacket_infoOf, secondSite] at secondInfo
  cases state₂Eq : history₂.state with
  | none => rw [state₂Eq] at secondInfo; cases secondInfo
  | some control₂ =>
  have trace₂ : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control₂) :=
    state₂Eq ▸ history₂.trace
  rw [state₂Eq] at secondInfo
  simp only [ReactiveApplication.observe] at member secondInfo
  split at member
  · split at secondInfo
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member).symm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj secondInfo).symm
      have firstDebt : ∀ point, nativeDecodedState setup leaks (some control₁) = some point →
          ¬ ProtocolState.OwesFailure who setup.program point := fun point decoded =>
        firstDebtFree ⟨⟨some control₁, trace₁⟩, firstMember⟩ point decoded
      have secondDebt : ∀ point, nativeDecodedState setup leaks (some control₂) = some point →
          ¬ ProtocolState.OwesFailure who setup.program point := fun point decoded =>
        secondDebtFree ⟨history₂, secondMember⟩ point (by rw [state₂Eq]; exact decoded)
      rw [firstSite, secondSite] at sameKey
      simp only [lateKey, Option.some.injEq, LateKey.mk.injEq] at sameKey
      obtain ⟨-, currentEq, recalledEq, deliveredEq⟩ := sameKey
      simp only [operationalView, Prod.mk.injEq] at currentEq
      have publicEq : control₁.execution.application.publicView =
          control₂.execution.application.publicView := currentEq.1
      have acceptedEq : control₁.execution.application.accepted =
          control₂.execution.application.accepted := congrArg PublicView.accepted publicEq
      have valid₁ := bindingInvariant_of_trace trace₁
      have firstRaw := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
        horizon scheduler trace₁
      have secondRaw := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace
        (initialLaw setup) horizon scheduler trace₂
      change SwapGuard setup (ownerSwap who (control₁.execution.application.playerView who)
        (control₂.execution.application.playerView who))
        (swapAllowed (ownerSwap who (control₁.execution.application.playerView who)
          (control₂.execution.application.playerView who))) control₁.execution
      refine ⟨?_, ?_, ?_, ?_, HiddenSwap.expired_ofPairs _ _ _⟩
      · -- The inputs: initial handles are compatible, and the prior is closed.
        obtain ⟨initial, initialMember, inputsEq, -⟩ := initialSlots_of_trace trace₁ control₁ rfl
        have drawnMember : ∀ draw ∈ setup.initialLaw.support,
            EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs draw) ∈
              (initialLaw setup).support := fun draw drawMember => by
          rw [initialLaw, serviceInitialLaw, PMF.support_map]
          exact ⟨draw, drawMember, rfl⟩
        have compatible : (ownerSwap who (control₁.execution.application.playerView who)
            (control₂.execution.application.playerView who)).InitialHandlesCompatible := by
          unfold ownerSwap
          apply HiddenSwap.initialHandlesCompatible_ofPairs
          intro input owner payload layoutEq
          by_cases owned : owner = who
          · subst owned
            exact ownerPairs_of_accepted trace₁ trace₂ firstDebt secondDebt acceptedEq
              (field := .inl input) layoutEq (accepted_initial_of_trace trace₁ layoutEq)
          · exact Or.inl ⟨ownerPairs_of_not_visible
              (not_visible_of_binding (field := .inl input) layoutEq owned),
              ownerHandlePairs_of_ne owned⟩
        refine ⟨_, drawnMember initial initialMember, inputsEq.symm, ?_⟩
        rw [State.swap_initial _ compatible]
        obtain ⟨other, otherMember, otherEq⟩ := priorClosed initial initialMember
          ⟨⟨⟨some control₁, trace₁⟩, firstMember⟩, control₁, rfl, inputsEq⟩
        have target := drawnMember other otherMember
        rw [otherEq] at target
        exact target
      · -- Accepted commitments: the pairs at the event and at the handle match.
        intro event candidate accepted
        obtain ⟨payload, layoutEq⟩ := valid₁.accepted_typed _ candidate accepted
        obtain ⟨owner, slot⟩ := candidate
        by_cases owned : owner = who
        · subst owned
          rcases ownerPairs_of_accepted trace₁ trace₂ firstDebt secondDebt acceptedEq layoutEq
              accepted with ⟨eventNone, handleNone⟩ | ⟨left, right, eventPair, handlePair⟩
          · exact HiddenSwap.bindCompatible_ofPairs_none _ _ eventNone handleNone
          · exact HiddenSwap.bindCompatible_ofPairs _ _ layoutEq left right eventPair handlePair
        · exact HiddenSwap.bindCompatible_ofPairs_none _ _
            (ownerPairs_of_not_visible (not_visible_of_binding layoutEq owned))
            (ownerHandlePairs_of_ne owned)
      · -- Ready and completed reveals read bindings both views store alike.
        intro event active
        unfold RevealFixed
        cases resolveView : nodeView (graph setup) event with
        | bind | sample => trivial
        | resolve owner payload binding checks outputEq codeEq =>
            have bindingLayout : (graph setup).layout binding.field = .binding owner payload :=
              binding.layout_eq
            by_cases owned : owner = who
            · subst owned
              have getEq : binding.get? control₁.execution.application.config.store =
                  binding.get? control₂.execution.application.config.store := by
                have visible := (privateTo_of_binding bindingLayout).1
                have masked : ∀ store : EventGraph.Store (graph setup).layout,
                    binding.get? ((graph setup).playerStore owner store) = binding.get? store :=
                  fun store => EventGraph.FieldRef.get?_congr binding _ _
                    (EventGraph.playerStore_of_visible _ owner store _ visible)
                rcases active with ready | completed
                · -- A ready reveal of the owner is its turn: both keys deliver its binding.
                  have actor : (graph setup).actor? event = some owner :=
                    nodeView_resolve_actor outputEq codeEq
                  have firstTurn := ownTurn?_of_ready setup control₁.execution.application ready
                    actor
                  have secondTurn : control₂.execution.application.publicView.ownTurn? owner =
                      some event := publicEq ▸ firstTurn
                  rw [deliveredValue_of_turn (view := control₁.execution.observe
                      (application setup leaks) owner) firstTurn resolveView,
                    deliveredValue_of_turn (view := control₂.execution.observe
                      (application setup leaks) owner) secondTurn resolveView] at deliveredEq
                  have viewGet := eq_of_heq (Sigma.mk.inj (Option.some.inj deliveredEq)).2
                  exact (masked _).symm.trans (viewGet.trans (masked _))
                · -- A completed reveal published its binding: the publication is public.
                  have publicField : (graph setup).fieldPublic (.inr event) := by
                    unfold EventGraph.fieldPublic
                    change ((graph setup).outputLayout event).IsPublic
                    rw [outputEq]
                    trivial
                  have publicStore := congrArg (fun view : PublicView (graph setup) =>
                    view.observation.store (.inr event)) publicEq
                  change (if (graph setup).fieldPublic (.inr event) then
                      control₁.execution.application.config.store (.inr event) else none) =
                    (if (graph setup).fieldPublic (.inr event) then
                      control₂.execution.application.config.store (.inr event) else none)
                    at publicStore
                  simp only [publicField, ↓reduceIte] at publicStore
                  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
                    ((control₁.execution.application.config.output_available event).mpr completed)
                  change control₁.execution.application.config.store (.inr event) = some value
                    at stored
                  have secondStored := publicStore ▸ stored
                  have secondCompleted :
                      event ∈ control₂.execution.application.config.cut.completed := by
                    apply (control₂.execution.application.config.output_available event).mp
                    change (control₂.execution.application.config.store (.inr event)).isSome
                    rw [secondStored]
                    rfl
                  let publication : EventGraph.FieldRef (graph setup).layout
                      (.publication payload) := ⟨.inr event, outputEq⟩
                  have firstRead := get?_of_store publication stored
                  have secondRead := get?_of_store publication secondStored
                  have noFailure : ∀ {control : (application setup leaks).Control},
                      (∀ point, nativeDecodedState setup leaks (some control) = some point →
                        ¬ ProtocolState.OwesFailure owner setup.program point) →
                      ∀ {rank} (_ : SourceResidual setup (failureProfile setup.program) rank
                        control.execution.application.config),
                      ¬ DecodedHolds (ProtocolState.RevealFailed owner setup.program) rank
                        control.execution.application.config :=
                    fun debt _ residual failed => debt _ (decodedPoint_eq residual)
                      (Or.inl (ProtocolState.RevealFailed.indebted _ _
                        (failed _ residual.decode)))
                  obtain ⟨_, ⟨firstResidual⟩, firstRecord⟩ :=
                    revealRecord_history (failureProfile setup.program) firstRaw
                  obtain ⟨_, ⟨secondResidual⟩, secondRecord⟩ :=
                    revealRecord_history (failureProfile setup.program) secondRaw
                  rcases firstRecord event completed owner payload binding checks outputEq codeEq
                      resolveView _ firstRead with ⟨first, firstResult, firstBound⟩ | failed
                  · rcases secondRecord event secondCompleted owner payload binding checks
                        outputEq codeEq resolveView _ secondRead with
                      ⟨second, secondResult, secondBound⟩ | failed
                    · rw [firstBound, secondBound, firstResult.symm.trans secondResult]
                    · exact (noFailure secondDebt secondResidual failed).elim
                  · exact (noFailure firstDebt firstResidual failed).elim
              have storeEq : control₁.execution.application.config.store binding.field =
                  control₂.execution.application.config.store binding.field := by
                unfold EventGraph.FieldRef.get? at getEq
                exact (cast_inj _).mp getEq
              have visible := (privateTo_of_binding bindingLayout).1
              refine ⟨?_, fun candidate accepted => ?_⟩
              · change EventGraph.pairSwap ((ownerPairs owner _ _).pair binding.field) = id
                rw [ownerPairs_of_store_eq ((EventGraph.playerStore_of_visible _ owner _ _
                  visible).trans (storeEq.trans (EventGraph.playerStore_of_visible _ owner _ _
                    visible).symm))]
                rfl
              · obtain ⟨other, candidateLayout⟩ := valid₁.accepted_typed _ candidate accepted
                have candidateOwner : candidate.1 = owner :=
                  (EventGraph.EventField.binding.inj (candidateLayout.symm.trans bindingLayout)).1
                obtain ⟨candidateOwner', slot⟩ := candidate
                change candidateOwner' = owner at candidateOwner
                subst candidateOwner
                obtain ⟨left, leftStore, leftCandidate⟩ :=
                  ownBinding_candidate trace₁ firstDebt accepted rfl
                obtain ⟨right, rightStore, rightCandidate⟩ :=
                  ownBinding_candidate trace₂ secondDebt (acceptedEq ▸ accepted) rfl
                rw [storeEq, rightStore] at leftStore
                cases Option.some.inj leftStore
                change EventGraph.pairSwap (ownerHandlePairs candidateOwner' _ _
                  (candidateOwner', slot)) = id
                rw [ownerHandlePairs_of_candidates_eq (leftCandidate.trans rightCandidate.symm)]
                rfl
            · refine ⟨?_, fun candidate accepted => ?_⟩
              · change EventGraph.pairSwap ((ownerPairs who _ _).pair binding.field) = id
                rw [ownerPairs_of_not_visible (not_visible_of_binding bindingLayout owned)]
                rfl
              · obtain ⟨other, candidateLayout⟩ := valid₁.accepted_typed _ candidate accepted
                have candidateOwner : candidate.1 = owner :=
                  (EventGraph.EventField.binding.inj (candidateLayout.symm.trans bindingLayout)).1
                change EventGraph.pairSwap (ownerHandlePairs who _ _ candidate) = id
                rw [ownerHandlePairs_of_ne (candidateOwner ▸ owned)]
                rfl
      · -- Owned requests in recall certify values both views hold alike.
        intro player recalled recalledMember submission sent
        cases owned : submission.evidence with
        | none | forward => trivial
        | owned fact =>
            change EventGraph.pairSwap (ownerHandlePairs who _ _ fact.handle) fact.raw = fact.raw
            have own := ownedRequestsOwn_history trace₁ player recalled recalledMember submission
              sent fact owned
            by_cases same : player = who
            · rw [same] at recalledMember own
              obtain ⟨message, emitted, evidence, -⟩ := ownedRequestsEmitted_history bounds trace₁
                who recalled recalledMember submission sent
              have carried := evidence fact owned
              have decoded : fact ∈ message.payload.evidence.toList := by
                rw [carried]
                exact List.mem_singleton_self fact
              have firstInput := output_mem_inputs_of_trace bounds trace₁ who message
                (List.mem_filterMap.mpr ⟨recalled, recalledMember, emitted⟩)
              have firstSound : ((runtime setup).packetEvidence leaks).Sound control₁.execution :=
                ((runtime setup).packetEvidence leaks).history_sound (initialLaw setup) horizon
                  scheduler firstRaw
              have firstHolds : fact.Holds control₁.execution.application :=
                firstSound.inputs message firstInput fact decoded
              have mapped := recalledEq ▸ List.mem_map_of_mem
                (f := fun entry : (application setup leaks).PlayerEntry =>
                  (operationalView setup leaks entry.beforeView, entry.emitted)) recalledMember
              obtain ⟨entry, entryMember, entryEq⟩ := List.mem_map.mp mapped
              have entryEmitted : entry.emitted = some message :=
                (congrArg Prod.snd entryEq).trans emitted
              have secondInput := output_mem_inputs_of_trace bounds trace₂ who message
                (List.mem_filterMap.mpr ⟨entry, entryMember, entryEmitted⟩)
              have secondSound : ((runtime setup).packetEvidence leaks).Sound
                  control₂.execution :=
                ((runtime setup).packetEvidence leaks).history_sound (initialLaw setup) horizon
                  scheduler secondRaw
              have secondHolds : fact.Holds control₂.execution.application :=
                secondSound.inputs message secondInput fact decoded
              have handleEq : fact.handle = (who, fact.handle.2) := Prod.ext own rfl
              unfold OpeningFact.Holds at firstHolds secondHolds
              rw [handleEq] at firstHolds secondHolds ⊢
              rw [ownerHandlePairs_of_candidates_eq (firstHolds.trans secondHolds.symm)]
              rfl
            · rw [ownerHandlePairs_of_ne (fun ownerEq => same (own.symm.trans ownerEq))]
              rfl
    · cases secondInfo
  · cases member

end Main

end Vegas
