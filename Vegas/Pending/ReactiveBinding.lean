/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicy
import Vegas.Pending.ReactiveSafety
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactivePolicyInvariant
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveRecallInvariant

/-! # Compiled bindings across arbitrary intervening interaction

A compiled response fixes its selected binding before the envelope becomes
observable. Arbitrary later responses, passive leaks, inclusions and application
commands preserve that meaning. If the original packet is eventually included
at an admissible opportunity, it performs exactly that graph action.

The theorem does not coalesce submission with inclusion. Nor does it guarantee
which packet is selected, or that an admissible opportunity remains available.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every operation preserves a previously fixed candidate lookup. -/
theorem fixedCandidateLookupInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (original : State graph) (candidate : Handle graph)
    (fixed : original.candidates.lookup candidate ≠ .fresh) :
    (runtime.reactiveApplication leaks).Invariant (fun state =>
      state.candidates.lookup candidate = original.candidates.lookup candidate) := by
  let app := runtime.reactiveApplication leaks
  constructor
  · intro state actor material same
    exact (runtime.reactive_respond_candidate_fixed leaks (.initial app state) actor
      ⟨some material⟩ candidate (by
        change state.candidates.lookup candidate ≠ .fresh
        rwa [same])).trans same
  · intro state message target same accepted
    exact (handle_lookup_of_not_fresh runtime state target
      ⟨message.id, message.payload.call⟩ candidate (by rwa [same])
      (reactiveHandle_call accepted)).trans same
  · intro state command target same supported
    rw [(environmentStep_tables runtime state target command supported).2]
    exact same

/-- The selected meaning of every genuinely fresh recorded binding is retained
 throughout arbitrary legal raw interaction. -/
def RecordedBindingMeaning (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ who entry, entry ∈ execution.recall who → ∀ event payload result serial,
    entry.action = runtime.reactiveBinding leaks who event payload result serial →
    entry.beforeView.application.candidates (.prepared serial) = .fresh →
    execution.application.candidates.lookup (who, .prepared serial) ≠ .fresh ∧
      execution.application.bindingResult (who, .prepared serial) payload = result

/-- Immutable prepared handles transport the actual recorded binding result. -/
theorem recordedBindingMeaningInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (runtime.RecordedBindingMeaning leaks) := by
  let app := runtime.reactiveApplication leaks
  constructor
  · intro execution who action valid observer entry retained event payload result serial
      declared fresh
    by_cases same : observer = who
    · subst observer
      have origin : entry ∈ execution.recall who ∨
          (entry.beforeView = execution.observe app who ∧ entry.action = action) := by
        rcases action with ⟨transmission⟩
        cases transmission <;>
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
            List.mem_singleton] at retained
        all_goals rcases retained with old | rfl
        all_goals first | exact Or.inl old | exact Or.inr ⟨rfl, rfl⟩
      rcases origin with old | ⟨viewed, chosen⟩
      · obtain ⟨fixed, meaning⟩ := valid who entry old event payload result serial declared fresh
        have stable := runtime.reactive_respond_candidate_fixed leaks execution who action
          (who, .prepared serial) fixed
        exact ⟨by rwa [stable], by simpa only [State.bindingResult, stable] using meaning⟩
      · have actual : action = runtime.reactiveBinding leaks who event payload result serial :=
          chosen.symm.trans declared
        have freshState : execution.application.candidates.lookup (who, .prepared serial) =
            .fresh := by simpa only [viewed, ReactiveApplication.Execution.observe,
              reactiveApplication, State.playerView, app] using fresh
        rw [actual]
        refine ⟨?_, runtime.reactiveBinding_result leaks who event payload result serial
          execution freshState⟩
        change (submitStep _ who (.commitment event (who, .prepared serial))).candidates.lookup
          (who, .prepared serial) ≠ .fresh
        exact submitStep_commitment_fixed _ who event (.prepared serial)
    · have old := app.respond_recall_other execution who observer same action
      obtain ⟨fixed, meaning⟩ := valid observer entry (old ▸ retained) event payload result serial
        declared fresh
      have stable := runtime.reactive_respond_candidate_fixed leaks execution who action
        (observer, .prepared serial) fixed
      exact ⟨by rwa [stable], by simpa only [State.bindingResult, stable] using meaning⟩
  · intro execution next command valid _ reached observer entry retained event payload result serial
      declared fresh
    rw [app.environmentStep_recall execution next command reached] at retained
    obtain ⟨fixed, meaning⟩ := valid observer entry retained event payload result serial
      declared fresh
    have stable := (runtime.fixedCandidateLookupInvariant leaks execution.application
      (observer, .prepared serial) fixed).environmentStep execution next command rfl reached
    exact ⟨by rwa [stable], by simpa only [State.bindingResult, stable] using meaning⟩

/-- Every initialized legal trace preserves the exact declared binding meaning;
 no policy consistency or supported continuation is required. -/
theorem recordedBindingMeaning_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) : runtime.RecordedBindingMeaning leaks control.execution := by
  exact (runtime.recordedBindingMeaningInvariant leaks scheduler).history initial horizon
    (fun _ _ who entry member => False.elim (List.not_mem_nil member)) trace

/-- Authentic acceptance realizes the original sampled binding of a retained
 fresh declaration along the actual raw trace, without a policy-run suffix. -/
theorem reactiveDecision_binding_accepted_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (action : graph.Action event) (serial : Nat)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (retained : entry ∈ control.execution.recall owner)
    (declared : entry.action = runtime.reactiveBinding leaks owner event payload
      (cast (congrArg EventField.Action outputEq) action) serial)
    (fresh : entry.beforeView.application.candidates (.prepared serial) = .fresh)
    (message : Message Player (WitnessedPacket graph))
    (packet : message.payload.call = .commitment event (owner, .prepared serial))
    (sender : message.id.1 = owner)
    (after : State graph)
    (accepted : (runtime.reactiveApplication leaks).handle control.execution.application message =
      some after) :
    ∃ ready : control.execution.application.config.cut.Ready event,
      PMF.pure after.config = control.execution.application.config.step event ready action := by
  have meaning := ((runtime.recordedBindingMeaning_history leaks initial horizon scheduler
    control trace) owner entry retained event payload
      (cast (congrArg EventField.Action outputEq) action) serial declared fresh).2
  let nonce := message.id.2
  have identity : message.id = (owner, nonce) := by
    apply Prod.ext
    · exact sender
    · rfl
  have physical : handle runtime control.execution.application
      ⟨(owner, nonce), .commitment event (owner, .prepared serial)⟩ = some after := by
    simpa only [identity, packet] using reactiveHandle_call accepted
  have originalCall := physical
  simp only [handle] at physical
  split at physical
  · rename_i ready
    split at physical
    · rename_i timely
      simp only [node, Message.sender] at physical
      simp only [dite_eq_ite, Option.ite_none_right_eq_some, Option.some.injEq,
        true_and] at physical
      obtain ⟨vacant, unused, _⟩ := physical
      have exactHandle := runtime.handle_commitment_eq control.execution.application
        (owner, nonce) event (owner, .prepared serial)
        owner payload outputEq codeEq node ready timely rfl rfl vacant unused
      have equal := Option.some.inj (originalCall.symm.trans exactHandle)
      refine ⟨ready, ?_⟩
      rw [equal]
      change PMF.pure (control.execution.application.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm)
          (control.execution.application.bindingResult (owner, .prepared serial) payload))
        (cast (congrArg EventField.Value outputEq.symm)
          (control.execution.application.bindingResult (owner, .prepared serial) payload))) = _
      rw [meaning]
      symm
      have law := control.execution.application.config.step_eq_map_of_code event ready
        outputEq _ codeEq
        (cast (congrArg EventField.Action outputEq) action)
        (PMF.pure (cast (congrArg EventField.Action outputEq) action)) rfl
      simpa only [PMF.pure_map, cast_cast, cast_eq] using law
    · simp at physical
  · simp at physical



theorem reactiveDecision_binding_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (action : graph.Action event) (view : PlayerView graph) (serial : Nat)
    (allocated : reactiveFreshSlot view = some serial) :
    runtime.reactiveDecision leaks who event action view =
      runtime.reactiveBinding leaks who event payload
        (cast (congrArg EventField.Action outputEq) action) serial := by
  simp only [reactiveDecision, node, allocated, Option.map_some, reactiveBinding]
  rfl

/-- This includes continuations in which the owner submits competing candidates,
other players react to partial leaks, and earlier inclusions are rejected. -/
theorem reactiveBinding_continuation_result (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy) (rounds : Nat)
    (reached : next ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players rounds
      (execution.respond (runtime.reactiveApplication leaks) who
        (runtime.reactiveBinding leaks who event payload result serial))).support) :
    next.application.bindingResult (who, .prepared serial) payload = result := by
  let app := runtime.reactiveApplication leaks
  let submitted := execution.respond app who
    (runtime.reactiveBinding leaks who event payload result serial)
  let candidate : Handle graph := (who, .prepared serial)
  have fixed : submitted.application.candidates.lookup candidate ≠ .fresh := by
    change (submitStep _ who (.commitment event candidate)).candidates.lookup candidate ≠ .fresh
    exact submitStep_commitment_fixed _ who event (.prepared serial)
  have invariant := runtime.fixedCandidateLookupInvariant leaks
    submitted.application candidate fixed
  have stable := (ReactiveApplication.Invariant.policyInvariant app invariant players).runRounds
    scheduler rounds submitted next rfl reached
  change next.application.candidates.lookup candidate =
    submitted.application.candidates.lookup candidate at stable
  have meaning := runtime.reactiveBinding_result leaks who event payload result serial
    execution fresh
  change submitted.application.bindingResult candidate payload = result at meaning
  rw [State.bindingResult, stable]
  exact meaning

/-- Conditional realization at the actual inclusion state. Readiness, the
deadline and handle availability are checked there, after the intervening play.
The conclusion retains the exact semantic action and its completion history. -/
theorem reactiveBinding_continuation_include (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (result : PublicationResult (L.Val payload)) (serial nonce : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (fresh : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy) (rounds : Nat)
    (reached : next ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players rounds
      (execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveBinding leaks owner event payload result serial))).support)
    (pending : next.network.lookup (owner, nonce) =
      some ⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none, some ⟨event⟩⟩⟩)
    (ready : next.application.config.cut.Ready event)
    (timely : next.application.WithinDeadline runtime event)
    (vacant : next.application.accepted (.inr event) = none)
    (unused : next.application.HandleUnused (owner, .prepared serial)) :
    (next.includePending (runtime.reactiveApplication leaks) (owner, nonce)).application.config =
      next.application.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) result)
        (cast (congrArg EventField.Value outputEq.symm) result) ∧
    (next.includePending (runtime.reactiveApplication leaks) (owner, nonce)).receipts =
      next.receipts ++ [((owner, nonce), true)] := by
  have meaning := runtime.reactiveBinding_continuation_result leaks owner event payload result
    serial execution next fresh scheduler players rounds reached
  have accepted := runtime.handle_commitment_eq next.application (owner, nonce) event
    (owner, .prepared serial) owner payload outputEq codeEq node ready timely rfl rfl vacant unused
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending, pending]
  change _ ∧ _
  dsimp only [reactiveApplication]
  simp only [WitnessedPacket.tokenValid_commitment, ite_true]
  rw [accepted]
  simp only [Option.getD_some, State.complete, meaning, Option.isSome_some]
  exact ⟨trivial, trivial⟩

/-- The actual compiler, rather than a separately chosen binding submission,
realizes its sampled graph action at a later admissible inclusion. No restriction
is imposed on intermediate policies or on the passive observation kernel. -/
theorem reactiveDecision_binding_continuation_step (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (action : graph.Action event) (serial : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (allocated : reactiveFreshSlot
      ((runtime.reactiveApplication leaks).observePlayer execution.application owner) = some serial)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy) (rounds : Nat)
    (reached : next ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players rounds
      (execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveDecision leaks owner event action
          ((runtime.reactiveApplication leaks).observePlayer
            execution.application owner)))).support)
    (pending : next.network.lookup (owner, execution.network.nextSerial owner) =
      some ⟨(owner, execution.network.nextSerial owner),
        ⟨.commitment event (owner, .prepared serial), none, some ⟨event⟩⟩⟩)
    (ready : next.application.config.cut.Ready event)
    (timely : next.application.WithinDeadline runtime event)
    (vacant : next.application.accepted (.inr event) = none)
    (unused : next.application.HandleUnused (owner, .prepared serial)) :
    PMF.pure ((next.includePending (runtime.reactiveApplication leaks)
      (owner, execution.network.nextSerial owner)).application.config) =
        next.application.config.step event ready action ∧
    (next.includePending (runtime.reactiveApplication leaks)
      (owner, execution.network.nextSerial owner)).receipts =
        next.receipts ++ [((owner, execution.network.nextSerial owner), true)] := by
  have fresh := reactiveFreshSlot_spec
    ((runtime.reactiveApplication leaks).observePlayer execution.application owner) serial allocated
  rw [runtime.reactiveDecision_binding_eq leaks owner owner event payload outputEq codeEq
    node action _ serial allocated] at reached
  obtain ⟨included, receipt⟩ := runtime.reactiveBinding_continuation_include leaks owner event
    payload outputEq codeEq node (cast (congrArg EventField.Action outputEq) action)
    serial (execution.network.nextSerial owner) execution next fresh scheduler players rounds
    reached pending ready timely vacant unused
  refine ⟨?_, receipt⟩
  rw [included]
  symm
  have law := next.application.config.step_eq_map_of_code event ready outputEq _ codeEq
    (cast (congrArg EventField.Action outputEq) action)
    (PMF.pure (cast (congrArg EventField.Action outputEq) action)) rfl
  simpa only [PMF.pure_map, cast_cast, cast_eq] using law

end Vegas.EventGraphRuntime
