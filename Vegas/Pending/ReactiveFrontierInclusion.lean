/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFrontierRecall
import Vegas.Pending.ReactiveOriginalConfig
import Vegas.Pending.ReactiveOriginalInclusionStability
import Vegas.Pending.ReactiveAcceptedIntentionRecall
import Vegas.Pending.ReactiveBinding
import Vegas.Pending.ReactiveResponseSampling
import Vegas.Pending.ReactiveSampledResolutionSettlement
import Vegas.EventGraph.ConfigRestriction
import Interaction.ReactiveProvenance

/-! # Actual protected inclusion preserves retained sampled frontiers -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A genuinely accepted resolution envelope restores its supported recorded
intention in the newly appended original history. Old completed actions remain
unchanged by actual message-identity and recall invariants. -/
theorem originalConfig_include_resolution_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (memories : Player → List (Option graph.Completion))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent
      (control.execution.recall who))
    (quiet : ∀ entry ∈ control.execution.recall who,
      entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ entry ∈ control.execution.recall who, ∀ material,
      entry.action.transmission = some material → ∃ message,
        entry.emitted = some message ∧ message.payload.call = material.call.packet)
    (supported : memories who ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (control.execution.recall who)).support)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (remembered completion : graph.Completion)
    (retained : (entry, some remembered) ∈ (control.execution.recall who).zip (memories who))
    (message : Message Player (WitnessedPacket graph))
    (emitted : entry.emitted = some message)
    (named : message.payload.call.event? graph = some completion.event)
    (sameEvent : remembered.event = completion.event)
    (resolution : (match nodeView graph completion.event with
      | .resolve .. => true | .sample .. | .bind .. => false) = true)
    (after : State graph)
    (found : control.execution.network.lookup message.id = some message)
    (accepted : (runtime.reactiveApplication leaks).handle control.execution.application message =
      some after)
    (history : after.config.history =
      control.execution.application.config.history ++ [completion]) :
    (runtime.originalConfig leaks
      (control.execution.includePending (runtime.reactiveApplication leaks) message.id)
      memories).history =
      (runtime.originalConfig leaks control.execution memories).history ++ [remembered] := by
  let next := control.execution.includePending (runtime.reactiveApplication leaks) message.id
  have includedRecall : next.recall = control.execution.recall := by
    simp only [next, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, accepted]
  have includedConfig : next.application.config = after.config := by
    simp only [next, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, accepted, Option.getD_some]
  have receipt : (message.id, true) ∈ next.receipts := by
    simp [next, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, accepted]
  have matching := runtime.prescribedReactivePosterior_decision_alignment leaks who policy
    consistent (memories who) supported entry remembered retained
  have distinct := runtime.prescribedReactivePosterior_events_nodup leaks who policy consistent
    quiet sent (memories who) supported
  have restored : runtime.reactiveOriginal leaks who (next.recall who) (memories who)
      next.receipts completion = remembered := by
    apply runtime.reactiveOriginal_accepted_of_unique_memory leaks who (next.recall who)
      (memories who) next.receipts entry remembered completion
    · rwa [includedRecall]
    · exact emitted
    · exact named
    · exact receipt
    · exact matching
    · exact sameEvent
    · intro other member saved equal event
      subst other
      exact completion_eq_of_intention_events_nodup (memories who) distinct saved remembered
        member (List.of_mem_zip retained).2 (event.trans sameEvent.symm)
    · exact resolution
  have actor := runtime.prescribedReactivePosterior_owned leaks who policy consistent
    (memories who) supported remembered (List.of_mem_zip retained).2
  have newOriginal : runtime.originalCompletion leaks next memories completion = remembered := by
    simp only [originalCompletion, ← sameEvent, actor]
    exact restored
  change (next.application.config.history.map (runtime.originalCompletion leaks next memories)) = _
  rw [includedConfig, history, List.map_append, List.map_singleton, newOriginal]
  apply congrArg (fun old => old ++ [remembered])
  apply List.map_congr_left
  intro old member
  have completed := (control.execution.application.config.history_exact old.event).mp
    (List.mem_map.mpr ⟨old, member, rfl⟩)
  unfold originalCompletion
  split
  · rfl
  · exact runtime.reactiveOriginal_include_completed_history leaks inputs horizon scheduler
      control trace _ (memories _) message.id old completed

/-- Inclusion of an actually emitted prescribed opening consumes the pending
original intention while preserving the reachable sampled frontier. -/
theorem ReactiveFrontier.include_resolution (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.BarrierOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks control.execution memories frontier)
    (profile : graph.BehavioralProfile)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (control.execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (control.execution.recall owner)).support)
    (who : Player)
    (quiet : ∀ entry ∈ control.execution.recall who,
      entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ entry ∈ control.execution.recall who, ∀ material,
      entry.action.transmission = some material → ∃ message,
        entry.emitted = some message ∧ message.payload.call = material.call.packet)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry) (remembered : graph.Completion)
    (retained : (entry, some remembered) ∈ (control.execution.recall who).zip (memories who))
    (message : Message Player (WitnessedPacket graph)) (emitted : entry.emitted = some message)
    (material : WitnessedSubmission graph) (transmitted : entry.action.transmission = some material)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout remembered.event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes remembered.event) = .resolve owner payload binding checks)
    (node : nodeView graph remembered.event =
      .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle graph) (raw : Raw L)
    (packet : message.payload.call = .opening remembered.event candidate raw)
    (after : State graph)
    (found : control.execution.network.lookup message.id = some message)
    (accepted : (runtime.reactiveApplication leaks).handle control.execution.application message =
      some after) :
    runtime.ReactiveFrontier leaks
      (control.execution.includePending (runtime.reactiveApplication leaks) message.id)
      memories frontier := by
  have matching := runtime.prescribedReactivePosterior_decision_alignment leaks who (profile who)
    (consistent who) (memories who) (supported who) entry remembered retained
  have disclosed := runtime.reactiveDecision_resolution_transmitted_true leaks who owner
    remembered.event payload binding checks outputEq codeEq node remembered.action
    entry.beforeView.application material (matching ▸ transmitted)
  have chosen : remembered.action = cast (congrArg EventField.Action outputEq.symm) true := by
    have restored := congrArg (cast (congrArg EventField.Action outputEq.symm)) disclosed
    simpa using restored
  have handled : handle runtime control.execution.application
      ⟨message.id, .opening remembered.event candidate raw⟩ = some after := by
    simpa only [packet] using reactiveHandle_call accepted
  obtain ⟨ready, effective, physicalStep, _, _, effectiveOwner, effectivePayload,
      effectiveBinding, effectiveChecks, effectiveOutput, _, _, effectiveTrue⟩ :=
    handle_opening_config_step runtime control.execution.application after message.id
      remembered.event candidate raw handled
  have payloadEq : payload = effectivePayload :=
    EventField.publication.inj (outputEq.symm.trans effectiveOutput)
  subst effectivePayload
  have effectiveEq : effective = remembered.action := effectiveTrue.trans chosen.symm
  rw [effectiveEq] at physicalStep
  let next := control.execution.includePending (runtime.reactiveApplication leaks) message.id
  have configEq : next.application.config = after.config := by
    simp only [next, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, accepted, Option.getD_some]
  have originalHistory := runtime.originalConfig_include_resolution_history leaks inputs horizon
    scheduler control trace memories who (profile who) (consistent who) quiet sent (supported who)
    entry remembered remembered retained message emitted
    (by simp [packet, Payload.event?]) rfl (by simp [node]) after found accepted
    (control.execution.application.config.step_history remembered.event ready remembered.action
      after.config physicalStep)
  have actor := runtime.prescribedReactivePosterior_owned leaks who (profile who)
    (consistent who) (memories who) (supported who) remembered (List.of_mem_zip retained).2
  have inputEq : after.config.inputs = control.execution.application.config.inputs := by
    rw [Config.step, PMF.support_map] at physicalStep
    obtain ⟨value, _, produced⟩ := physicalStep
    simpa only [Config.complete] using congrArg Config.inputs produced.symm
  constructor
  · rw [configEq, inputEq]
    exact related.reachable
  · rw [configEq, inputEq]
    exact related.inputs
  · intro event
    rw [configEq, control.execution.application.config.step_cut remembered.event ready
      remembered.action after.config physicalStep, EventOrder.Cut.mem_complete]
    constructor
    · intro completed
      rcases (related.domain event).mp completed with physical | saved
      · exact Or.inl (Or.inr physical)
      · exact Or.inr saved
    · rintro ((same | physical) | saved)
      · exact (related.domain event).mpr (Or.inr
          ⟨who, remembered, (List.of_mem_zip retained).2, same.symm⟩)
      · exact (related.domain event).mpr (Or.inl physical)
      · exact (related.domain event).mpr (Or.inr saved)
  · rw [configEq]
    have recorded : remembered ∈ frontier.history := (List.mem_filter.mp (by
      rw [related.intentions who]
      exact List.mem_filterMap.mpr ⟨some remembered, (List.of_mem_zip retained).2, rfl⟩ :
        remembered ∈ graph.ownCompletions who frontier.history)).1
    exact Config.CompletedOutputAgreement.settle_sampled_owned
      control.execution.application.config frontier after.config related.settled related.inputs.symm
      (by simpa only [related.inputs] using related.reachable) remembered recorded who actor ready
      physicalStep
  · exact related.intentions
  · intro observer
    rw [originalHistory]
    by_cases equal : observer = who
    · subst observer
      have suffix := related.pending_owner_suffix runtime leaks ordered control.execution
        (runtime.entryEventStable_history leaks (inputs.map State.initial) horizon scheduler trace)
        memories frontier profile consistent supported who remembered
        (List.of_mem_zip retained).2 ready
      have ownAppend : graph.ownCompletions who
          ((runtime.originalConfig leaks control.execution memories).history ++ [remembered]) =
          graph.ownCompletions who
            (runtime.originalConfig leaks control.execution memories).history ++
            [remembered] := by simp [ownCompletions, actor]
      rw [ownAppend, ← suffix]
    · have foreign : graph.actor? remembered.event ≠ some observer := by
        simpa only [actor, Option.some.injEq, ne_eq] using Ne.symm equal
      simpa [ownCompletions, foreign] using related.recalled observer

private theorem originalConfig_include_binding_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (memories : Player → List (Option graph.Completion)) (remembered : graph.Completion)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout remembered.event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes remembered.event) = .bind owner payload)
    (node : nodeView graph remembered.event = .bind owner payload outputEq codeEq)
    (message : Message Player (WitnessedPacket graph)) (after : State graph)
    (found : control.execution.network.lookup message.id = some message)
    (accepted : (runtime.reactiveApplication leaks).handle control.execution.application message =
      some after)
    (history : after.config.history =
      control.execution.application.config.history ++ [remembered]) :
    (runtime.originalConfig leaks
      (control.execution.includePending (runtime.reactiveApplication leaks) message.id)
      memories).history =
      (runtime.originalConfig leaks control.execution memories).history ++ [remembered] := by
  let next := control.execution.includePending (runtime.reactiveApplication leaks) message.id
  have includedConfig : next.application.config = after.config := by
    simp only [next, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, accepted, Option.getD_some]
  have newOriginal : runtime.originalCompletion leaks next memories remembered = remembered := by
    unfold originalCompletion
    split
    · rfl
    · simp only [reactiveOriginal, node]
  change next.application.config.history.map (runtime.originalCompletion leaks next memories) = _
  rw [includedConfig, history, List.map_append, List.map_singleton, newOriginal]
  apply congrArg (fun old => old ++ [remembered])
  apply List.map_congr_left
  intro old member
  have completed := (control.execution.application.config.history_exact old.event).mp
    (List.mem_map.mpr ⟨old, member, rfl⟩)
  unfold originalCompletion
  split
  · rfl
  · exact runtime.reactiveOriginal_include_completed_history leaks inputs horizon scheduler
      control trace _ (memories _) message.id old completed

/-- An actual accepted prescribed binding consumes its sampled intention,
including an originally sampled failed binding. -/
theorem ReactiveFrontier.include_binding (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.BarrierOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks control.execution memories frontier)
    (profile : graph.BehavioralProfile)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (control.execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (control.execution.recall owner)).support)
    (who : Player)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry) (remembered : graph.Completion)
    (retained : (entry, some remembered) ∈ (control.execution.recall who).zip (memories who))
    (payload : L.Ty)
    (outputEq : graph.outputLayout remembered.event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes remembered.event) = .bind who payload)
    (node : nodeView graph remembered.event = .bind who payload outputEq codeEq)
    (serial : Nat) (allocated : reactiveFreshSlot entry.beforeView.application = some serial)
    (message : Message Player (WitnessedPacket graph)) (emitted : entry.emitted = some message)
    (packet : message.payload.call = .commitment remembered.event (who, .prepared serial))
    (after : State graph)
    (found : control.execution.network.lookup message.id = some message)
    (accepted : (runtime.reactiveApplication leaks).handle control.execution.application message =
      some after) :
    runtime.ReactiveFrontier leaks
      (control.execution.includePending (runtime.reactiveApplication leaks) message.id)
      memories frontier := by
  have entryMember := (List.of_mem_zip retained).1
  have matching := runtime.prescribedReactivePosterior_decision_alignment leaks who (profile who)
    (consistent who) (memories who) (supported who) entry remembered retained
  have declared := matching.trans (runtime.reactiveDecision_binding_eq leaks who who
    remembered.event payload outputEq codeEq node remembered.action entry.beforeView.application
    serial allocated)
  have recalled := (runtime.reactiveApplication leaks).history_inputRecall
    (inputs.map State.initial) horizon scheduler trace
  have output : message ∈ (runtime.reactiveApplication leaks).outputs
      (control.execution.recall who) := List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩
  rw [← recalled who] at output
  have sender : message.id.1 = who := of_decide_eq_true (List.mem_filter.mp output).2
  obtain ⟨ready, physicalLaw⟩ := runtime.reactiveDecision_binding_accepted_history leaks
    (inputs.map State.initial) horizon scheduler control trace who remembered.event payload
    outputEq codeEq node remembered.action serial entry entryMember declared
    (reactiveFreshSlot_spec entry.beforeView.application serial allocated) message packet sender
    after accepted
  have physicalStep : after.config ∈
      (control.execution.application.config.step remembered.event ready
        remembered.action).support := by
    rw [← physicalLaw, PMF.mem_support_pure_iff]
  let next := control.execution.includePending (runtime.reactiveApplication leaks) message.id
  have configEq : next.application.config = after.config := by
    simp only [next, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, accepted, Option.getD_some]
  have originalHistory := runtime.originalConfig_include_binding_history leaks inputs horizon
    scheduler control trace memories remembered who payload outputEq codeEq node message after
    found accepted
    (control.execution.application.config.step_history remembered.event ready remembered.action
      after.config physicalStep)
  have actor := runtime.prescribedReactivePosterior_owned leaks who (profile who)
    (consistent who) (memories who) (supported who) remembered (List.of_mem_zip retained).2
  have inputEq : after.config.inputs = control.execution.application.config.inputs := by
    rw [Config.step, PMF.support_map] at physicalStep
    obtain ⟨value, _, produced⟩ := physicalStep
    simpa only [Config.complete] using congrArg Config.inputs produced.symm
  constructor
  · rw [configEq, inputEq]
    exact related.reachable
  · rw [configEq, inputEq]
    exact related.inputs
  · intro event
    rw [configEq, control.execution.application.config.step_cut remembered.event ready
      remembered.action after.config physicalStep, EventOrder.Cut.mem_complete]
    constructor
    · intro completed
      rcases (related.domain event).mp completed with physical | saved
      · exact Or.inl (Or.inr physical)
      · exact Or.inr saved
    · rintro ((same | physical) | saved)
      · exact (related.domain event).mpr (Or.inr
          ⟨who, remembered, (List.of_mem_zip retained).2, same.symm⟩)
      · exact (related.domain event).mpr (Or.inl physical)
      · exact (related.domain event).mpr (Or.inr saved)
  · rw [configEq]
    have recorded : remembered ∈ frontier.history := (List.mem_filter.mp (by
      rw [related.intentions who]
      exact List.mem_filterMap.mpr ⟨some remembered, (List.of_mem_zip retained).2, rfl⟩ :
        remembered ∈ graph.ownCompletions who frontier.history)).1
    exact Config.CompletedOutputAgreement.settle_sampled_owned
      control.execution.application.config frontier after.config related.settled related.inputs.symm
      (by simpa only [related.inputs] using related.reachable) remembered recorded who actor ready
      physicalStep
  · exact related.intentions
  · intro observer
    rw [originalHistory]
    by_cases equal : observer = who
    · subst observer
      have suffix := related.pending_owner_suffix runtime leaks ordered control.execution
        (runtime.entryEventStable_history leaks (inputs.map State.initial) horizon scheduler trace)
        memories frontier profile consistent supported who remembered
        (List.of_mem_zip retained).2 ready
      have ownAppend : graph.ownCompletions who
          ((runtime.originalConfig leaks control.execution memories).history ++ [remembered]) =
          graph.ownCompletions who
            (runtime.originalConfig leaks control.execution memories).history ++
            [remembered] := by simp [ownCompletions, actor]
      rw [ownAppend, ← suffix]
    · have foreign : graph.actor? remembered.event ≠ some observer := by
        simpa only [actor, Option.some.injEq, ne_eq] using Ne.symm equal
      simpa [ownCompletions, foreign] using related.recalled observer

/-- Actual initialized raw traces record silence faithfully and retain the exact
call carried by every transmitted material, regardless of player policies. -/
theorem reactiveEmission_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (who : Player) :
    (∀ entry ∈ control.execution.recall who,
      entry.action.transmission = none → entry.emitted = none) ∧
    (∀ entry ∈ control.execution.recall who, ∀ material,
      entry.action.transmission = some material → ∃ message,
        entry.emitted = some message ∧ message.payload.call = material.call.packet) := by
  let app := runtime.reactiveApplication leaks
  have quietInvariant : app.ServiceInvariant scheduler (fun execution =>
      ∀ entry ∈ execution.recall who,
        entry.action.transmission = none → entry.emitted = none) := by
    constructor
    · intro execution actor action faithful
      exact
      (ReactiveApplication.silentEmission_invariant app (fun _ _ _ => PMF.pure action) who).respond
        execution actor action faithful (by simp)
    · intro execution next command faithful _ reached
      exact
      (ReactiveApplication.silentEmission_invariant app
          (fun _ _ _ => PMF.pure ⟨none⟩) who).environment
        execution next command faithful reached
  have sentInvariant : app.ServiceInvariant scheduler (fun execution =>
      ∀ entry ∈ execution.recall who, ∀ material,
        entry.action.transmission = some material → ∃ message,
          entry.emitted = some message ∧ message.payload.call = material.call.packet) := by
    constructor
    · intro execution actor action faithful
      exact
      (runtime.reactiveEmission_call_invariant leaks (fun _ _ _ => PMF.pure action) who).respond
        execution actor action faithful (by simp)
    · intro execution next command faithful _ reached
      exact
      (runtime.reactiveEmission_call_invariant leaks (fun _ _ _ => PMF.pure ⟨none⟩) who).environment
        execution next command faithful reached
  exact ⟨quietInvariant.history initial horizon (by
      intro state _ entry member
      simp [ReactiveApplication.Execution.initial] at member) trace,
    sentInvariant.history initial horizon (by
      intro state _ entry member
      simp [ReactiveApplication.Execution.initial] at member) trace⟩

/-- Every actually accepted pending envelope from the initialized prescribed
profile settles a sampled intention and preserves the entire semantic frontier. -/
theorem ReactiveFrontier.include_accepted (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.BarrierOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks control.execution memories frontier)
    (profile : graph.BehavioralProfile)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (control.execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (control.execution.recall owner)).support)
    (id : MessageId Player) (message : Message Player (WitnessedPacket graph))
    (found : control.execution.network.lookup id = some message)
    (after : State graph)
    (accepted : (runtime.reactiveApplication leaks).handle control.execution.application message =
      some after) :
    runtime.ReactiveFrontier leaks
      (control.execution.includePending (runtime.reactiveApplication leaks) id)
      memories frontier := by
  have identity : message.id = id := by
    simpa using (List.find?_eq_some_iff_append.mp found).1
  subst id
  let who := message.sender
  have provenance := (runtime.reactiveApplication leaks).history_provenance
    (inputs.map State.initial) horizon scheduler trace
  obtain ⟨entry, entryMember, material, transmitted, emitted, _, _, _⟩ :=
    provenance.lookup message.id message found
  obtain ⟨quiet, sent⟩ := runtime.reactiveEmission_history leaks (inputs.map State.initial)
    horizon scheduler control trace who
  obtain ⟨remembered, retained, addressed⟩ :=
    runtime.prescribedReactivePosterior_emitted_coverage leaks who (profile who)
      (consistent who) quiet sent (memories who) (supported who) entry entryMember message emitted
  have matching := runtime.prescribedReactivePosterior_decision_alignment leaks who (profile who)
    (consistent who) (memories who) (supported who) entry remembered retained
  have decisionSent : (runtime.reactiveDecision leaks who remembered.event remembered.action
      entry.beforeView.application).transmission = some material :=
    (congrArg ReactiveApplication.Action.transmission matching).symm.trans transmitted
  obtain ⟨actual, actualEmitted, packetEq⟩ := sent entry entryMember material transmitted
  have actualEq := Option.some.inj (actualEmitted.symm.trans emitted)
  subst actual
  have physical := reactiveHandle_call accepted
  cases node : nodeView graph remembered.event with
  | sample payload law outputEq codeEq =>
      simp [reactiveDecision, node] at decisionSent
  | bind owner payload outputEq codeEq =>
      have owns := runtime.prescribedReactivePosterior_owned leaks who (profile who)
        (consistent who) (memories who) (supported who) remembered (List.of_mem_zip retained).2
      have sameOwner : owner = who := Option.some.inj
        ((graph.actor?_of_outputLayout_binding outputEq).symm.trans owns)
      subst owner
      cases selected : reactiveFreshSlot entry.beforeView.application with
      | none => simp [reactiveDecision, node, selected] at decisionSent
      | some serial =>
        have materialEq := decisionSent
        simp only [reactiveDecision, node, selected, Option.map_some,
          Option.some.injEq] at materialEq
        subst material
        exact related.include_binding runtime leaks ordered inputs horizon scheduler control trace
          memories frontier profile consistent supported who entry remembered retained payload
          outputEq codeEq node serial selected message emitted packetEq after found accepted
  | resolve owner payload binding checks outputEq codeEq =>
      cases packet : message.payload.call with
      | malformed raw => simp [packet, handle] at physical
      | commitment event candidate =>
        have sameEvent : event = remembered.event := by
          simpa only [packet, Payload.event?, Option.some.injEq] using addressed
        subst event
        simp [packet, handle, node] at physical
      | opening event candidate raw =>
        have sameEvent : event = remembered.event := by
          simpa only [packet, Payload.event?, Option.some.injEq] using addressed
        subst event
        exact related.include_resolution runtime leaks ordered inputs horizon scheduler
          control trace
          memories frontier profile consistent supported who quiet sent entry remembered retained
          message emitted material transmitted owner payload binding checks outputEq codeEq node
          candidate raw packet after found accepted

private theorem ReactiveFrontier.include_rejected (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks control.execution memories frontier)
    (id : MessageId Player) (message : Message Player (WitnessedPacket graph))
    (found : control.execution.network.lookup id = some message)
    (rejected : (runtime.reactiveApplication leaks).handle control.execution.application message =
      none) :
    runtime.ReactiveFrontier leaks
      (control.execution.includePending (runtime.reactiveApplication leaks) id)
      memories frontier := by
  let next := control.execution.includePending (runtime.reactiveApplication leaks) id
  have configEq : next.application.config = control.execution.application.config := by
    simp only [next, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, rejected, Option.getD_none]
  have originalHistory : (runtime.originalConfig leaks next memories).history =
      (runtime.originalConfig leaks control.execution memories).history := by
    change next.application.config.history.map (runtime.originalCompletion leaks next memories) = _
    rw [configEq]
    apply List.map_congr_left
    intro completion member
    have completed := (control.execution.application.config.history_exact completion.event).mp
      (List.mem_map.mpr ⟨completion, member, rfl⟩)
    unfold originalCompletion
    split
    · rfl
    · exact runtime.reactiveOriginal_include_completed_history leaks inputs horizon scheduler
        control trace _ (memories _) id completion completed
  constructor
  · rw [configEq]
    exact related.reachable
  · rw [configEq]
    exact related.inputs
  · rw [configEq]
    exact related.domain
  · rw [configEq]
    exact related.settled
  · exact related.intentions
  · intro owner
    rw [originalHistory]
    exact related.recalled owner

/-- Every actual pending-inclusion command preserves the reachable sampled
frontier under the prescribed profile. Authentication, associated intentions,
prepared bindings and original recall are all derived from actual histories. -/
theorem ReactiveFrontier.include_pending (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.BarrierOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks control.execution memories frontier)
    (profile : graph.BehavioralProfile)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (control.execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (control.execution.recall owner)).support)
    (id : MessageId Player) :
    runtime.ReactiveFrontier leaks
      (control.execution.includePending (runtime.reactiveApplication leaks) id)
      memories frontier := by
  cases found : control.execution.network.lookup id with
  | none =>
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found] using related
  | some message =>
      cases accepted : (runtime.reactiveApplication leaks).handle
          control.execution.application message with
      | none =>
          exact related.include_rejected runtime leaks inputs horizon scheduler control trace
            memories frontier id message found accepted
      | some after =>
          exact related.include_accepted runtime leaks ordered inputs horizon scheduler control
            trace
            memories frontier profile consistent supported id message found after accepted

end Vegas.EventGraphRuntime
