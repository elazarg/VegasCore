/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFrontierSampling
import Vegas.Pending.ReactiveFrontierUniqueness
import Vegas.Pending.ReactiveFrontierEnvironment
import Vegas.Pending.ReactiveFrontierInclusion
import Interaction.ReactiveImplementation
import Interaction.ReactiveRecovery

/-! # Canonical continuation through actual reactive execution commands -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

open Classical in
/-- The canonical continuation of a reachable retained-intention frontier.
The value is independent of the chosen witness on actual supported memories. -/
def reactiveFrontierPotential (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) : PMF graph.SemanticKey :=
  if related : ∃ frontier, runtime.ReactiveFrontier leaks execution memories frontier then
    graph.canonicalContinuation profile (Classical.choose related)
  else graph.canonicalContinuation profile (runtime.originalConfig leaks execution memories)

/-- A genuine related frontier computes the witness-independent continuation. -/
theorem ReactiveFrontier.potential_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support) :
    runtime.reactiveFrontierPotential leaks profile execution memories =
      graph.canonicalContinuation profile frontier := by
  have existsFrontier : ∃ other, runtime.ReactiveFrontier leaks execution memories other :=
    ⟨frontier, related⟩
  unfold reactiveFrontierPotential
  rw [dite_eq_left existsFrontier]
  apply canonicalContinuation_congr
  exact ReactiveFrontier.semanticKey_unique runtime leaks execution stable memories
    (Classical.choose existsFrontier) frontier (Classical.choose_spec existsFrontier)
    related profile consistent supported

/-- At actual physical termination the retained canonical continuation reads
the exact physical typed store, including every input parameter. -/
theorem ReactiveFrontier.terminal_potential (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (terminal : execution.application.config.cut.Terminal) :
    (runtime.reactiveFrontierPotential leaks profile execution memories).map
      (fun key => key.2.1) = PMF.pure execution.application.config.store := by
  rw [related.potential_eq runtime leaks profile execution stable memories frontier
    consistent supported,
    ← canonicalContinuation_terminal profile frontier (related.settled.terminal _ _ terminal),
    PMF.pure_map]
  apply congrArg PMF.pure
  exact (related.settled.terminal_store _ _ related.inputs.symm terminal).symm

/-- Conditioning on a genuine compiler response retains its private memory
and consistent recall for every owner simultaneously. -/
theorem prescribedReactiveResponse_posterior_profile (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion))
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supportedMemory : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (who : Player) (action : (runtime.reactiveApplication leaks).Action)
    (saved : Option graph.Completion)
    (produced : (action, saved) ∈
      (runtime.prescribedReactiveResponse leaks who (profile who) (execution.recall who)
        (memories who) (execution.observe (runtime.reactiveApplication leaks) who)).support) :
    let next := execution.respond (runtime.reactiveApplication leaks) who action
    let nextMemories := Function.update memories who (memories who ++ [saved])
    (∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (next.recall owner)) ∧
    (∀ owner, nextMemories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (next.recall owner)).support) := by
  have transition : (action, memories who ++ [saved]) ∈
      ((runtime.prescribedReactiveImplementation leaks who (profile who)).respond
        (memories who) (execution.recall who,
          execution.observe (runtime.reactiveApplication leaks) who)).support := by
    rw [prescribedReactiveImplementation, PMF.support_map]
    exact ⟨(action, saved), produced, rfl⟩
  have actionSupported : action ∈
      (runtime.prescribedReactivePolicy leaks who (profile who) (execution.recall who)
        (execution.observe (runtime.reactiveApplication leaks) who)).support := by
    rw [prescribedReactivePolicy_apply, PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨memories who, supportedMemory who, ?_⟩
    rw [PMF.support_map]
    exact ⟨(action, saved), produced, rfl⟩
  refine ⟨(ReactiveApplication.consistentRecall_policyInvariant
    (fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner))).respond
      execution who action consistent actionSupported, ?_⟩
  intro owner
  by_cases equal : owner = who
  · subst owner
    rw [Function.update_self]
    exact ReactiveApplication.Implementation.mem_support_posterior_respond _ execution who
      (memories who) (memories who ++ [saved]) (supportedMemory who) action transition
  · rw [Function.update_of_ne equal,
      (runtime.reactiveApplication leaks).respond_recall_other execution who owner equal action]
    exact supportedMemory owner

/-- Every supported retained response has exactly the canonical continuation
of its original sampled action. No arbitrary frontier witness affects the law. -/
theorem ReactiveFrontier.response_continuation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supportedMemory : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (who : Player)
    (quiet : ∀ entry ∈ execution.recall who,
      entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ entry ∈ execution.recall who, ∀ material,
      entry.action.transmission = some material → ∃ message,
        entry.emitted = some message ∧ message.payload.call = material.call.packet)
    (action : (runtime.reactiveApplication leaks).Action) (saved : Option graph.Completion)
    (produced : (action, saved) ∈
      (runtime.prescribedReactiveResponse leaks who (profile who) (execution.recall who)
        (memories who) (execution.observe (runtime.reactiveApplication leaks) who)).support) :
    runtime.reactiveFrontierPotential leaks profile
      (execution.respond (runtime.reactiveApplication leaks) who action)
      (Function.update memories who (memories who ++ [saved])) =
        originalDecisionContinuation graph profile frontier saved := by
  have after := runtime.prescribedReactiveResponse_posterior_profile leaks profile execution
    memories consistent supportedMemory who action saved produced
  have aligned := (runtime.prescribedReactivePosterior_length leaks who (profile who)
    (consistent who) (memories who) (supportedMemory who)).symm
  have stableAfter := (runtime.entryEventStable_serviceInvariant leaks
    (fun _ _ => PMF.pure .wait)).respond execution who action stable
  cases saved with
  | none =>
      have nextRelated := related.respond_none runtime leaks execution memories frontier who
        (profile who) aligned action produced
      exact nextRelated.potential_eq runtime leaks profile _ stableAfter _ frontier
        after.1 after.2
  | some remembered =>
      obtain ⟨ready, next, stepped, nextRelated⟩ := related.respond_some runtime leaks execution
        memories frontier profile consistent supportedMemory who quiet sent aligned action
        remembered produced
      have actor := (runtime.prescribedReactiveResponse_some_ready leaks who (profile who)
        (execution.recall who) (memories who)
        (execution.observe (runtime.reactiveApplication leaks) who) action remembered produced).2
      rw [nextRelated.potential_eq runtime leaks profile _ stableAfter _ next after.1 after.2]
      simp only [originalDecisionContinuation, dite_eq_left ready]
      rw [frontier.step_eq_pure_of_actor remembered.event ready remembered.action who actor
          next stepped, PMF.pure_bind]

/-- Every actual prescribed callback preserves the full canonical continuation
potential, whether it samples a fresh decision or reuses retained memory. -/
theorem ReactiveFrontier.response_harmonic (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supportedMemory : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (who : Player)
    (quiet : ∀ entry ∈ execution.recall who,
      entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ entry ∈ execution.recall who, ∀ material,
      entry.action.transmission = some material → ∃ message,
        entry.emitted = some message ∧ message.payload.call = material.call.packet) :
    (runtime.prescribedReactiveResponse leaks who (profile who) (execution.recall who)
      (memories who) (execution.observe (runtime.reactiveApplication leaks) who)).bind
        (fun response => runtime.reactiveFrontierPotential leaks profile
          (execution.respond (runtime.reactiveApplication leaks) who response.1)
          (Function.update memories who (memories who ++ [response.2]))) =
      runtime.reactiveFrontierPotential leaks profile execution memories := by
  rw [related.potential_eq runtime leaks profile execution stable memories frontier
    consistent supportedMemory]
  calc
    _ = (runtime.prescribedReactiveResponse leaks who (profile who) (execution.recall who)
        (memories who) (execution.observe (runtime.reactiveApplication leaks) who)).bind
          (fun response => originalDecisionContinuation graph profile frontier response.2) := by
      apply bind_congr_on_support
      rintro ⟨action, saved⟩ produced
      exact related.response_continuation runtime leaks profile execution stable memories
        frontier consistent supportedMemory who quiet sent action saved produced
    _ = graph.canonicalContinuation profile frontier := by
      cases turn : execution.application.publicView.ownTurn? who with
      | none =>
          simp [prescribedReactiveResponse, ReactiveApplication.Execution.observe,
            reactiveApplication, State.playerView, turn, originalDecisionContinuation]
      | some event =>
          obtain ⟨ready, actor⟩ := execution.application.publicView.ownTurn?_spec who event turn
          by_cases blocked : runtime.reactiveAlreadySubmitted leaks (execution.recall who) event ||
              runtime.reactiveAlreadyDecided leaks who (execution.recall who) (memories who) event
          · simp [prescribedReactiveResponse, ReactiveApplication.Execution.observe,
              reactiveApplication, State.playerView, turn, blocked, originalDecisionContinuation]
          · have unblocked := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr blocked)
            obtain ⟨action, actionSupported⟩ := (graph.normalizePolicy who (profile who)
              event actor (graph.playerObserve who
                (runtime.originalConfig leaks execution memories))).support_nonempty
            have produced :
                (runtime.reactiveDecision leaks who event action
                    (execution.observe (runtime.reactiveApplication leaks) who).application,
                  some (⟨event, action⟩ : graph.Completion)) ∈
                (runtime.prescribedReactiveResponse leaks who (profile who)
                  (execution.recall who) (memories who)
                  (execution.observe (runtime.reactiveApplication leaks) who)).support := by
              rw [runtime.prescribedReactiveResponse_originalConfig leaks execution memories who
                (profile who) event turn unblocked.1 unblocked.2 actor, PMF.support_map]
              exact ⟨action, actionSupported, rfl⟩
            have freshMemory := runtime.prescribedReactiveResponse_event_not_saved leaks who
              (profile who) (consistent who) quiet sent (memories who) (supportedMemory who)
              (execution.observe (runtime.reactiveApplication leaks) who) _ _ produced
            exact related.sampled_response_canonicalContinuation runtime leaks ordered execution
              stable profile memories consistent supportedMemory frontier who event turn actor
              freshMemory unblocked.1 unblocked.2

/-- An actual public chance command preserves the canonical continuation
potential using its genuine common draw with the retained frontier. -/
theorem ReactiveFrontier.sample_harmonic (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supportedMemory : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (event : graph.EventId) (physicalReady : execution.application.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (node : nodeView graph event = .sample payload law outputEq codeEq) :
    (execution.environmentStep (runtime.reactiveApplication leaks)
      (.application (.executeSample event))).bind
        (fun next => runtime.reactiveFrontierPotential leaks profile next memories) =
      runtime.reactiveFrontierPotential leaks profile execution memories := by
  obtain ⟨ready, joint, physicalMarginal, frontierMarginal, preserves⟩ :=
    related.sample_coupling runtime leaks execution memories frontier profile consistent
      supportedMemory event physicalReady payload law outputEq codeEq node
  have chance : graph.actor? event = none := by
    change (graph.nodes event).actor = none
    rw [← EventCode.actor_cast outputEq (graph.nodes event), codeEq]
    rfl
  have jointKernel : joint.bind (fun pair =>
      runtime.reactiveFrontierPotential leaks profile pair.1 memories) =
        joint.bind (fun pair => graph.canonicalContinuation profile pair.2) := by
    apply bind_congr_on_support
    intro pair supported
    have physicalSupported : pair.1 ∈ (execution.environmentStep
        (runtime.reactiveApplication leaks) (.application (.executeSample event))).support := by
      rw [← physicalMarginal, PMF.support_map]
      exact ⟨pair, supported, rfl⟩
    have recallEq := (runtime.reactiveApplication leaks).environmentStep_recall
      execution pair.1 (.application (.executeSample event)) physicalSupported
    have stableAfter := (runtime.entryEventStable_serviceInvariant leaks
      (fun _ _ => PMF.pure (.application (.executeSample event)))).environment execution pair.1
      (.application (.executeSample event)) stable (by simp [reactiveApplication]) physicalSupported
    exact (preserves pair supported).potential_eq runtime leaks profile pair.1 stableAfter
      memories pair.2 (by simpa only [recallEq] using consistent)
        (by simpa only [recallEq] using supportedMemory)
  rw [← physicalMarginal, PMF.bind_map]
  simp only [Function.comp_def]
  rw [jointKernel]
  change joint.bind ((graph.canonicalContinuation profile) ∘ Prod.snd) = _
  rw [← PMF.bind_map, frontierMarginal]
  have harmonic := (ordered.readyIndependent profile).normalizedThenCanonical_eq
    frontier event ready
  have stepEq : graph.normalizedPolicyStep profile frontier event ready =
      frontier.step event ready (cast (congrArg EventField.Action outputEq.symm) PUnit.unit) := by
    unfold normalizedPolicyStep
    split
    · rename_i owner owned
      rw [chance] at owned
      cases owned
    · congr 1
      exact EventCode.action_eq_of_actor_none (graph.nodes event) chance _ _
  unfold normalizedThenCanonical at harmonic
  rw [stepEq] at harmonic
  exact harmonic.trans (related.potential_eq runtime leaks profile execution stable memories
    frontier consistent supportedMemory).symm

private theorem frontier_stutter_harmonic (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supportedMemory : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (command : (runtime.reactiveApplication leaks).Command)
    (preserves : ∀ next, next ∈ (execution.environmentStep
      (runtime.reactiveApplication leaks) command).support →
      runtime.ReactiveFrontier leaks next memories frontier) :
    (execution.environmentStep (runtime.reactiveApplication leaks) command).bind
      (fun next => runtime.reactiveFrontierPotential leaks profile next memories) =
        runtime.reactiveFrontierPotential leaks profile execution memories := by
  calc
    _ = (execution.environmentStep (runtime.reactiveApplication leaks) command).bind
        (fun _ => graph.canonicalContinuation profile frontier) := by
      apply bind_congr_on_support
      intro next reached
      have recallEq := (runtime.reactiveApplication leaks).environmentStep_recall
        execution next command reached
      have stableNext := (runtime.entryEventStable_serviceInvariant leaks
        (fun _ _ => PMF.pure command)).environment execution next command stable
          (by simp) reached
      exact (preserves next reached).potential_eq runtime leaks profile next stableNext
        memories frontier (by simpa only [recallEq] using consistent)
          (by simpa only [recallEq] using supportedMemory)
    _ = graph.canonicalContinuation profile frontier := PMF.bind_const _ _
    _ = _ := (related.potential_eq runtime leaks profile execution stable memories frontier
      consistent supportedMemory).symm

theorem ReactiveFrontier.passive_command_harmonic (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supportedMemory : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (command : (runtime.reactiveApplication leaks).Command)
    (passive : command = .wait ∨ (∃ owner, command = .activate owner) ∨
      command = .application .advanceClock) :
    (execution.environmentStep (runtime.reactiveApplication leaks) command).bind
      (fun next => runtime.reactiveFrontierPotential leaks profile next memories) =
        runtime.reactiveFrontierPotential leaks profile execution memories := by
  apply frontier_stutter_harmonic runtime leaks profile execution stable memories frontier
    related consistent supportedMemory
  intro next reached
  rcases passive with rfl | ⟨owner, rfl⟩ | rfl
  · exact related.wait runtime leaks execution next memories frontier reached
  · exact related.activate runtime leaks execution next memories frontier owner reached
  · exact related.advanceClock runtime leaks execution next memories frontier reached

theorem ReactiveFrontier.sample_command_harmonic (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supportedMemory : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (event : graph.EventId) :
    (execution.environmentStep (runtime.reactiveApplication leaks)
      (.application (.executeSample event))).bind
        (fun next => runtime.reactiveFrontierPotential leaks profile next memories) =
      runtime.reactiveFrontierPotential leaks profile execution memories := by
  have stutter (law : environmentStep runtime execution.application (.executeSample event) =
      PMF.pure execution.application) :
      ∀ next, next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
        (.application (.executeSample event))).support →
        runtime.ReactiveFrontier leaks next memories frontier := by
    intro next reached
    simp only [ReactiveApplication.Execution.environmentStep, reactiveApplication, law,
      PMF.pure_map, PMF.mem_support_pure_iff] at reached
    subst next
    exact related.congr_execution runtime leaks _ _ memories frontier rfl rfl rfl
  by_cases ready : execution.application.config.cut.Ready event
  · cases node : nodeView graph event with
    | sample payload law outputEq codeEq =>
        exact related.sample_harmonic runtime leaks ordered profile execution stable memories
          frontier consistent supportedMemory event ready payload law outputEq codeEq node
    | bind owner payload outputEq codeEq =>
        apply frontier_stutter_harmonic runtime leaks profile execution stable memories frontier
          related consistent supportedMemory
        apply stutter
        exact environmentStep_executeSample_of_nonsample runtime execution.application event ready
          (by
            intro payload law outputEq codeEq impossible
            rw [node] at impossible
            cases impossible)
    | resolve owner payload binding checks outputEq codeEq =>
        apply frontier_stutter_harmonic runtime leaks profile execution stable memories frontier
          related consistent supportedMemory
        apply stutter
        exact environmentStep_executeSample_of_nonsample runtime execution.application event ready
          (by
            intro payload law outputEq codeEq impossible
            rw [node] at impossible
            cases impossible)
  · apply frontier_stutter_harmonic runtime leaks profile execution stable memories frontier
      related consistent supportedMemory
    exact stutter (environmentStep_executeSample_of_not_ready runtime execution.application
      event ready)

theorem ReactiveFrontier.passive_command_frontier_exists (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (command : (runtime.reactiveApplication leaks).Command)
    (passive : command = .wait ∨ (∃ owner, command = .activate owner) ∨
      command = .application .advanceClock)
    (next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) :
    ∃ nextFrontier, runtime.ReactiveFrontier leaks next memories nextFrontier := by
  refine ⟨frontier, ?_⟩
  rcases passive with rfl | ⟨owner, rfl⟩ | rfl
  · exact related.wait runtime leaks execution next memories frontier reached
  · exact related.activate runtime leaks execution next memories frontier owner reached
  · exact related.advanceClock runtime leaks execution next memories frontier reached

theorem ReactiveFrontier.sample_command_frontier_exists (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supportedMemory : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (event : graph.EventId) (next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      (.application (.executeSample event))).support) :
    ∃ nextFrontier, runtime.ReactiveFrontier leaks next memories nextFrontier := by
  have stutter (law : environmentStep runtime execution.application (.executeSample event) =
      PMF.pure execution.application) :
      runtime.ReactiveFrontier leaks next memories frontier := by
    simp only [ReactiveApplication.Execution.environmentStep, reactiveApplication, law,
      PMF.pure_map, PMF.mem_support_pure_iff] at reached
    subst next
    exact related.congr_execution runtime leaks _ _ memories frontier rfl rfl rfl
  by_cases ready : execution.application.config.cut.Ready event
  · cases node : nodeView graph event with
    | sample payload law outputEq codeEq =>
        obtain ⟨_, joint, physicalMarginal, _, preserves⟩ :=
          related.sample_coupling runtime leaks execution memories frontier profile consistent
            supportedMemory event ready payload law outputEq codeEq node
        rw [← physicalMarginal, PMF.support_map, Set.mem_image] at reached
        obtain ⟨pair, member, equal⟩ := reached
        exact ⟨pair.2, equal ▸ preserves pair member⟩
    | bind owner payload outputEq codeEq =>
        refine ⟨frontier, stutter ?_⟩
        exact environmentStep_executeSample_of_nonsample runtime execution.application event ready
          (by
            intro payload law outputEq codeEq impossible
            rw [node] at impossible
            cases impossible)
    | resolve owner payload binding checks outputEq codeEq =>
        refine ⟨frontier, stutter ?_⟩
        exact environmentStep_executeSample_of_nonsample runtime execution.application event ready
          (by
            intro payload law outputEq codeEq impossible
            rw [node] at impossible
            cases impossible)
  · exact ⟨frontier, stutter (environmentStep_executeSample_of_not_ready runtime
      execution.application event ready)⟩

theorem ReactiveFrontier.include_command_frontier_exists (runtime : EventGraphRuntime graph)
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
    (supportedMemory : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (control.execution.recall owner)).support)
    (id : MessageId Player) (next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep (runtime.reactiveApplication leaks)
      (.include id)).support) :
    ∃ nextFrontier, runtime.ReactiveFrontier leaks next memories nextFrontier := by
  have settled := related.include_pending runtime leaks ordered inputs horizon scheduler control
    trace memories frontier profile consistent supportedMemory id
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
    PMF.mem_support_pure_iff] at reached
  subst next
  exact ⟨frontier, settled.congr_execution runtime leaks _ _ memories frontier rfl rfl rfl⟩

theorem ReactiveFrontier.include_command_harmonic (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.BarrierOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (stable : runtime.EntryEventStable leaks control.execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks control.execution memories frontier)
    (profile : graph.BehavioralProfile)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (control.execution.recall owner))
    (supportedMemory : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (control.execution.recall owner)).support)
    (id : MessageId Player) :
    (control.execution.environmentStep (runtime.reactiveApplication leaks) (.include id)).bind
      (fun next => runtime.reactiveFrontierPotential leaks profile next memories) =
        runtime.reactiveFrontierPotential leaks profile control.execution memories := by
  apply frontier_stutter_harmonic runtime leaks profile control.execution stable memories frontier
    related consistent supportedMemory
  intro next reached
  have settled := related.include_pending runtime leaks ordered inputs horizon scheduler control
    trace memories frontier profile consistent supportedMemory id
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
    PMF.mem_support_pure_iff] at reached
  subst next
  exact settled.congr_execution runtime leaks _ _ memories frontier rfl rfl rfl

/-- Every genuinely conditioned posterior after an actual behavioral response
has a reachable retained frontier, reconstructed from a genuine predecessor
private-memory profile and its supported implementation transition. -/
theorem respond_policy_frontier_exists (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (frontiers : ∀ memories : Player → List (Option graph.Completion),
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
        ∃ frontier, runtime.ReactiveFrontier leaks execution memories frontier)
    (who : Player)
    (quiet : ∀ entry ∈ execution.recall who,
      entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ entry ∈ execution.recall who, ∀ material,
      entry.action.transmission = some material → ∃ message,
        entry.emitted = some message ∧ message.payload.call = material.call.packet)
    (action : (runtime.reactiveApplication leaks).Action)
    (chosen : action ∈ (runtime.prescribedReactivePolicy leaks who (profile who)
      (execution.recall who) (execution.observe (runtime.reactiveApplication leaks) who)).support)
    (afterMemories : Player → List (Option graph.Completion))
    (supported : ∀ owner, afterMemories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        ((execution.respond (runtime.reactiveApplication leaks) who action).recall owner)).support)
    :
    ∃ frontier, runtime.ReactiveFrontier leaks
      (execution.respond (runtime.reactiveApplication leaks) who action)
        afterMemories frontier := by
  let implementation := runtime.prescribedReactiveImplementation leaks who (profile who)
  have posterior := supported who
  rw [implementation.posterior_respond execution who action, PMF.support_map,
    Set.mem_image] at posterior
  obtain ⟨response, conditioned, memoryEq⟩ := posterior
  have positive : action ∈ (((implementation.posterior (execution.recall who)).bind fun memory =>
      implementation.respond memory
        (execution.recall who, execution.observe (runtime.reactiveApplication leaks) who)).map
          Prod.fst).support := chosen
  have genuine := mem_support_fiberPosterior positive conditioned
  obtain ⟨memory, memorySupported, produced⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ genuine.2)
  have pairEq : response = (action, afterMemories who) := Prod.ext genuine.1 memoryEq
  rw [pairEq] at produced
  change (action, afterMemories who) ∈
    ((runtime.prescribedReactiveResponse leaks who (profile who) (execution.recall who) memory
      (execution.observe (runtime.reactiveApplication leaks) who)).map
        (fun response => (response.1, memory ++ [response.2]))).support at produced
  obtain ⟨⟨actual, saved⟩, produced, pairEq⟩ := PMF.support_map .. ▸ produced
  have actionEq : actual = action := congrArg Prod.fst pairEq
  have appended : memory ++ [saved] = afterMemories who := congrArg Prod.snd pairEq
  subst actual
  let memories := Function.update afterMemories who memory
  have prior : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support := by
    intro owner
    by_cases equal : owner = who
    · subst owner
      simpa only [memories, Function.update_self, implementation] using memorySupported
    · simpa only [memories, Function.update_of_ne equal,
        (runtime.reactiveApplication leaks).respond_recall_other execution who owner equal action]
        using supported owner
  obtain ⟨frontier, related⟩ := frontiers memories prior
  have produces : (action, saved) ∈
      (runtime.prescribedReactiveResponse leaks who (profile who) (execution.recall who)
        (memories who) (execution.observe (runtime.reactiveApplication leaks) who)).support := by
    simpa only [memories, Function.update_self] using produced
  have restored : Function.update memories who (memories who ++ [saved]) = afterMemories := by
    funext owner
    by_cases equal : owner = who
    · subst owner
      simpa only [memories, Function.update_self] using appended
    · simp only [Function.update_of_ne equal, memories]
  have aligned := (runtime.prescribedReactivePosterior_length leaks who (profile who)
    (consistent who) (memories who) (prior who)).symm
  cases saved with
  | none =>
      refine ⟨frontier, ?_⟩
      rw [← restored]
      exact related.respond_none runtime leaks execution memories frontier who (profile who)
        aligned action produces
  | some remembered =>
      obtain ⟨_, next, _, nextRelated⟩ := related.respond_some runtime leaks execution memories
        frontier profile consistent prior who quiet sent aligned action remembered produces
      exact ⟨next, restored ▸ nextRelated⟩

end Vegas.EventGraphRuntime
