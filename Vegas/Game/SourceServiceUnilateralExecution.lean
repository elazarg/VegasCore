/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceUnilateralRound
import Interaction.ReactivePolicyInvariant
import Interaction.ReactiveRecallInvariant

/-! # Actual unilateral source-service execution support -/

noncomputable section
namespace Vegas
open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every supported actual continuation retains a reachable mixed frontier
for every genuine foreign posterior memory. The induction uses actual service
and arbitrary focal responses, and makes no source/noise factorization claim. -/
theorem source_unilateral_runRounds_frontier
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (opportunity : (serviceRuntime setup mode deadline).Opportunity leaks
      (serviceInitialLaw setup mode) horizon scheduler delay)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (ordered : (serviceGraph setup mode).RevealRelaxedOrdered)
    (profile : (serviceGraph setup mode).BehavioralProfile)
    (focal : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (count remaining : Nat)
    (execution next : (serviceApplication setup mode deadline leaks).Execution)
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some ⟨remaining + count, none, execution⟩))
    (valid : execution.application.BindingInvariant ∧
      ∀ owner : {who : Player // who ≠ focal},
        (serviceRuntime setup mode deadline).RecordedTimelyCalls leaks owner.val execution)
    (consistent : ∀ owner,
      ((Function.update (fun who => (serviceRuntime setup mode deadline).prescribedReactivePolicy
        leaks who (profile who)) focal deviation) owner).Consistent (execution.recall owner))
    (frontiers : ∀ memories : Player → List (Option (serviceGraph setup mode).Completion),
      memories focal = [] →
      (∀ owner, owner ≠ focal → memories owner ∈
        (((serviceRuntime setup mode deadline).prescribedReactiveImplementation leaks owner
          (profile owner)).posterior (execution.recall owner)).support) →
      ∃ frontier, (serviceRuntime setup mode deadline).ReactiveUnilateralFrontier leaks focal
        execution memories frontier)
    (reached : next ∈ ((serviceApplication setup mode deadline leaks).runRounds scheduler
      (Function.update (fun owner => (serviceRuntime setup mode deadline).prescribedReactivePolicy
        leaks owner (profile owner)) focal deviation) count execution).support) :
    ∀ memories : Player → List (Option (serviceGraph setup mode).Completion),
      memories focal = [] →
      (∀ owner, owner ≠ focal → memories owner ∈
        (((serviceRuntime setup mode deadline).prescribedReactiveImplementation leaks owner
          (profile owner)).posterior (next.recall owner)).support) →
      ∃ frontier, (serviceRuntime setup mode deadline).ReactiveUnilateralFrontier leaks focal
        next memories frontier := by
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  let players := Function.update
    (fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)) focal deviation
  induction count generalizing execution next with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact frontiers
  | succ count ih =>
      have before : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
          (some ⟨remaining + count + 1, none, execution⟩) := by
        simpa only [Nat.add_assoc] using trace
      obtain ⟨middle, first, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have one : middle ∈ (app.runRounds scheduler players 1 execution).support := by
        simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using first
      obtain ⟨middleTrace⟩ := app.raw_trace_round (serviceInitialLaw setup mode) horizon scheduler
        players (remaining + count) execution middle before first
      have nextValid := (runtime.recordedTimelyCalls_unilateral_policyInvariant leaks profile
        focal deviation).runRounds scheduler 1 execution middle valid one
      have nextConsistent := (app.consistentRecall_policyInvariant players).runRounds
        scheduler 1 execution middle consistent one
      have foreignConsistent : ∀ owner, owner ≠ focal →
          (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
            (execution.recall owner) := by
        intro owner foreign
        simpa only [players, Function.update_of_ne foreign] using consistent owner
      have nextFrontiers := source_unilateral_round_frontier setup leaks ordered profile
        horizon scheduler delay bound opportunity timely inclusion focal deviation
        (remaining + count) execution before valid.1
        (fun owner foreign => valid.2 ⟨owner, foreign⟩) foreignConsistent frontiers middle first
      exact ih middle next middleTrace nextValid nextConsistent nextFrontiers later

/-- Actual initialized play under one arbitrary raw focal policy admits a
reachable mixed source frontier at every supported bounded execution prefix. -/
theorem source_unilateral_initialized_frontier
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (opportunity : (serviceRuntime setup mode deadline).Opportunity leaks
      (serviceInitialLaw setup mode) horizon scheduler delay)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (profile : (serviceGraph setup mode).BehavioralProfile)
    (focal : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (initial : State L setup.context) (supportedInitial : initial ∈ setup.initialLaw.support)
    (count : Nat) (within : count ≤ horizon)
    (next : (serviceApplication setup mode deadline leaks).Execution)
    (reached : next ∈ ((serviceApplication setup mode deadline leaks).runRounds scheduler
      (Function.update (fun owner => (serviceRuntime setup mode deadline).prescribedReactivePolicy
        leaks owner (profile owner)) focal deviation) count
      (.initial (serviceApplication setup mode deadline leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs initial)))).support)
    (memories : Player → List (Option (serviceGraph setup mode).Completion))
    (empty : memories focal = [])
    (supported : ∀ owner, owner ≠ focal → memories owner ∈
      (((serviceRuntime setup mode deadline).prescribedReactiveImplementation leaks owner
        (profile owner)).posterior (next.recall owner)).support) :
    ∃ frontier, (serviceRuntime setup mode deadline).ReactiveUnilateralFrontier leaks focal
      next memories frontier := by
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  let players := Function.update
    (fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)) focal deviation
  let execution := ReactiveApplication.Execution.initial app
    (EventGraphRuntime.State.initial (setup.eventInputs initial))
  have supportedState : EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
      (setup.eventInputs initial) ∈ (serviceInitialLaw setup mode).support := by
    rw [serviceInitialLaw, PMF.support_map]
    exact ⟨initial, supportedInitial, rfl⟩
  obtain ⟨initialTrace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
    players 0 (Nat.zero_le horizon) execution (by
      rw [ReactiveApplication.roundsFrom, PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨EventGraphRuntime.State.initial (setup.eventInputs initial),
        supportedState, ?_⟩
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have valid : execution.application.BindingInvariant ∧
      ∀ owner : {who : Player // who ≠ focal},
        runtime.RecordedTimelyCalls leaks owner.val execution := by
    refine ⟨EventGraphRuntime.State.initial_bindingInvariant _, ?_⟩
    intro owner entry retained
    exact (List.not_mem_nil retained).elim
  have consistent : ∀ owner, (players owner).Consistent (execution.recall owner) := fun _ => .nil
  have frontiers : ∀ saved : Player → List (Option (serviceGraph setup mode).Completion),
      saved focal = [] →
      (∀ owner, owner ≠ focal → saved owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
      ∃ frontier, runtime.ReactiveUnilateralFrontier leaks focal execution saved frontier := by
    intro saved savedEmpty retained
    have allEmpty : saved = fun _ => [] := by
      funext owner
      by_cases same : owner = focal
      · exact same ▸ savedEmpty
      · exact (PMF.mem_support_pure_iff _ _).mp (retained owner same)
    rw [allEmpty]
    exact ⟨EventGraph.Config.initial (setup.eventInputs initial),
      runtime.reactiveUnilateralFrontier_initial leaks focal (setup.eventInputs initial)⟩
  exact source_unilateral_runRounds_frontier setup leaks horizon scheduler delay bound
    opportunity timely inclusion (serviceGraph_revealRelaxedOrdered setup mode) profile
    focal deviation count (horizon - count) execution next
    (by simpa only [Nat.sub_add_cancel within, Nat.sub_zero] using initialTrace)
    valid consistent frontiers reached memories empty supported

end Vegas
