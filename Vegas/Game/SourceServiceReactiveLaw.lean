/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceExpiry
import Vegas.Pending.ReactiveFrontierExecution
import Vegas.Compile.EventGraphCanonicalContinuation

noncomputable section
namespace Vegas
open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] [Finite Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Actual protected asynchronous execution preserves the complete source input/output law,
 including its correlation with the original initial source-state draw. -/
theorem source_prescribed_terminal_joint_store_law
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} (keepsReveals : mode ≠ .concurrentReveals)
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (contract : (serviceRuntime setup mode deadline).AsyncContract leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (profile : (serviceGraph setup mode).BehavioralProfile) :
    setup.initialLaw.bind (fun initial =>
      ((serviceApplication setup mode deadline leaks).runRounds scheduler
        (fun owner => (serviceRuntime setup mode deadline).prescribedReactivePolicy leaks
          owner (profile owner)) horizon
        (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks)
          (State.initial (setup.eventInputs initial)))).map
            (fun next => (initial, next.application.config.store))) =
      setup.initialLaw.bind (fun initial =>
        ((serviceGraph setup mode).canonicalContinuation profile
          (EventGraph.Config.initial (setup.eventInputs initial))).map
            (fun key => (initial, key.2.1))) := by
  let _ := Fintype.ofFinite Player
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  let graph := serviceGraph setup mode
  let inputs : PMF graph.Inputs := setup.initialLaw.map setup.eventInputs
  let players := fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)
  let safe : app.Execution → Prop := fun execution =>
    execution.application.BindingInvariant ∧ runtime.RecordedTimelyCalls leaks execution
  have initialEq : inputs.map State.initial = serviceInitialLaw setup mode := by
    simp only [inputs, serviceInitialLaw, PMF.map_comp, Function.comp_def]
  have ordered := serviceGraph_barrierOrdered setup keepsReveals
  have invariant := runtime.recordedTimelyCalls_policyInvariant leaks profile
  have expiry : ∀ remaining execution,
      Nonempty (((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩)) → safe execution →
      (∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner)) → ∀ memories frontier,
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
      runtime.ReactiveFrontier leaks execution memories frontier → ∀ event next,
        next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
          (.application (.expire event))).support →
        runtime.ReactiveFrontier leaks next memories frontier := by
    intro remaining execution ⟨trace⟩ valid consistent memories frontier supported related
      event next moved
    have sourceTrace := initialEq ▸ trace
    have faithful := runtime.reactiveEmission_history leaks (serviceInitialLaw setup mode)
      horizon scheduler ⟨remaining + 1, none, execution⟩ sourceTrace
    exact source_prescribed_expiry_frontier setup leaks horizon scheduler delay bound
      contract.opportunity timely contract.inclusion ordered ⟨remaining + 1, none, execution⟩
      sourceTrace rfl valid.1 valid.2 profile memories consistent
      (fun owner => (faithful owner).1) (fun owner => (faithful owner).2)
      supported frontier related event next moved
  have completes : runtime.CompletesPlay leaks (inputs.map State.initial) horizon scheduler :=
    initialEq.symm ▸ contract.completes
  apply bind_congr_on_support
  intro initial supportedInitial
  let execution := ReactiveApplication.Execution.initial app
    (State.initial (setup.eventInputs initial))
  have supportedInput : setup.eventInputs initial ∈ inputs.support := by
    rw [PMF.support_map]
    exact ⟨initial, supportedInitial, rfl⟩
  have supportedState : State.initial (graph := graph) (setup.eventInputs initial) ∈
      (inputs.map State.initial).support := by
    rw [PMF.support_map]
    exact ⟨setup.eventInputs initial, supportedInput, rfl⟩
  obtain ⟨initialTrace⟩ := app.raw_trace_roundsFrom (inputs.map State.initial) horizon scheduler
    players 0 (Nat.zero_le horizon) execution (by
      rw [ReactiveApplication.roundsFrom, PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨State.initial (setup.eventInputs initial), supportedState, ?_⟩
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have valid : safe execution := by
    refine ⟨State.initial_bindingInvariant _, ?_⟩
    intro owner entry member
    exact (List.not_mem_nil member).elim
  have consistent : ∀ owner, (players owner).Consistent (execution.recall owner) :=
    fun _ => ReactiveApplication.Policy.Consistent.nil
  have frontiers : ∀ memories : Player → List (Option graph.Completion),
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
        ∃ frontier, runtime.ReactiveFrontier leaks execution memories frontier := by
    intro memories supported
    have empty : memories = fun _ => [] := by
      funext owner
      exact (PMF.mem_support_pure_iff _ _).mp (supported owner)
    rw [empty]
    exact ⟨EventGraph.Config.initial (setup.eventInputs initial),
      runtime.reactiveFrontier_initial leaks (setup.eventInputs initial)⟩
  have law := runRounds_terminal_store_of_expiry runtime leaks ordered profile inputs horizon
    scheduler safe invariant expiry completes horizon execution
      (by simpa only [Nat.sub_zero] using initialTrace) valid consistent frontiers
  rw [initial_posterior_potential runtime leaks profile (setup.eventInputs initial)] at law
  have joint := congrArg (fun distribution => distribution.map (fun store => (initial, store))) law
  simpa only [PMF.map_comp, Function.comp_def] using joint

/-- The initialized native execution and the original source semantics have the same
 joint initial-state and decoded final-state distribution. -/
theorem source_prescribed_terminal_joint_law
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} (keepsReveals : mode ≠ .concurrentReveals)
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (contract : (serviceRuntime setup mode deadline).AsyncContract leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (profile : SourceProgram.BehavioralProfile setup.program) :
    setup.initialLaw.bind (fun initial =>
      ((serviceApplication setup mode deadline leaks).runRounds scheduler
        (fun owner => (serviceRuntime setup mode deadline).prescribedReactivePolicy leaks owner
          ((setup.eventGraph.toModeProfile mode (compileEventProfile setup.program profile)) owner))
        horizon (ReactiveApplication.Execution.initial
          (serviceApplication setup mode deadline leaks)
          (State.initial (setup.eventInputs initial)))).map
            (fun next => (initial, decodeState? (terminalRefs setup.program)
              next.application.config.store))) =
      setup.initialLaw.bind (fun initial =>
        (SourceProgram.run setup.program profile initial).map
          (fun final => (initial, some final))) := by
  have storeLaw := source_prescribed_terminal_joint_store_law setup keepsReveals leaks
    horizon scheduler delay bound contract timely
      (setup.eventGraph.toModeProfile mode (compileEventProfile setup.program profile))
  have decoded := congrArg (fun distribution => distribution.map
    (fun pair => (pair.1, decodeState? (terminalRefs setup.program) pair.2))) storeLaw
  rw [PMF.map_bind, PMF.map_bind] at decoded
  simp only [PMF.map_comp, Function.comp_def] at decoded
  rw [decoded]
  apply bind_congr_on_support
  intro initial _
  have projected := congrArg (fun distribution => distribution.map (fun final => (initial, final)))
    (canonicalContinuation_mode_source_decode setup.program profile mode initial)
  simpa only [serviceGraph, Setup.eventGraph, Setup.eventInputs,
    PMF.map_comp, Function.comp_def] using projected

end Vegas
