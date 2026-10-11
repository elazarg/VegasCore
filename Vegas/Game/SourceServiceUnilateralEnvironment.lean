/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceUnilateralExpiry
import Vegas.Pending.ReactiveUnilateralCommands
import Vegas.Pending.ReactiveUnilateralSettlement

/-! # Actual source-service environment support with one arbitrary raw player -/

noncomputable section
namespace Vegas
open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- All actual source-service commands admit a reachable mixed frontier under
the existing operational opportunity, timing and protected inclusion contract.
No desired source execution or noise law is supplied as a hypothesis. -/
theorem source_unilateral_environment_frontier
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
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some control)) (idle : control.actor = none)
    (valid : control.execution.application.BindingInvariant) (focal : Player)
    (conformance : ∀ owner, owner ≠ focal → (serviceRuntime setup mode deadline).RecordedTimelyCalls
      leaks owner
      control.execution)
    (profile : (serviceGraph setup mode).BehavioralProfile)
    (memories : Player → List (Option (serviceGraph setup mode).Completion))
    (consistent : ∀ owner, owner ≠ focal →
      ((serviceRuntime setup mode deadline).prescribedReactivePolicy leaks
      owner (profile owner)).Consistent (control.execution.recall owner))
    (supported : ∀ owner, owner ≠ focal → memories owner ∈
      (((serviceRuntime setup mode deadline).prescribedReactiveImplementation leaks owner
        (profile owner)).posterior (control.execution.recall owner)).support)
    (frontier : (serviceGraph setup mode).Config)
    (related : (serviceRuntime setup mode deadline).ReactiveUnilateralFrontier
      leaks focal control.execution
      memories frontier)
    (command : (serviceApplication setup mode deadline leaks).Command)
    (after : (serviceApplication setup mode deadline leaks).Execution)
    (moved : after ∈ (control.execution.environmentStep
      (serviceApplication setup mode deadline leaks) command).support) :
    ∃ final, (serviceRuntime setup mode deadline).ReactiveUnilateralFrontier leaks focal
      after memories final := by
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map setup.eventInputs
  have initialEq : inputs.map State.initial = serviceInitialLaw setup mode := by
    simp only [inputs, PMF.map_comp, Function.comp_def, serviceInitialLaw]
  cases command with
  | wait =>
      exact ⟨frontier, related.wait runtime leaks control.execution after focal
        memories frontier moved⟩
  | activate who =>
      exact ⟨frontier, related.activate runtime leaks control.execution after focal
        memories frontier who moved⟩
  | «include» id =>
      obtain ⟨final, settled⟩ := related.include_pending runtime leaks ordered inputs horizon
        scheduler control (initialEq ▸ trace) focal memories frontier profile consistent
        supported id
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at moved
      subst after
      exact ⟨final, settled.congr_execution runtime leaks _ _ focal memories final
        rfl rfl rfl⟩
  | application command =>
      cases command with
      | advanceClock =>
          exact ⟨frontier, related.advanceClock runtime leaks control.execution after focal
            memories frontier moved⟩
      | executeSample event =>
          exact related.sample_command_frontier_exists runtime leaks profile control.execution
            focal memories frontier consistent supported event after moved
      | expire event =>
          have faithful := runtime.reactiveEmission_history leaks (serviceInitialLaw setup mode)
            horizon scheduler control trace
          exact source_unilateral_expiry_frontier setup leaks horizon scheduler delay bound
            opportunity timely inclusion ordered control trace idle valid focal conformance
            profile memories consistent (fun owner => (faithful owner).1)
            (fun owner => (faithful owner).2) supported frontier related event after moved

end Vegas
