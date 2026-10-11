/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceUnilateralEnvironment
import Vegas.Pending.ReactiveUnilateralCallback
import Interaction.ReactiveRawRoundTrace

/-! # Actual unilateral source-service round support -/

noncomputable section
namespace Vegas
open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- One actual scheduler round reconstructs a mixed reachable frontier for
all genuine foreign posterior memories under operational source service. -/
theorem source_unilateral_round_frontier
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (ordered : (serviceGraph setup mode).RevealRelaxedOrdered)
      (profile : (serviceGraph setup mode).BehavioralProfile)
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (opportunity : (serviceRuntime setup mode deadline).Opportunity leaks
      (serviceInitialLaw setup mode) horizon scheduler delay)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (focal : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (remaining : Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (valid : execution.application.BindingInvariant)
    (conformance : ∀ owner, owner ≠ focal →
      (serviceRuntime setup mode deadline).RecordedTimelyCalls leaks owner execution)
    (consistent : ∀ owner, owner ≠ focal →
      ((serviceRuntime setup mode deadline).prescribedReactivePolicy
      leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (frontiers : ∀ memories : Player → List (Option (serviceGraph setup mode).Completion),
      memories focal = [] →
      (∀ owner, owner ≠ focal → memories owner ∈
        (((serviceRuntime setup mode deadline).prescribedReactiveImplementation
          leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
        ∃ frontier, (serviceRuntime setup mode deadline).ReactiveUnilateralFrontier
          leaks focal execution memories frontier)
    (next : (serviceApplication setup mode deadline leaks).Execution)
    (reached : next ∈ ((serviceApplication setup mode deadline leaks).round scheduler
      (Function.update (fun owner =>
        (serviceRuntime setup mode deadline).prescribedReactivePolicy leaks owner (profile owner))
        focal deviation)
        execution).support)
    (memories : Player → List (Option (serviceGraph setup mode).Completion))
    (empty : memories focal = [])
    (supported : ∀ owner, owner ≠ focal → memories owner ∈
      (((serviceRuntime setup mode deadline).prescribedReactiveImplementation
        leaks owner (profile owner)).posterior
        (next.recall owner)).support) :
    ∃ frontier, (serviceRuntime setup mode deadline).ReactiveUnilateralFrontier
      leaks focal next memories frontier := by
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  let players := Function.update
    (fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)) focal deviation
  change next ∈ (app.round scheduler players execution).support at reached
  rw [ReactiveApplication.round, PMF.support_bind] at reached
  obtain ⟨command, chosen, dispatched⟩ := Set.mem_iUnion₂.mp reached
  rw [ReactiveApplication.dispatch, PMF.support_bind] at dispatched
  obtain ⟨current, moved, resumed⟩ := Set.mem_iUnion₂.mp dispatched
  have recallEq := app.environmentStep_recall execution current command moved
  have currentConsistent : ∀ owner, owner ≠ focal →
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (current.recall owner) := by
    simpa only [recallEq] using consistent
  have currentFrontiers : ∀ saved : Player → List (Option (serviceGraph setup mode).Completion),
      saved focal = [] →
      (∀ owner, owner ≠ focal → saved owner ∈
        (((serviceRuntime setup mode deadline).prescribedReactiveImplementation
          leaks owner (profile owner)).posterior
          (current.recall owner)).support) →
        ∃ frontier, (serviceRuntime setup mode deadline).ReactiveUnilateralFrontier
          leaks focal current saved frontier := by
    intro saved savedEmpty retained
    have prior : ∀ owner, owner ≠ focal → saved owner ∈
        (((serviceRuntime setup mode deadline).prescribedReactiveImplementation
          leaks owner (profile owner)).posterior
          (execution.recall owner)).support := by simpa only [recallEq] using retained
    obtain ⟨frontier, related⟩ := frontiers saved savedEmpty prior
    exact source_unilateral_environment_frontier setup leaks horizon scheduler delay bound
      opportunity timely inclusion ordered ⟨remaining + 1, none, execution⟩ trace rfl
      valid focal conformance profile saved consistent prior frontier related command current moved
  cases actorEq : command.actor? app with
  | none =>
      simp only [ReactiveApplication.resume, actorEq, PMF.mem_support_pure_iff] at resumed
      subst next
      exact currentFrontiers memories empty supported
  | some who =>
      simp only [ReactiveApplication.resume, actorEq, ReactiveApplication.invoke, PMF.support_map,
        Set.mem_image] at resumed
      obtain ⟨action, positive, rfl⟩ := resumed
      obtain ⟨currentTrace⟩ :=
        app.raw_trace_environment (serviceInitialLaw setup mode) horizon scheduler
        remaining execution current command trace chosen moved
      obtain ⟨quiet, sent⟩ := runtime.reactiveEmission_history leaks
        (serviceInitialLaw setup mode) horizon scheduler ⟨remaining, some who, current⟩
          (by simpa only [actorEq] using currentTrace) who
      have chosenForeign : who ≠ focal → action ∈
          (runtime.prescribedReactivePolicy leaks who (profile who)
            (current.recall who) (current.observe app who)).support := by
        intro foreign
        simpa only [players, Function.update_of_ne foreign] using positive
      exact respond_policy_unilateral_frontier_exists runtime leaks profile current focal
        currentConsistent currentFrontiers who quiet sent action chosenForeign
        memories empty supported

end Vegas
