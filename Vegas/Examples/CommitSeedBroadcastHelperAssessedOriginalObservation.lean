/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperAssessedOriginalStop
import Vegas.Examples.CommitSeedBroadcastHelperOriginalObservation

/-! # The actual incumbent original helper observation law -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

open Classical in
/-- Stopping the existing evaluator at original retirement changes no
original observation. Later publication effects are not equated. -/
theorem original_observation_rounds_stopped (selected : app.Scheduler)
    (players : Player → app.Policy) (hidden : Player) (count remaining : Nat)
    (execution : app.Execution)
    (trace : (app.protocol initial horizon selected).Trace
      (some ⟨remaining + count, none, execution⟩)) :
    (app.runRounds selected players count execution).map (originalHelperObservation hidden) =
      (app.runUntil selected players (fun current => current.application.attempt ≠ originalAttempt)
        count execution).map (originalHelperObservation hidden) := by
  classical
  let stop := fun current : app.Execution => current.application.attempt ≠ originalAttempt
  let deadline := execution.environmentRecall.length + count
  have length : deadline - execution.environmentRecall.length = count := by
    dsimp only [deadline]
    omega
  have rounds : app.runToHorizon selected players deadline execution =
      app.runRounds selected players count execution := by
    rw [ReactiveApplication.runToHorizon, length]
  have stopped : app.runUntilHorizon selected players stop deadline execution =
      app.runUntil selected players stop count execution := by
    rw [ReactiveApplication.runUntilHorizon, length]
  have decomposition := app.runToHorizon_eq_runUntilHorizon_bind selected players stop
    deadline execution
  rw [rounds, stopped] at decomposition
  rw [decomposition, PMF.map_bind]
  change ((app.runUntil selected players stop count execution).bind fun current =>
    (app.runToHorizon selected players deadline current).map (originalHelperObservation hidden)) =
      (app.runUntil selected players stop count execution).map (originalHelperObservation hidden)
  conv_rhs => rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support
  intro current reached
  obtain retired | last :=
    app.runUntil_stopped selected players stop count execution current reached
  · obtain ⟨used, within, actual, _position⟩ :=
      app.runUntil_runRounds selected players stop count execution current reached
    have fuel : (remaining + (count - used)) + used = remaining + count := by omega
    have earlier : (app.protocol initial horizon selected).Trace
        (some ⟨(remaining + (count - used)) + used, none, execution⟩) := by
      rw [fuel]
      exact trace
    obtain ⟨currentTrace⟩ := app.raw_trace_runRounds initial horizon selected players
      (remaining + (count - used)) used execution current earlier actual
    change current.application.attempt ≠ originalAttempt at retired
    change (app.runRounds selected players (deadline - current.environmentRecall.length)
      current).map (originalHelperObservation hidden) = _
    rw [retired_helper_observation_run selected
      ⟨remaining + (count - used), none, current⟩ currentTrace retired players
        (deadline - current.environmentRecall.length) hidden]
    simp only [Function.comp_def, originalHelperObservation, retired, ite_false]
  · change current.environmentRecall.length = deadline at last
    rw [ReactiveApplication.runToHorizon, last, Nat.sub_self,
      ReactiveApplication.runRounds, PMF.pure_map]
    rfl

/-- From a genuine original counted prefix with its helper packet already
retained, the unchanged raw equilibrium continuation has exactly the same
original observation law as silencing that helper. This concerns the actual
native round evaluator and assumes neither a proper foreign policy nor a
posterior equation. -/
theorem assessed_sent_helper_original_observation_law
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (hidden : Player) (count remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining + count, none, execution⟩))
    (sent : ∃ message ∈ app.outputs (execution.recall hidden),
      PhaseCount.event? message.payload = some (originalCoordinate hidden)) :
    (app.runRounds scheduler (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      count execution).map (originalHelperObservation hidden) =
    (app.runRounds scheduler
      (Function.update (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        hidden (fun _ _ => PMF.pure ⟨none⟩)) count execution).map
      (originalHelperObservation hidden) := by
  rw [original_observation_rounds_stopped scheduler _ hidden count remaining execution
      (countedMenu.toRawTrace initial horizon scheduler trace),
    original_observation_rounds_stopped scheduler _ hidden count remaining execution
      (countedMenu.toRawTrace initial horizon scheduler trace),
    assessed_sent_helper_original_stopped_law assessment equilibrium hidden count remaining
      execution trace sent]

end Vegas.Examples.CommitSeedBroadcast
