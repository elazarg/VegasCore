/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperAssessedOriginalStop
import Vegas.Examples.CommitSeedBroadcastHelperOriginalObservation

/-! # The actual incumbent original helper observation law -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

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
