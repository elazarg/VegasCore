/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPreparationKernel

/-! # Preparation improvement under the unchanged original seed posterior -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- The two actual native experiments are compared under the same original
posterior. Their later own draws may differ; every foreign policy is unchanged. -/
theorem counted_unusable_clock_two_finish_gap
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = [])
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner))
    (past : (scheduledProperPolicy 2 owner).Consistent (execution.recall owner))
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner))
    (unusable : (material.call.opening.bind fun raw => raw.as? .bool) = none)
    (tail : app.Policy)
    (tailCovered : ∀ past view action, action ∈ (tail past view).support →
      action ∈ countedMenu.actions owner past view) :
    expect (app.finish initial horizon scheduler
      (Function.update
        (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
        owner tail) (some ⟨remaining, none, execution.respond app owner ⟨some material⟩⟩))
          (fun state => netPayoff state owner) +
      preparationAdvantageValue (some ⟨remaining, some owner, execution⟩) owner ≤
    expect (app.finish initial horizon scheduler
      (Function.update
        (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
        owner (scheduledProperPolicy 2 owner)) (some ⟨remaining, some owner, execution⟩))
          (fun state => netPayoff state owner) := by
  have bounded (state : app.ProtocolState) : |netPayoff state owner| ≤ (9 / 2 : ℝ) := by
    have range := netPayoff_mem_Icc state owner
    exact abs_le.mpr ⟨range.1, by linarith [range.2]⟩
  rw [native_finish_original_seed_law, native_finish_original_seed_law,
    expect_bind_tower_bounded _ _ _ bounded, expect_bind_tower_bounded _ _ _ bounded]
  change expect (implementation.posterior
      (execution.respond app owner ⟨some material⟩).environmentRecall) _ +
    expect (implementation.posterior execution.environmentRecall)
      (fun seed => preparationAdvantageMark seed
        (some ⟨remaining, some owner, execution⟩) owner) ≤ _
  rw [app.respond_environmentRecall]
  rw [← expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
  apply expect_mono ?_ (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  intro seed supported
  obtain ⟨original, ⟨fixed⟩⟩ := menu_original_posterior_trace countedMenu
    ⟨remaining, some owner, execution⟩ trace seed supported
  have upper := unusable_clock_two_preparation_reference_upper assessment equilibrium seed original
    remaining execution owner fixed request clock empty material offered unusable tail tailCovered
  have lower := proper_clock_two_preparation_reference_lower assessment equilibrium seed original
    remaining execution owner fixed request clock empty unsent past
  linarith

end Vegas.Examples.CommitSeedBroadcast
