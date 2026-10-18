/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastEarlyContinuation
import Vegas.Examples.CommitSeedBroadcastPreparationLoss
import Vegas.Examples.CommitSeedBroadcastCurrentChoiceValue

/-! # Exact native loss of an unusable initial declaration -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- An unusable permitted initial packet has the fixed exclusion value under
unchanged assessed future play, at every genuine counted initial input. -/
theorem counted_unusable_early_assessed_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 0)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner))
    (unusable : (material.call.opening.bind fun raw => raw.as? .bool) = none) :
    expect (app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (some ⟨remaining, none, execution.respond app owner ⟨some material⟩⟩))
        (fun state => netPayoff state owner) = -(3 / 2) := by
  classical
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon scheduler remaining execution
    owner ⟨some material⟩ trace offered
  let next := execution.respond app owner ⟨some material⟩
  let history : countedProtocol.History := ⟨some ⟨remaining, none, next⟩, responded⟩
  have law := counted_assessment_finish_eq assessment equilibrium history
  change app.finish initial horizon scheduler
    (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
      history.state = _ at law
  rw [← law]
  let players := countedMenu.decodeProfile initial horizon scheduler
    (countedAssessmentProfile assessment)
  have covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view := fun who past view action supported =>
    countedMenu.decode_embedPolicy_covered initial horizon scheduler who
      (countedAssessmentProfile assessment who) past view action supported
  have bounded (state : app.ProtocolState) : |netPayoff state owner| ≤ (9 / 2 : ℝ) := by
    have range := netPayoff_mem_Icc state owner
    exact abs_le.mpr ⟨range.1, by linarith [range.2]⟩
  change expect (app.finish initial horizon scheduler players
    (some ⟨remaining, none, next⟩)) (fun state => netPayoff state owner) = _
  rw [native_finish_original_seed_law, expect_bind_tower_bounded _ _ _ bounded,
    ← expect_constant (implementation.posterior next.environmentRecall) (-(3 / 2) : ℝ)]
  apply expect_congr_on_support
  intro seed supported
  have originalSupported : seed ∈ (implementation.posterior execution.environmentRecall).support :=
    supported
  obtain ⟨priorSeed, ⟨fixed⟩⟩ := menu_original_posterior_trace countedMenu
    ⟨remaining, some owner, execution⟩ trace seed originalSupported
  rw [← expect_constant (app.finish initial horizon (family seed) players
    (some ⟨remaining, none, next⟩)) (-(3 / 2) : ℝ)]
  apply expect_congr_on_support
  intro state reached
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind] at reached
  obtain ⟨after, continued, rfl⟩ := PMF.support_map .. ▸ reached
  have admitted := early_response_original_admissions assessment equilibrium seed priorSeed
    remaining execution owner fixed request clock material offered players covered
      (fun _ _ => rfl) after continued
  exact current_unusable_binding_all_admissions_payoff seed remaining execution owner fixed request
    material offered unusable players covered after continued admitted

end Vegas.Examples.CommitSeedBroadcast
