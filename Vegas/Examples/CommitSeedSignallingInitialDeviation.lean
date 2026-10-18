/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingQuietPayoff

/-! # The initial profitable deviation after the other owner withholds its signal -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- If Bob initially waits after Alice waits, Alice's fixed proper late
continuation has strictly positive value at her actual initial information set.
Every later Bob decision uses the original assessed raw strategy. -/
theorem aliceFirst_fixedLate_context_quarter_of_bobQuiet_wait
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (bobWait : countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment) bob [] ((bobFirst ⟨none⟩).observe app bob) =
        PMF.pure ⟨none⟩) :
    (1 / 4 : ℝ) ≤ (assessment.continuationContext canonicalCertificate aliceFirstSite
      (rawPayoff alice)).value (fixedLateContinuation alice) := by
  let profile := Function.update (countedAssessmentProfile assessment) alice
    (countedMenu.restrictPolicy initial horizon scheduler alice (fixedLatePolicy alice))
  let players := countedMenu.decodeProfile initial horizon scheduler profile
  have selected : players alice = fixedLatePolicy alice := by
    change app.decodePolicy (countedMenu.embedPolicy initial horizon scheduler alice
      ((Function.update (countedAssessmentProfile assessment) alice
        (countedMenu.restrictPolicy initial horizon scheduler alice (fixedLatePolicy alice)))
          alice)) = _
    rw [Function.update_self]
    exact countedMenu.decode_restrictPolicy_of_covered initial horizon scheduler alice _
      (fixedLatePolicy_counted alice)
  have aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩ := by
    rw [selected]
    simpa only [aliceFirst_recall] using fixedLatePolicy_aliceFirst
  have bobWait' : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩ := by
    change app.decodePolicy (countedMenu.embedPolicy initial horizon scheduler bob
      (profile bob)) [] _ = _
    have other : bob ≠ alice := by decide
    dsimp only [profile]
    rw [Function.update_of_ne other]
    exact bobWait
  have positive := initialized_fixed_late_netPayoff_quarter profile alice selected
    aliceWait bobWait'
  have value := aliceFirst_context_value_eq_finish assessment (fixedLateContinuation alice)
  rw [rawMenu.decodeProfile_update, decode_fixedLateContinuation,
    ← finish_initial_eq_aliceFirst] at value
  simp only [ReactiveApplication.finish, initial_eq_pure, PMF.pure_bind, expect_map] at value
  change _ = expect (app.runRounds scheduler
    (Function.update (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) alice
      (fixedLatePolicy alice)) horizon initialExecution)
        (fun final => netPayoff (app.finished final) alice) at value
  have law := raw_equilibrium_initialized_counted_run assessment equilibrium alice
    (fixedLatePolicy alice) (fixedLatePolicy_counted alice)
  rw [← law] at value
  rw [value]
  exact positive

/-- No preserving sequential equilibrium can have Bob withhold his initial
packet after Alice waits. The remaining information-signalling argument must
establish that withholding is forced in every candidate preserving assessment. -/
theorem preserving_equilibrium_bobQuiet_not_wait
    (source : ∀ who, OnePacketCommitRevealHypotheses.setup.intendedModel.BehavioralPolicy who)
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (preserves : sourceJointLaw source = nativeJointLaw assessment.strategy) :
    countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment)
      bob [] ((bobFirst ⟨none⟩).observe app bob) ≠ PMF.pure ⟨none⟩ := by
  intro waits
  have positive := aliceFirst_fixedLate_context_quarter_of_bobQuiet_wait assessment equilibrium
    waits
  have zero := preservation_implies_aliceFirst_zero source assessment preserves
  have integrable (alternative : rawModel.BehavioralPolicy alice) :=
    assessment.continuationContext_integrable_of_bounded_terminal canonicalCertificate
      aliceFirstSite (rawPayoff alice) 6 (fun final _ => rawPayoff_abs_le alice final) alternative
  have compare := (Context.isLocallyOptimal_iff_of_integrable
    (integrable (assessment.strategy alice)) (fun alternative _ => integrable alternative)).mp
    (equilibrium.1 alice aliceFirstSite)
  have upper := compare (fixedLateContinuation alice) (Set.mem_univ _)
  linarith

end Vegas.Examples.CommitSeedSignalling
