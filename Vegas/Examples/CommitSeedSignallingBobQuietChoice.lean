/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperIncentives
import Vegas.Examples.CommitSeedSignallingQuietPayoff
import Interaction.ReactiveRawRoundTrace

/-! # Withholding the initial helper is forced by sequential rationality -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob)

open Classical in
/-- Every admitted initial Bob transmission has nonpositive committed value
under the unchanged assessed continuation. Its hidden preparation is arbitrary. -/
theorem bobQuiet_counted_transmission_context_nonpositive
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (material : app.Submission)
    (allowed : (⟨some material⟩ : app.Action) ∈ countedMenu.actions bob []
      ((bobFirst ⟨none⟩).observe app bob))
    (choice : rawModel.Choice bob bobQuietSite.1)
    (selected : choice.1 = some ⟨some material⟩) :
    (assessment.continuationContext canonicalCertificate bobQuietSite
      (rawPayoff bob)).value ((assessment.strategy bob).commit bobQuietSite.1 choice) ≤ 0 := by
  classical
  rw [bobQuiet_context_committed_value assessment choice ⟨some material⟩ selected]
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind, expect_map]
  let players := rawMenu.decodeProfile initial horizon scheduler assessment.strategy
  let start := (bobFirst ⟨none⟩).respond app bob ⟨some material⟩
  let law := app.runRounds scheduler players 62 start
  change expect law (fun final => netPayoff (app.finished final) bob) ≤ 0
  have upper (final : app.Execution) (reached : final ∈ law.support) :
      netPayoff (app.finished final) bob ≤ 0 := by
    have survives := bobQuiet_counted_transmission_alice_survives assessment equilibrium material
      allowed final reached
    obtain ⟨before⟩ := bobFirst_quiet_trace
    obtain ⟨responded⟩ := app.raw_trace_respond initial horizon scheduler 62 (bobFirst ⟨none⟩) bob
      ⟨some material⟩ (rawMenu.toRawTrace initial horizon scheduler before)
    obtain ⟨after⟩ := app.raw_trace_runRounds initial horizon scheduler players 0 62 start final
      responded reached
    have complete := scheduler_completesPlay ⟨0, none, final⟩ after ⟨rfl, rfl⟩
    have opponentEq : opponent bob = alice := by decide
    exact netPayoff_le_zero_of_opponent_survives scheduler ⟨0, none, final⟩ after complete bob
      (by simpa only [opponentEq] using survives)
  have integrable : PayoffIntegrable law (fun final => netPayoff (app.finished final) bob) := by
    apply payoffIntegrable_of_bounded law _ (C := 6)
    intro final
    have bounds := netPayoff_mem_Icc (app.finished final) bob
    exact abs_le.mpr ⟨bounds.1, bounds.2.trans (by norm_num)⟩
  have bounded := expect_mono upper integrable (payoffIntegrable_constant law 0)
  simpa only [expect_constant] using bounded

/-- Every supported current choice is literal WAIT. Its optimal committed
value must dominate the positive whole proper-late deviation. -/
theorem bobQuiet_supported_choice_wait
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (choice : rawModel.Choice bob bobQuietSite.1)
    (supported : choice ∈ (assessment.strategy bob bobQuietSite.1).support) :
    choice.1 = some ⟨none⟩ := by
  classical
  obtain ⟨response, _available, selected⟩ := choice.2
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact selected
  | some material =>
      have allowed := bobQuiet_supported_response_counted assessment equilibrium choice supported
        ⟨some material⟩ selected
      rw [bobFirst_recall] at allowed
      have upper := bobQuiet_counted_transmission_context_nonpositive assessment equilibrium
        material allowed choice selected
      have factor := rawModel.runnerFactorsAt_terminal canonicalCertificate
        (rawMenu.decisionRecall initial horizon scheduler).actsOnceWhereItMatters
        (rawMenu.informationSite_allNonterminal initial horizon scheduler bob bobQuietSite)
      have integrable (policy : rawModel.BehavioralPolicy bob) :=
        assessment.continuationContext_integrable_of_bounded_terminal canonicalCertificate
          bobQuietSite (rawPayoff bob) 6 (fun final _ => rawPayoff_abs_le bob final) policy
      have better := assessment.supported_choice_optimal
        (rawModel.runBehavioralTerminalFrom canonicalCertificate) bobQuietSite factor
        (rawPayoff bob) (equilibrium.1 bob bobQuietSite) (integrable (assessment.strategy bob))
        choice supported (fixedLateContinuation bob) (integrable (fixedLateContinuation bob))
      change (assessment.continuationContext canonicalCertificate bobQuietSite
        (rawPayoff bob)).value (fixedLateContinuation bob) ≤
          (assessment.continuationContext canonicalCertificate bobQuietSite
            (rawPayoff bob)).value ((assessment.strategy bob).commit bobQuietSite.1 choice)
        at better
      have lower := bobQuiet_fixedLate_context_quarter assessment equilibrium
      linarith

/-- The actual decoded assessed law withholds Bob's first helper packet,
including when Alice's earlier WAIT has zero assessed probability. -/
theorem bobQuiet_raw_decoded_wait
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff) :
    rawMenu.decodeProfile initial horizon scheduler assessment.strategy bob []
      ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩ := by
  classical
  simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
    ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp, Function.comp_def,
    ReactiveApplication.ResponseMenu.rawChoice]
  change ((assessment.strategy bob bobQuietSite.1).map
    (fun choice => choice.1.getD ⟨none⟩)) = PMF.pure ⟨none⟩
  apply pmf_eq_pure_of_support_subset_singleton
  intro response supported
  obtain ⟨choice, positive, same⟩ := PMF.support_map .. ▸ supported
  have selected := bobQuiet_supported_choice_wait assessment equilibrium choice positive
  have actual : response = (⟨none⟩ : app.Action) := by
    simpa only [selected, Option.getD_some] using same.symm
  exact actual

/-- The retained counted profile has the same forced quiet response, so the
initial proper-late deviation applies without an added strategy assumption. -/
theorem bobQuiet_counted_decoded_wait
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff) :
    countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment)
      bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩ := by
  classical
  let players := rawMenu.decodeProfile initial horizon scheduler assessment.strategy
  have quiet : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩ :=
    bobQuiet_raw_decoded_wait assessment equilibrium
  have covered (response : app.Action)
      (supported : response ∈ (players bob [] ((bobFirst ⟨none⟩).observe app bob)).support) :
      response ∈ countedMenu.actions bob [] ((bobFirst ⟨none⟩).observe app bob) := by
    rw [quiet, PMF.mem_support_pure_iff] at supported
    subst response
    exact PhaseCount.silence_onePacket runtime leaks bounds bob [] _
  have encoded := countedMenu.embed_restrictPolicy initial horizon scheduler bob (players bob) []
    ((bobFirst ⟨none⟩).observe app bob) covered
  change ((countedMenu.embedPolicy initial horizon scheduler bob
    (countedMenu.restrictPolicy initial horizon scheduler bob (players bob)))
      (some ([], (bobFirst ⟨none⟩).observe app bob))).map
        (fun selected => selected.1.getD ⟨none⟩) = PMF.pure ⟨none⟩
  rw [encoded]
  simp only [ReactiveApplication.encodePolicy, PMF.map_comp, Function.comp_def,
    Option.getD_some]
  change (players bob [] ((bobFirst ⟨none⟩).observe app bob)).map id = PMF.pure ⟨none⟩
  rw [PMF.map_id]
  exact quiet

end Vegas.Examples.CommitSeedSignalling
