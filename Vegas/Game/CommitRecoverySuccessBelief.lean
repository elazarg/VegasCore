/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoverySuccessProbability

/-! # Successful first-close payoffs under the actual source belief

The joint retains the original information history, its actual first-close
boundary and its complete later terminal history. Conditioning that joint
keeps the success-induced tilt of the original source belief explicitly.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

variable
  (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
  (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
  (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
    PMF (setup.CommitRecoveryValueChoice who info))

local notation "baseline" => setup.commitRecoveryNormalizedTrembledProfile omission
  omissionNonnegative omissionBounded bad badNonnegative badBounded values

open Classical in
/-- The original source belief, not a no-miss representative belief, has
near-unit successful-window mass and a uniformly close success-conditioned
continuation value. The conditioned law retains all three actual histories. -/
theorem commitRecovery_normalized_success_belief_value_error
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (prescribed : ∀ who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        baseline who (setup.commitRecoveryModel.infoOf who history.trace))
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (regular : ∀ history : setup.commitRecoveryModel.InformationHistory focal site.1,
      ∃ first, history.1.state = some first ∧
        ProtocolState.atCommit setup.program first.point = true ∧
        first.excluded = first.entryExcluded ∧
        ProtocolState.BindingsHoldValues focal setup.program first.point)
    (law : PMF (setup.CommitRecoveryValueChoice focal site.1))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ history,
      |setup.commitRecoveryPayoff utility excludedPayoff focal history| ≤ bound) :
    let certificate := setup.commitRecoveryProtocol_bounded.wellFoundedHistories
    let altered := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
      baseline focal ((baseline focal).withLaw site.1 (law.map Subtype.val))
    let stop := fun (origin final : setup.commitRecoveryProtocol.History) =>
      final.state.map (fun point => point.publicAddress.2.2) ≠
        origin.state.map (fun point => point.publicAddress.2.2)
    let joint := (assessment.belief focal site).bind fun origin =>
      (bindPairLaw (setup.commitRecoveryModel.runBehavioralUntil certificate altered
        (stop origin.1) origin.1)
          (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate baseline)).map
            (fun pair => (origin.1, pair))
    let observed := fun triple : setup.commitRecoveryProtocol.History ×
      (setup.commitRecoveryProtocol.History × setup.commitRecoveryProtocol.History) =>
        decide (triple.1.state.elim False (fun first =>
          triple.2.1.state.elim False (fun last => last.excluded = first.entryExcluded ∧
            ProtocolState.BindingsHoldValues focal setup.program last.eraseHistory.point)))
    let loss := (Fintype.card Player * instructionCount setup.program : Nat) * (omission + bad)
    1 - ((joint.map observed) true).toReal ≤ loss ∧
      |expect (fiberPosterior joint observed true)
          (fun triple => setup.commitRecoveryPayoff utility excludedPayoff focal triple.2.2) -
        (assessment.continuationContext certificate site
          (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
            ((assessment.strategy focal).withLaw site.1 (law.map Subtype.val))| ≤
        loss * (2 * bound) := by
  classical
  intro certificate altered stop joint observed loss
  let payoff := setup.commitRecoveryPayoff utility excludedPayoff focal
  let branch := fun origin : setup.commitRecoveryModel.InformationHistory focal site.1 =>
    (bindPairLaw (setup.commitRecoveryModel.runBehavioralUntil certificate altered
      (stop origin.1) origin.1)
        (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate baseline)).map
          (fun pair => (origin.1, pair))
  have pointwise (origin : setup.commitRecoveryModel.InformationHistory focal site.1) :
      1 - (((branch origin).map observed) true).toReal ≤ loss ∧
      (branch origin).map (fun triple => triple.2.2) =
        setup.commitRecoveryModel.runBehavioralTerminalFrom certificate altered origin.1 := by
    have active := InformationModel.InformationSite.active
      (M := setup.commitRecoveryModel) site origin
    obtain ⟨first, state, committing, ordinary, valued⟩ := regular origin
    rcases origin with ⟨⟨state', trace⟩, atSite⟩
    dsimp only at state atSite
    subst state'
    have survives : focal ∉ first.excluded := active.2
    have ending : ProtocolState.commitEnd setup.program first.point =
        ProtocolState.commitEnd setup.program first.saved := by
      rcases setup.commitRecovery_blockFrontier trace with ⟨_saved, _live, ending⟩ | same
      · exact ending
      · rw [same]
    let fuel := ProtocolState.remaining setup.program first.point -
      ProtocolState.commitEnd setup.program first.saved
    have inside := ProtocolState.commitEnd_lt_remaining setup.program first.point committing
    have distance : fuel + ProtocolState.commitEnd setup.program first.saved =
        ProtocolState.remaining setup.program first.point := by dsimp only [fuel]; omega
    have run := setup.commitRecovery_run_until_attempt_exit altered fuel first trace committing
      distance
    have atInfo (info : setup.commitRecoveryModel.InfoState focal)
        (here : setup.commitRecoveryModel.infoOf focal trace = info)
        (currentLaw : PMF (setup.CommitRecoveryValueChoice focal info)) :
        let changed := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
          baseline focal ((baseline focal).withLaw info (currentLaw.map Subtype.val))
        let success := {history : setup.commitRecoveryProtocol.History |
          history.state.elim False (fun last => last.excluded = first.entryExcluded ∧
            ProtocolState.BindingsHoldValues focal setup.program last.eraseHistory.point)}
        1 - ((setup.commitRecoveryModel.runBehavioralFrom changed fuel
          ⟨some first, trace⟩).toOuterMeasure success).toReal ≤ loss ∧
          setup.commitRecoveryModel.runBehavioralTerminalFrom certificate changed
              ⟨some first, trace⟩ =
            (setup.commitRecoveryModel.runBehavioralFrom changed fuel ⟨some first, trace⟩).bind
              (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate baseline) := by
      subst info
      exact ⟨setup.commitRecoveryNormalizedTrembledProfile_success_mass_loss omission
          omissionNonnegative omissionBounded bad badNonnegative badBounded values focal first
          trace committing ordinary survives valued currentLaw fuel distance,
        setup.commitRecoveryNormalizedTrembledProfile_local_terminal_window omission
          omissionNonnegative omissionBounded bad badNonnegative badBounded values certificate
          focal first trace committing fuel distance (currentLaw.map Subtype.val)⟩
    obtain ⟨localLoss, split⟩ := atInfo site.1 atSite law
    have atom : (((branch ⟨⟨some first, trace⟩, atSite⟩).map observed) true).toReal =
        ((setup.commitRecoveryModel.runBehavioralFrom altered fuel
          ⟨some first, trace⟩).toOuterMeasure {history |
            history.state.elim False (fun last => last.excluded = first.entryExcluded ∧
              ProtocolState.BindingsHoldValues focal setup.program
                last.eraseHistory.point)}).toReal := by
      rw [PMF.map_comp]
      change (((bindPairLaw _ _).map (fun pair : setup.commitRecoveryProtocol.History ×
        setup.commitRecoveryProtocol.History => decide (pair.1.state.elim False
        (fun last => last.excluded = first.entryExcluded ∧
          ProtocolState.BindingsHoldValues focal setup.program last.eraseHistory.point))))
            true).toReal = _
      rw [show setup.commitRecoveryModel.runBehavioralUntil certificate altered
        (stop ⟨some first, trace⟩) ⟨some first, trace⟩ =
          setup.commitRecoveryModel.runBehavioralFrom altered fuel ⟨some first, trace⟩ from run]
      let window := setup.commitRecoveryModel.runBehavioralFrom altered fuel ⟨some first, trace⟩
      let finish := setup.commitRecoveryModel.runBehavioralTerminalFrom certificate baseline
      let success := {history : setup.commitRecoveryProtocol.History |
        history.state.elim False (fun last => last.excluded = first.entryExcluded ∧
          ProtocolState.BindingsHoldValues focal setup.program last.eraseHistory.point)}
      calc
        _ = ((bindPairLaw window finish).toOuterMeasure (Prod.fst ⁻¹' success)).toReal := by
          congr 1
          rw [PMF.map_apply, PMF.toOuterMeasure_apply]
          apply tsum_congr
          intro pair
          simp [success, Set.indicator, window, finish]
        _ = (((bindPairLaw window finish).map Prod.fst).toOuterMeasure success).toReal := by
          rw [PMF.toOuterMeasure_map_apply]
        _ = _ := by rw [bindPairLaw_map_fst]
    refine ⟨by rw [atom]; exact localLoss, ?_⟩
    simp only [branch, PMF.map_comp, Function.comp_def]
    rw [bindPairLaw_map_snd]
    rw [show setup.commitRecoveryModel.runBehavioralUntil certificate altered
      (stop ⟨some first, trace⟩) ⟨some first, trace⟩ =
        setup.commitRecoveryModel.runBehavioralFrom altered fuel ⟨some first, trace⟩ from run]
    exact split.symm
  have mass : ((joint.map observed) true).toReal =
      expect (assessment.belief focal site) (fun origin =>
        (((branch origin).map observed) true).toReal) := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      toReal_toOuterMeasure_bind]
    apply expect_congr_on_support
    intro origin _supported
    rw [← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]
  have integrable := payoffIntegrable_of_bounded (assessment.belief focal site)
    (fun origin => (((branch origin).map observed) true).toReal) (C := 1)
    (fun origin => by rw [abs_of_nonneg ENNReal.toReal_nonneg]; exact pmf_toReal_apply_le_one _ _)
  have missing : 1 - ((joint.map observed) true).toReal ≤ loss := by
    rw [mass, ← expect_constant (assessment.belief focal site) 1,
      ← expect_sub (payoffIntegrable_constant _ _) integrable]
    exact expect_le_const _ _ (payoffIntegrable_sub (payoffIntegrable_constant _ _) integrable)
      loss (fun origin _supported => (pointwise origin).1)
  refine ⟨missing, ?_⟩
  have close := PMF.WithinTV.of_bind_point (joint.map observed) true
    (fiberPosterior joint observed) (le_refl (1 - ((joint.map observed) true).toReal))
  rw [fiberPosterior_reconstruct] at close
  have interval (triple : setup.commitRecoveryProtocol.History ×
      (setup.commitRecoveryProtocol.History × setup.commitRecoveryProtocol.History)) :
      -bound ≤ payoff triple.2.2 ∧ payoff triple.2.2 ≤ -bound + 2 * bound := by
    have limits := abs_le.mp (bounded triple.2.2)
    exact ⟨limits.1, by linarith [limits.2]⟩
  have forwards := close.expect_sub_le (fun triple => payoff triple.2.2) (-bound) (2 * bound)
    (fun triple _ => interval triple)
  have backwards := close.symm.expect_sub_le (fun triple => payoff triple.2.2) (-bound) (2 * bound)
    (fun triple _ => interval triple)
  have terminalLaw : joint.map (fun triple => triple.2.2) =
      (assessment.belief focal site).bind (fun origin =>
        setup.commitRecoveryModel.runBehavioralTerminalFrom certificate altered origin.1) := by
    rw [PMF.map_bind]
    apply bind_congr_on_support
    intro origin _supported
    exact (pointwise origin).2
  have terminalValue : expect joint (fun triple => payoff triple.2.2) =
      (assessment.continuationContext certificate site payoff).value
        ((assessment.strategy focal).withLaw site.1 (law.map Subtype.val)) := by
    rw [InformationModel.BehavioralAssessment.continuationContext_value]
    have same : (assessment.belief focal site).bind (fun origin =>
        setup.commitRecoveryModel.runBehavioralTerminalFrom certificate altered origin.1) =
        (assessment.belief focal site).bind (fun origin =>
          setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
            (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
              assessment.strategy focal ((assessment.strategy focal).withLaw site.1
                (law.map Subtype.val))) origin.1) := by
      apply bind_congr_on_support
      intro origin _supported
      exact (setup.commitRecoveryNormalizedTrembledProfile_local_terminal_of_prescribed omission
        omissionNonnegative omissionBounded bad badNonnegative badBounded values assessment
        prescribed certificate focal site.1 (law.map Subtype.val) origin.1).symm
    calc
      _ = expect (joint.map (fun triple => triple.2.2)) payoff := (expect_map _ _ _).symm
      _ = _ := by rw [terminalLaw, same]
  rw [terminalValue] at forwards backwards
  have scaled := mul_le_mul_of_nonneg_right missing (by positivity : 0 ≤ 2 * bound)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Vegas.SourceProgram.Setup
