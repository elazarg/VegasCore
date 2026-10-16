/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryAcceptedFailure
import Vegas.Game.CommitRecoveryCommitSuccess
import GameTheoryExtensions.Analysis.Protocol.SupportedChoiceContinuation

/-! # Original source success mass after a forced domain law

The original normalized source continuation retains a near-unit fraction of
the same prescription with its two failure rates set to zero. At a genuine
ordinary valued-prefix history every supported zero-rate window is successful.
The existing continuation-domination theorem then bounds failure uniformly,
before integrating any original source information belief.
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
local notation "clean" => setup.commitRecoveryNormalizedTrembledProfile 0 le_rfl zero_le_one
  0 le_rfl zero_le_one values

omit [Fintype Player] in
private theorem normalized_zero_raw (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) :
    (clean who info).map Subtype.val =
      (values who (setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who info))).map (fun value => value.val.val) := by
  rw [commitRecoveryNormalizedTrembledProfile, setup.commitRecoveryNoMissErasedProfile_raw]
  simp only [commitRecoveryValueTremble, mix_zero]
  split <;> (simp only [PMF.map_comp, Function.comp_def]; rfl)

omit [Fintype Player] in
/-- The SAME normalized domain law with zero failure rates is retained at
every original source input, including inputs outside the honest embedding. -/
theorem commitRecoveryNormalizedTrembledProfile_domain_lower
    (who : Player) (info : setup.commitRecoveryModel.InfoState who)
    (choice : setup.commitRecoveryModel.Choice who info) :
    ((1 - omission) * (1 - bad)) * ((clean who info) choice).toReal ≤
      ((baseline who info) choice).toReal := by
  classical
  have observed : ((1 - omission) * (1 - bad)) *
      (((clean who info).map Subtype.val) choice.val).toReal ≤
        (((baseline who info).map Subtype.val) choice.val).toReal := by
    rw [setup.normalized_zero_raw values,
      commitRecoveryNormalizedTrembledProfile, setup.commitRecoveryNoMissErasedProfile_raw]
    let query := setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who info)
    let ordinary := ((values who query).map (fun value => value.val.val) choice.val).toReal
    let omitted := (((PMF.pure (setup.commitRecoveryFailureChoice who query true)).map
      Subtype.val) choice.val).toReal
    let failed := (((PMF.pure (setup.commitRecoveryFailureChoice who query false)).map
      Subtype.val) choice.val).toReal
    change ((1 - omission) * (1 - bad)) * ordinary ≤
      (((setup.commitRecoveryValueTremble who query omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded (values who query)).map Subtype.val) choice.val).toReal
    by_cases committing : query.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true
    · simp only [commitRecoveryValueTremble, committing, ↓reduceIte, mix_map, PMF.map_comp,
        Function.comp_def, mix_apply_toReal]
      change ((1 - omission) * (1 - bad)) * ordinary ≤
        omission * omitted + (1 - omission) * (bad * failed + (1 - bad) * ordinary)
      nlinarith [mul_nonneg omissionNonnegative (show 0 ≤ omitted from ENNReal.toReal_nonneg),
        mul_nonneg (sub_nonneg.mpr omissionBounded)
          (mul_nonneg badNonnegative (show 0 ≤ failed from ENNReal.toReal_nonneg))]
    · have notCommit : query.1.1.1.elim false (ProtocolView.atCommit who setup.program) = false :=
        Bool.eq_false_iff.mpr committing
      simp only [commitRecoveryValueTremble, notCommit, Bool.false_eq_true, ↓reduceIte,
        mix_map, PMF.map_comp, Function.comp_def, mix_apply_toReal]
      change ((1 - omission) * (1 - bad)) * ordinary ≤
        omission * omitted + (1 - omission) * ordinary
      have scaled := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (show 0 ≤ ordinary from ENNReal.toReal_nonneg)
          (sub_le_self 1 badNonnegative)) (sub_nonneg.mpr omissionBounded)
      nlinarith [mul_nonneg omissionNonnegative (show 0 ≤ omitted from ENNReal.toReal_nonneg)]
  simpa only [pmf_map_apply_of_injective _ Subtype.val_injective] using observed

omit [Fintype Player] in
private theorem normalized_zero_safe (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (choice : setup.commitRecoveryModel.Choice who info)
    (supported : choice ∈ (clean who info).support) (move : CommitRecoveryMove Player L)
    (selected : choice.val = some move) : move.missing = false ∧ ¬ move.action.IsFailure := by
  have raw : choice.val ∈ ((clean who info).map Subtype.val).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨choice, supported, rfl⟩
  rw [setup.normalized_zero_raw values] at raw
  obtain ⟨value, _offered, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp raw
  exact value.property move (equal.trans selected)

private theorem domain_window_word
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (safe : ∀ (history : setup.commitRecoveryProtocol.History) who choice,
      choice ∈ (profile who (setup.commitRecoveryModel.infoOf who history.trace)).support →
      ∀ move, choice.val = some move → move.missing = false ∧ ¬ move.action.IsFailure)
    (fuel : Nat) (first final : setup.commitRecoveryProtocol.History)
    (supported : final ∈ (setup.commitRecoveryModel.runBehavioralFrom profile fuel first).support) :
    ∃ added, setup.recoveryJointRecall final.trace =
        added ++ setup.recoveryJointRecall first.trace ∧
      ∀ joint ∈ added, ∀ who move, joint who = some move →
        move.missing = false ∧ ¬ move.action.IsFailure := by
  classical
  induction fuel generalizing first with
  | zero =>
      simp only [InformationModel.runBehavioralFrom, runRandomizedFor,
        PMF.mem_support_pure_iff] at supported
      subst final
      exact ⟨[], rfl, fun _ member => (List.not_mem_nil member).elim⟩
  | succ fuel ih =>
      by_cases terminal : setup.commitRecoveryProtocol.terminal first.state
      · rw [setup.commitRecoveryModel.runBehavioralFrom_of_terminal profile fuel.succ terminal,
          PMF.mem_support_pure_iff] at supported
        subst final
        exact ⟨[], rfl, fun _ member => (List.not_mem_nil member).elim⟩
      · rw [setup.commitRecoveryModel.runBehavioralFrom_succ_of_not_terminal profile fuel terminal,
          PMF.mem_support_bind_iff] at supported
        obtain ⟨draw, drawn, continued⟩ := supported
        rw [PMF.mem_support_bindOnSupport_iff] at continued
        obtain ⟨target, realized, child⟩ := continued
        obtain ⟨added, word, safeAdded⟩ := ih (first.extend draw.property realized) child
        let joint : Player → Option (CommitRecoveryMove Player L) := draw.val
        refine ⟨added ++ [joint], ?_, ?_⟩
        · simpa only [History.extend, recoveryJointRecall, joint, List.append_assoc,
            List.singleton_append] using word
        · intro joint member who move selected
          rcases List.mem_append.mp member with kept | current
          · exact safeAdded joint kept who move selected
          · have equal : joint = draw.val := List.mem_singleton.mp current
            subst joint
            have marginal : draw.val ∈ ((setup.commitRecoveryModel.behavioralJoint profile
                first.trace terminal).map Subtype.val).support :=
              (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, drawn, rfl⟩
            rw [setup.commitRecoveryModel.behavioralJoint_map_val,
              independentProduct_support_iff] at marginal
            obtain ⟨choice, chosen, raw⟩ := (PMF.mem_support_map_iff _ _ _).mp (marginal who)
            exact safe first who choice chosen move (raw.trans selected)

open Classical in
/-- The actual first-close success event under a forced current DOMAIN law
has probability at least the retained zero-failure fraction. This is uniform
over genuine ordinary source histories, before any source belief is averaged. -/
theorem commitRecoveryNormalizedTrembledProfile_success_mass_lower
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (ordinary : first.excluded = first.entryExcluded) (active : focal ∉ first.excluded)
    (valued : ProtocolState.BindingsHoldValues focal setup.program first.point)
    (law : PMF (setup.CommitRecoveryValueChoice focal
      (setup.commitRecoveryModel.infoOf focal prior)))
    (fuel : Nat) (distance : fuel + ProtocolState.commitEnd setup.program first.saved =
      ProtocolState.remaining setup.program first.point) :
    let altered := fun profile => Profile.update
      (sig := setup.commitRecoveryModel.behavioralSignature) profile focal
        ((profile focal).withLaw (setup.commitRecoveryModel.infoOf focal prior)
          (law.map Subtype.val))
    let success := {history : setup.commitRecoveryProtocol.History |
      history.state.elim False (fun last => last.excluded = first.entryExcluded ∧
        ProtocolState.BindingsHoldValues focal setup.program last.eraseHistory.point)}
    ((1 - omission) * (1 - bad)) ^ (Fintype.card Player * fuel) ≤
      ((setup.commitRecoveryModel.runBehavioralFrom (altered baseline) fuel
        ⟨some first, prior⟩).toOuterMeasure success).toReal := by
  classical
  intro altered success
  let factor := (1 - omission) * (1 - bad)
  have factorNonnegative : 0 ≤ factor :=
    mul_nonneg (sub_nonneg.mpr omissionBounded) (sub_nonneg.mpr badBounded)
  have factorSmall : factor ≤ 1 :=
    (mul_le_of_le_one_left (sub_nonneg.mpr badBounded)
      (sub_le_self 1 omissionNonnegative)).trans (sub_le_self 1 badNonnegative)
  have lower : ∀ count history,
      history ∈ (setup.commitRecoveryModel.runBehavioralFrom (altered clean) count
        ⟨some first, prior⟩).support → ∀ who choice,
      factor * (((altered clean) who (setup.commitRecoveryModel.infoOf who history.trace))
        choice).toReal ≤
        (((altered baseline) who (setup.commitRecoveryModel.infoOf who history.trace))
          choice).toReal := by
    intro _count history _reached who choice
    by_cases own : who = focal
    · subst who
      simp only [altered, Profile.update_same]
      generalize _information : setup.commitRecoveryModel.infoOf focal history.trace = info
        at choice ⊢
      clear _information
      by_cases here : info = setup.commitRecoveryModel.infoOf focal prior
      · subst info
        rw [InformationModel.BehavioralPolicy.withLaw_self,
          InformationModel.BehavioralPolicy.withLaw_self]
        exact mul_le_of_le_one_left ENNReal.toReal_nonneg factorSmall
      · rw [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ here,
          InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ here]
        exact setup.commitRecoveryNormalizedTrembledProfile_domain_lower omission
          omissionNonnegative omissionBounded bad badNonnegative badBounded values focal _ choice
    · simp only [altered, Profile.update_of_ne _ _ own]
      exact setup.commitRecoveryNormalizedTrembledProfile_domain_lower omission
        omissionNonnegative omissionBounded bad badNonnegative badBounded values who _ choice
  have safe : ∀ (history : setup.commitRecoveryProtocol.History) who choice,
      choice ∈ ((altered clean) who (setup.commitRecoveryModel.infoOf who history.trace)).support →
      ∀ move, choice.val = some move → move.missing = false ∧ ¬ move.action.IsFailure := by
    intro history who choice supported move selected
    by_cases own : who = focal
    · subst who
      simp only [altered, Profile.update_same] at supported
      generalize _information : setup.commitRecoveryModel.infoOf focal history.trace = info
        at choice supported selected ⊢
      clear _information
      by_cases here : info = setup.commitRecoveryModel.infoOf focal prior
      · have raw : choice.val ∈ ((law.map Subtype.val).map Subtype.val).support := by
          subst info
          have member := supported
          rw [InformationModel.BehavioralPolicy.withLaw_self] at member
          exact (PMF.mem_support_map_iff _ _ _).mpr ⟨_, member, rfl⟩
        rw [PMF.map_comp] at raw
        obtain ⟨value, _offered, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp raw
        exact value.property move (equal.trans selected)
      · rw [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ here] at supported
        exact setup.normalized_zero_safe values focal _ choice supported move selected
    · simp only [altered, Profile.update_of_ne _ _ own] at supported
      exact setup.normalized_zero_safe values who _ choice supported move selected
  have sure : ((setup.commitRecoveryModel.runBehavioralFrom (altered clean) fuel
      ⟨some first, prior⟩).toOuterMeasure success).toReal = 1 := by
    rw [ENNReal.toReal_eq_one_iff]
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro final supported
    obtain ⟨added, word, safeAdded⟩ := setup.domain_window_word (altered clean) safe fuel
      ⟨some first, prior⟩ final supported
    let initial := setup.initialConfig setup.initialLaw.support_nonempty.choose
    obtain ⟨_last, _joints, _addresses, _state, _length, _path, consumed, _word, _signals⟩ :=
      setup.commitRecovery_run_commit_window_instructions (altered clean) initial fuel first prior
        committing distance.le final supported
    have addedLength : added.length = fuel := by
      have count := congrArg List.length word
      simp only [List.length_append, setup.recoveryJointRecall_length] at count
      omega
    have newWord : (setup.recoveryJointRecall final.trace).take fuel = added := by
      rw [word, ← addedLength, List.take_left]
    apply (setup.commitRecovery_commit_window_success_iff (altered clean) first prior committing
      fuel distance focal active valued final supported).mp
    refine ⟨ordinary, ?_, ?_⟩
    · intro joint member who
      rw [newWord] at member
      cases chosen : joint who with
      | none => rfl
      | some move => exact (safeAdded joint member who move chosen).1
    · intro joint member move selected
      rw [newWord] at member
      exact (safeAdded joint member focal move selected).2
  have dominated := probOf_domination _ _ (factor ^ (Fintype.card Player * fuel))
    (setup.commitRecoveryModel.runBehavioralFrom_domination_of_supported_choices
      (altered clean) (altered baseline) factor factorNonnegative ⟨some first, prior⟩ lower fuel)
    success
  rw [sure, mul_one] at dominated
  exact dominated

open Classical in
/-- Uniform failure loss for the actual ORIGINAL source window. The bound
depends on the static source horizon, not on the probability of its current
information fiber or on any native future-survival event. -/
theorem commitRecoveryNormalizedTrembledProfile_success_mass_loss
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (ordinary : first.excluded = first.entryExcluded) (active : focal ∉ first.excluded)
    (valued : ProtocolState.BindingsHoldValues focal setup.program first.point)
    (law : PMF (setup.CommitRecoveryValueChoice focal
      (setup.commitRecoveryModel.infoOf focal prior)))
    (fuel : Nat) (distance : fuel + ProtocolState.commitEnd setup.program first.saved =
      ProtocolState.remaining setup.program first.point) :
    let altered := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
      baseline focal ((baseline focal).withLaw (setup.commitRecoveryModel.infoOf focal prior)
        (law.map Subtype.val))
    let success := {history : setup.commitRecoveryProtocol.History |
      history.state.elim False (fun last => last.excluded = first.entryExcluded ∧
        ProtocolState.BindingsHoldValues focal setup.program last.eraseHistory.point)}
    1 - ((setup.commitRecoveryModel.runBehavioralFrom altered fuel
      ⟨some first, prior⟩).toOuterMeasure success).toReal ≤
      (Fintype.card Player * instructionCount setup.program : Nat) * (omission + bad) := by
  classical
  intro altered success
  have lower := setup.commitRecoveryNormalizedTrembledProfile_success_mass_lower omission
    omissionNonnegative omissionBounded bad badNonnegative badBounded values focal first prior
    committing ordinary active valued law fuel distance
  have factorNonnegative : 0 ≤ (1 - omission) * (1 - bad) :=
    mul_nonneg (sub_nonneg.mpr omissionBounded) (sub_nonneg.mpr badBounded)
  have bernoulli := one_sub_pow_le_mul factorNonnegative (Fintype.card Player * fuel)
  have rates : 1 - (1 - omission) * (1 - bad) ≤ omission + bad := by
    nlinarith [mul_nonneg omissionNonnegative badNonnegative]
  have count : fuel ≤ instructionCount setup.program := by
    have bounded := ProtocolState.remaining_le_instructionCount setup.program first.point
    omega
  have countReal : (Fintype.card Player * fuel : Nat) ≤
      (Fintype.card Player * instructionCount setup.program : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left (Fintype.card Player) count
  calc
    _ ≤ 1 - ((1 - omission) * (1 - bad)) ^ (Fintype.card Player * fuel) := by linarith
    _ ≤ (Fintype.card Player * fuel : Nat) * (1 - (1 - omission) * (1 - bad)) := bernoulli
    _ ≤ (Fintype.card Player * fuel : Nat) * (omission + bad) :=
      mul_le_mul_of_nonneg_left rates (Nat.cast_nonneg _)
    _ ≤ _ := by
      simpa only [Nat.cast_mul] using
        mul_le_mul_of_nonneg_right countReal (add_nonneg omissionNonnegative badNonnegative)

open Classical in
/-- Conditioning the ACTUAL original stopped/terminal joint on successful
first close changes its continuation payoff by a uniformly vanishing source
error. The posterior retains the genuine boundary and the entire later
terminal history, including later resets. At zero success mass the standard
fiber posterior is the original law; no conditional law is asserted there. -/
theorem commitRecoveryNormalizedTrembledProfile_success_value_error
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (ordinary : first.excluded = first.entryExcluded) (active : focal ∉ first.excluded)
    (valued : ProtocolState.BindingsHoldValues focal setup.program first.point)
    (law : PMF (setup.CommitRecoveryValueChoice focal
      (setup.commitRecoveryModel.infoOf focal prior)))
    (fuel : Nat) (distance : fuel + ProtocolState.commitEnd setup.program first.saved =
      ProtocolState.remaining setup.program first.point)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ history,
      |setup.commitRecoveryPayoff utility excludedPayoff focal history| ≤ bound) :
    let certificate := setup.commitRecoveryProtocol_bounded.wellFoundedHistories
    let altered := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
      baseline focal ((baseline focal).withLaw (setup.commitRecoveryModel.infoOf focal prior)
        (law.map Subtype.val))
    let success := {history : setup.commitRecoveryProtocol.History |
      history.state.elim False (fun last => last.excluded = first.entryExcluded ∧
        ProtocolState.BindingsHoldValues focal setup.program last.eraseHistory.point)}
    let joint := bindPairLaw (setup.commitRecoveryModel.runBehavioralFrom altered fuel
      ⟨some first, prior⟩)
        (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate baseline)
    let observed := fun pair : setup.commitRecoveryProtocol.History ×
      setup.commitRecoveryProtocol.History => decide (pair.1 ∈ success)
    |expect (fiberPosterior joint observed true)
        (fun pair => setup.commitRecoveryPayoff utility excludedPayoff focal pair.2) -
      expect (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate altered
        ⟨some first, prior⟩) (setup.commitRecoveryPayoff utility excludedPayoff focal)| ≤
      (Fintype.card Player * instructionCount setup.program : Nat) *
        (omission + bad) * (2 * bound) := by
  classical
  intro certificate altered success joint observed
  let payoff := setup.commitRecoveryPayoff utility excludedPayoff focal
  have mass : ((joint.map observed) true).toReal =
      ((setup.commitRecoveryModel.runBehavioralFrom altered fuel
        ⟨some first, prior⟩).toOuterMeasure success).toReal := by
    calc
      _ = (joint.toOuterMeasure (Prod.fst ⁻¹' success)).toReal := by
        congr 1
        rw [PMF.map_apply, PMF.toOuterMeasure_apply]
        apply tsum_congr
        intro pair
        by_cases good : pair.1 ∈ success <;> simp [observed, good, Set.indicator]
      _ = ((joint.map Prod.fst).toOuterMeasure success).toReal := by
        rw [PMF.toOuterMeasure_map_apply]
      _ = _ := by rw [bindPairLaw_map_fst]
  have close := PMF.WithinTV.of_bind_point (joint.map observed) true
    (fiberPosterior joint observed) (le_refl (1 - ((joint.map observed) true).toReal))
  rw [fiberPosterior_reconstruct] at close
  have interval (pair : setup.commitRecoveryProtocol.History ×
      setup.commitRecoveryProtocol.History) :
      -bound ≤ payoff pair.2 ∧ payoff pair.2 ≤ -bound + 2 * bound := by
    have limits := abs_le.mp (bounded pair.2)
    exact ⟨limits.1, by linarith [limits.2]⟩
  have forwards := close.expect_sub_le (fun pair => payoff pair.2) (-bound) (2 * bound)
    (fun pair _ => interval pair)
  have backwards := close.symm.expect_sub_le (fun pair => payoff pair.2) (-bound) (2 * bound)
    (fun pair _ => interval pair)
  have split := setup.commitRecoveryNormalizedTrembledProfile_local_terminal_window omission
    omissionNonnegative omissionBounded bad badNonnegative badBounded values certificate focal
    first prior committing fuel distance (law.map Subtype.val)
  have terminalLaw : joint.map Prod.snd =
      setup.commitRecoveryModel.runBehavioralTerminalFrom certificate altered
        ⟨some first, prior⟩ := by
    rw [bindPairLaw_map_snd]
    exact split.symm
  have terminalValue : expect joint (fun pair => payoff pair.2) =
      expect (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate altered
        ⟨some first, prior⟩) payoff := by
    calc
      _ = expect (joint.map Prod.snd) payoff := (expect_map Prod.snd joint payoff).symm
      _ = _ := congrArg (fun law => expect law payoff) terminalLaw
  rw [terminalValue, mass] at forwards backwards
  have loss := setup.commitRecoveryNormalizedTrembledProfile_success_mass_loss omission
    omissionNonnegative omissionBounded bad badNonnegative badBounded values focal first prior
    committing ordinary active valued law fuel distance
  have scaled := mul_le_mul_of_nonneg_right loss (by positivity : 0 ≤ 2 * bound)
  apply abs_le.mpr
  exact ⟨by linarith, by linarith⟩

end Vegas.SourceProgram.Setup
