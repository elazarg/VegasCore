/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoverySuccessBelief

/-! # Successful source values along the original assessment sequence

Removing the two prescribed source failure rates gives the same current
domain law. Its distance from the actual current prescription vanishes even
when that domain law varies. The original success-conditioned joint retains
its information-history tilt and converges to the original continuation value.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
/-- The selected original domain law transported to its original full menu,
without changing its underlying declaration. -/
def commitRecoveryNormalizedDomainLaw
    (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    PMF (setup.CommitRecoveryValueChoice who info) :=
  (values who (setup.commitRecoveryErasedInformation who
    (setup.commitRecoveryNoMissInformation who info))).map (fun value =>
      ⟨(setup.commitRecoveryNoMissErasedChoice who info).symm value.val, value.property⟩)

omit [Fintype Player] in
/-- The current domain law is exactly the same normalized prescription with
both source failure rates set to zero. -/
theorem commitRecoveryNormalizedDomainLaw_raw
    (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryNormalizedDomainLaw values who info).map Subtype.val =
      setup.commitRecoveryNormalizedTrembledProfile 0 le_rfl zero_le_one
        0 le_rfl zero_le_one values who info := by
  apply pmf_map_injective Subtype.val_injective
  rw [commitRecoveryNormalizedDomainLaw, PMF.map_comp, PMF.map_comp,
    commitRecoveryNormalizedTrembledProfile, setup.commitRecoveryNoMissErasedProfile_raw]
  simp only [commitRecoveryValueTremble, mix_zero]
  split <;> (simp only [PMF.map_comp, Function.comp_def]; rfl)

/-- This is the actual original belief, first-close boundary and terminal
history joint conditioned on successful first close. It does not condition
each starting history separately. -/
def commitRecoverySuccessValue
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (law : PMF (setup.CommitRecoveryValueChoice focal site.1))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ) :
    ℝ := by
  classical
  let certificate := setup.commitRecoveryProtocol_bounded.wellFoundedHistories
  let baseline := setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative
    omissionBounded bad badNonnegative badBounded values
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
  exact expect (fiberPosterior joint observed true)
    (fun triple => setup.commitRecoveryPayoff utility excludedPayoff focal triple.2.2)

section Sequence

variable
  (omission bad : ℕ → ℝ)
  (omissionNonnegative : ∀ n, 0 ≤ omission n) (omissionBounded : ∀ n, omission n ≤ 1)
  (badNonnegative : ∀ n, 0 ≤ bad n) (badBounded : ∀ n, bad n ≤ 1)
  (omissionVanishes : Tendsto omission atTop (nhds 0))
  (badVanishes : Tendsto bad atTop (nhds 0))
  (values : ℕ → (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
    PMF (setup.CommitRecoveryValueChoice who info))
  (sequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
  (limit : setup.commitRecoveryModel.BehavioralAssessment)
  (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence limit)
  (prescribed : ∀ n who (history : setup.commitRecoveryProtocol.History)
    (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
    (sequence n).strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
      setup.commitRecoveryNormalizedTrembledProfile
        (omission n) (omissionNonnegative n) (omissionBounded n)
        (bad n) (badNonnegative n) (badBounded n) (values n) who
          (setup.commitRecoveryModel.infoOf who history.trace))

include omissionVanishes badVanishes converges prescribed

omit [Fintype Player] in
open Classical in
/-- The same varying domain prescription converges to the actual current
limit strategy. No convergence assumption on the domain weights is needed. -/
theorem commitRecoveryNormalizedDomainLaw_converges
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal) :
    PMFConvergesPointwise
      (fun n => (setup.commitRecoveryNormalizedDomainLaw (values n) focal site.1).map Subtype.val)
      (limit.strategy focal site.1) := by
  classical
  obtain ⟨history, running, _action, _offered⟩ := site.property
  have actual (n : ℕ) := prescribed n focal history.1 running
  rw [history.property] at actual
  apply pmfConvergesPointwise_iff_toReal.mpr
  intro choice
  have close (n : ℕ) :
      |(((setup.commitRecoveryNormalizedDomainLaw (values n) focal site.1).map Subtype.val)
          choice).toReal - ((sequence n).strategy focal site.1 choice).toReal| ≤
        omission n + bad n := by
    rw [setup.commitRecoveryNormalizedDomainLaw_raw, actual]
    have small : (1 - omission n) * (1 - bad n) ≤ 1 := by
      calc
        _ ≤ 1 - omission n := mul_le_of_le_one_right
          (sub_nonneg.mpr (omissionBounded n)) (sub_le_self 1 (badNonnegative n))
        _ ≤ 1 := sub_le_self 1 (omissionNonnegative n)
    have near := PMF.WithinTV.of_domination _ _ _ small
      (setup.commitRecoveryNormalizedTrembledProfile_domain_lower
        (omission n) (omissionNonnegative n) (omissionBounded n)
        (bad n) (badNonnegative n) (badBounded n) (values n) focal site.1)
    exact (near.apply choice).trans (by
      nlinarith [mul_nonneg (omissionNonnegative n) (badNonnegative n)])
  have difference : Tendsto (fun n =>
      (((setup.commitRecoveryNormalizedDomainLaw (values n) focal site.1).map Subtype.val)
        choice).toReal - ((sequence n).strategy focal site.1 choice).toReal)
      atTop (nhds 0) :=
    squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using close n)
      (by simpa only [zero_add] using omissionVanishes.add badVanishes)
  simpa only [sub_add_cancel, zero_add] using
    difference.add ((converges.strategy focal site).toReal choice)

omit [Fintype Player] in
open Classical in
/-- The original limit prescription is supported on genuine domain choices
at each original played source input. -/
theorem commitRecovery_normalized_limit_domain_support
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (choice : setup.commitRecoveryModel.Choice focal site.1)
    (supported : choice ∈ (limit.strategy focal site.1).support) :
    ∀ move, choice.val = some move → move.missing = false ∧ ¬ move.action.IsFailure := by
  classical
  have current := setup.commitRecoveryNormalizedDomainLaw_converges
    omission bad omissionNonnegative omissionBounded badNonnegative badBounded
    omissionVanishes badVanishes values sequence limit converges prescribed focal site
  by_contra outside
  have zero (n : ℕ) :
      ((setup.commitRecoveryNormalizedDomainLaw (values n) focal site.1).map Subtype.val)
        choice = 0 := by
    by_contra nonzero
    have member := (PMF.mem_support_iff _ _).mpr nonzero
    obtain ⟨value, _selected, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact outside (by simpa only [← same] using value.property)
  have zeroLimit : Tendsto (fun n =>
      ((setup.commitRecoveryNormalizedDomainLaw (values n) focal site.1).map Subtype.val)
        choice) atTop (nhds 0) := by
    simp only [zero]
    exact tendsto_const_nhds
  exact (PMF.mem_support_iff _ _).mp supported
    (tendsto_nhds_unique (current choice) zeroLimit)

open Classical in
/-- Success conditioning preserves the original limit value along any
convergent sequence of actual current domain laws. -/
theorem commitRecoverySuccessValue_tendsto
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (regular : ∀ history : setup.commitRecoveryModel.InformationHistory focal site.1,
      ∃ first, history.1.state = some first ∧
        ProtocolState.atCommit setup.program first.point = true ∧
        first.excluded = first.entryExcluded ∧
        ProtocolState.BindingsHoldValues focal setup.program first.point)
    (laws : ℕ → PMF (setup.CommitRecoveryValueChoice focal site.1))
    (target : PMF (setup.commitRecoveryModel.Choice focal site.1))
    (lawConverges : PMFConvergesPointwise (fun n => (laws n).map Subtype.val) target)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ history,
      |setup.commitRecoveryPayoff utility excludedPayoff focal history| ≤ bound) :
    Tendsto (fun n => setup.commitRecoverySuccessValue
      (omission n) (omissionNonnegative n) (omissionBounded n)
      (bad n) (badNonnegative n) (badBounded n) (values n) (sequence n)
      focal site (laws n) utility excludedPayoff) atTop
      (nhds ((limit.continuationContext
        setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
          (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
            ((limit.strategy focal).withLaw site.1 target))) := by
  classical
  let payoff := setup.commitRecoveryPayoff utility excludedPayoff focal
  let certificate := setup.commitRecoveryProtocol_bounded.wellFoundedHistories
  let original := fun n => ((sequence n).continuationContext certificate site payoff).value
    (((sequence n).strategy focal).withLaw site.1 ((laws n).map Subtype.val))
  have localPolicies (decision : setup.commitRecoveryModel.InformationSite focal) :
      PMFConvergesPointwise
        (fun n => ((sequence n).strategy focal).withLaw site.1
          ((laws n).map Subtype.val) decision.1)
        (((limit.strategy focal).withLaw site.1 target) decision.1) := by
    by_cases same : decision.1 = site.1
    · have equal : decision = site := Subtype.ext same
      subst decision
      simpa only [InformationModel.BehavioralPolicy.withLaw_self] using lawConverges
    · simpa only [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ same] using
        converges.strategy focal decision
  have originalLimit :=
    setup.commitRecoveryModel.continuationContext_value_tendsto_of_bounded_terminal
      certificate (fun who decision => converges.strategy who decision) focal site
      (converges.belief focal site) localPolicies payoff bound boundNonnegative
      (fun final _ => bounded final)
  let success := fun n => setup.commitRecoverySuccessValue
    (omission n) (omissionNonnegative n) (omissionBounded n)
    (bad n) (badNonnegative n) (badBounded n) (values n) (sequence n)
      focal site (laws n) utility excludedPayoff
  have error (n : ℕ) : |success n - original n| ≤
      ((Fintype.card Player * instructionCount setup.program : Nat) *
        (omission n + bad n)) * (2 * bound) :=
    (setup.commitRecovery_normalized_success_belief_value_error
      (omission n) (omissionNonnegative n) (omissionBounded n)
      (bad n) (badNonnegative n) (badBounded n) (values n) (sequence n)
      (prescribed n) focal site regular (laws n) utility excludedPayoff
      bound boundNonnegative bounded).2
  have vanishes : Tendsto (fun n =>
      ((Fintype.card Player * instructionCount setup.program : Nat) *
        (omission n + bad n)) * (2 * bound)) atTop (nhds 0) := by
    convert ((omissionVanishes.add badVanishes).const_mul
      ((Fintype.card Player * instructionCount setup.program : Nat) : ℝ)).mul_const (2 * bound)
      using 1
    simp
  have difference : Tendsto (fun n => success n - original n) atTop (nhds 0) :=
    squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using error n) vanishes
  have combined := difference.add originalLimit
  change Tendsto (fun n => success n - original n + original n) atTop _ at combined
  simpa only [sub_add_cancel, zero_add] using combined

end Sequence

end Vegas.SourceProgram.Setup
