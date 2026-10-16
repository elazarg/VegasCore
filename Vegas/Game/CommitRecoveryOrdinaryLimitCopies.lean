/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryPooledOrdinaryLimit

/-! # Original conditional incentives at ordinary copies of the source limit

Actual fully mixed source Bayes comparisons pass through the same assessment
limit. Thus an ordinary copy of an honest site inherits its full raw local
incentives, without a positive lower bound on the site's limiting reach.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
omit [Fintype Player] in
private theorem selected_current_eq
    (first second : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (focal : Player) (query site : setup.commitRecoveryModel.InfoState focal)
    (same : setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal site) = query)
    (law : PMF (setup.commitRecoveryModel.Choice focal query)) :
    setup.commitRecoveryNoMissErasedProfile
        (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) first focal
          ((first focal).withLaw query law)) focal site =
      setup.commitRecoveryNoMissErasedProfile
        (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) second focal
          ((second focal).withLaw query law)) focal site := by
  apply pmf_map_injective Subtype.val_injective
  rw [setup.commitRecoveryNoMissErasedProfile_raw,
    setup.commitRecoveryNoMissErasedProfile_raw, Profile.update_same, Profile.update_same,
    same, InformationModel.BehavioralPolicy.withLaw_self,
    InformationModel.BehavioralPolicy.withLaw_self]

omit [Fintype Player] in
private theorem cast_choice_raw (who : Player)
    {first second : setup.commitRecoveryModel.InfoState who} (same : first = second)
    (choice : setup.commitRecoveryModel.Choice who first) :
    (Equiv.cast (congrArg (setup.commitRecoveryModel.Choice who) same) choice).val =
      choice.val := by
  cases same
  rfl

section Copies

variable [Finite setup.commitRecoveryProtocol.History]
  (sequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
  (limit : setup.commitRecoveryModel.BehavioralAssessment)
  (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence limit)
  (mixed : ∀ n, (sequence n).IsFullyMixed)
  (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
    setup.commitRecoveryModel (sequence n) setup.commitRecoveryModel_decisionAntichain)
  (omission bad : ℕ → ℝ)
  (omissionNonnegative : ∀ n, 0 ≤ omission n) (omissionBounded : ∀ n, omission n ≤ 1)
  (badNonnegative : ∀ n, 0 ≤ bad n) (badBounded : ∀ n, bad n ≤ 1)
  (values : ℕ → (who : Player) → (info : setup.commitRecoveryModel.InfoState who) →
    PMF (setup.CommitRecoveryValueChoice who info))
  (prescribed : ∀ n who (history : setup.commitRecoveryProtocol.History)
    (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
    (sequence n).strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
      setup.commitRecoveryNormalizedTrembledProfile
        (omission n) (omissionNonnegative n) (omissionBounded n)
        (bad n) (badNonnegative n) (badBounded n) (values n) who
          (setup.commitRecoveryModel.infoOf who history.trace))
  (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)

include converges mixed bayes prescribed

open Classical in
/-- Arbitrary current raw-law gains at ordinary copies agree in the SAME
original source limit, including original full-information beliefs. -/
theorem commitRecovery_normalized_limit_gain_eq
    (focal : Player) (target source : setup.commitRecoveryModel.InformationSite focal)
    (same : setup.commitRecoveryErasedInformation focal target.1 =
      setup.commitRecoveryErasedInformation focal source.1)
    (law : PMF (setup.commitRecoveryModel.Choice focal
      (setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal source.1)))) :
    let query := setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal source.1)
    let changed := setup.commitRecoveryNoMissErasedProfile
      (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) limit.strategy focal
        ((limit.strategy focal).withLaw query law))
    (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories source
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw source.1 (changed focal source.1)) -
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories source
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value (limit.strategy focal) =
    (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories target
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw target.1 (changed focal target.1)) -
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories target
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  classical
  let _ := Fintype.ofFinite setup.commitRecoveryProtocol.History
  dsimp only
  let query := setup.commitRecoveryErasedInformation focal
    (setup.commitRecoveryNoMissInformation focal source.1)
  let base := fun n who info => setup.commitRecoveryValueTremble who info
    (omission n) (omissionNonnegative n) (omissionBounded n)
    (bad n) (badNonnegative n) (badBounded n) (values n who info)
  let changed := fun (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) =>
    setup.commitRecoveryNoMissErasedProfile
      (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) profile focal
        ((profile focal).withLaw query law))
  have atSource (n : ℕ) : changed (base n) focal source.1 =
      changed limit.strategy focal source.1 :=
    setup.selected_current_eq (base n) limit.strategy focal query source.1 rfl law
  have atTarget (n : ℕ) : changed (base n) focal target.1 =
      changed limit.strategy focal target.1 := by
    apply setup.selected_current_eq
    change setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal target.1) =
      setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal source.1)
    rw [setup.commitRecoveryNoMissInformation_erased,
      setup.commitRecoveryNoMissInformation_erased, same]
  have exactGain (n : ℕ) := setup.commitRecovery_normalized_conditional_gain_eq (sequence n)
    (mixed n) (bayes n) (base n) (prescribed n) utility excludedPayoff
    setup.commitRecoveryProtocol_bounded.wellFoundedHistories focal target source same law
  dsimp only at exactGain
  have equal (n : ℕ) :
      ((sequence n).continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        source (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (((sequence n).strategy focal).withLaw source.1 (changed limit.strategy focal source.1)) -
        ((sequence n).continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
          source (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
            ((sequence n).strategy focal) =
      ((sequence n).continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        target (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (((sequence n).strategy focal).withLaw target.1 (changed limit.strategy focal target.1)) -
        ((sequence n).continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
          target (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
            ((sequence n).strategy focal) := by
    simpa only [← atSource n, ← atTarget n] using exactGain n
  let payoff := setup.commitRecoveryPayoff utility excludedPayoff focal
  let total := ∑ history : setup.commitRecoveryProtocol.History, |payoff history|
  have totalBound (history : setup.commitRecoveryProtocol.History) : |payoff history| ≤ total :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff other)) (Finset.mem_univ history)
  have actualValue (site : setup.commitRecoveryModel.InformationSite focal)
      (replacement : ℕ → setup.commitRecoveryModel.BehavioralPolicy focal)
      (policy : setup.commitRecoveryModel.BehavioralPolicy focal)
      (policies : ∀ decision : setup.commitRecoveryModel.InformationSite focal,
        PMFConvergesPointwise (fun n => replacement n decision.1) (policy decision.1)) :=
    setup.commitRecoveryModel.continuationContext_value_tendsto_of_bounded_terminal
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories
      (fun who decision => converges.strategy who decision) focal site (converges.belief focal site)
      policies payoff total
      ((abs_nonneg _).trans (totalBound setup.commitRecoveryProtocol.initHistory))
      (fun final _ => totalBound final)
  have installed (site decision : setup.commitRecoveryModel.InformationSite focal) :
      PMFConvergesPointwise
        (fun n => ((sequence n).strategy focal).withLaw site.1
          (changed limit.strategy focal site.1) decision.1)
        (((limit.strategy focal).withLaw site.1
          (changed limit.strategy focal site.1)) decision.1) := by
    by_cases here : decision.1 = site.1
    · have siteEq : decision = site := Subtype.ext here
      subst decision
      simpa only [InformationModel.BehavioralPolicy.withLaw_self] using
        pmfConvergesPointwise_const (changed limit.strategy focal site.1)
    · simpa only [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ here] using
        converges.strategy focal decision
  have left := (actualValue source _ _ (installed source)).sub
    (actualValue source _ _ (converges.strategy focal))
  have right := (actualValue target _ _ (installed target)).sub
    (actualValue target _ _ (converges.strategy focal))
  exact tendsto_nhds_unique left (right.congr' (Eventually.of_forall fun n => (equal n).symm))

open Classical in
/-- The same limit's raw local best response transfers from a genuine source
site to an ordinary erased copy. In particular, the honest-limit theorem can
be consumed directly; no conditional-success or positive-reach premise occurs. -/
theorem commitRecovery_normalized_limit_localOptimal_of_erased_copy
    (focal : Player) (target source : setup.commitRecoveryModel.InformationSite focal)
    (same : setup.commitRecoveryErasedInformation focal target.1 =
      setup.commitRecoveryErasedInformation focal source.1)
    (sourceOptimal : ∀ law : PMF (setup.commitRecoveryModel.Choice focal source.1),
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories source
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          ((limit.strategy focal).withLaw source.1 law) ≤
        (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories source
          (setup.commitRecoveryPayoff utility excludedPayoff focal)).value (limit.strategy focal))
    (law : PMF (setup.commitRecoveryModel.Choice focal target.1)) :
    (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories target
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw target.1 law) ≤
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories target
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  classical
  let targetQuery := setup.commitRecoveryErasedInformation focal
    (setup.commitRecoveryNoMissInformation focal target.1)
  let sourceQuery := setup.commitRecoveryErasedInformation focal
    (setup.commitRecoveryNoMissInformation focal source.1)
  have keys : targetQuery = sourceQuery := by
    dsimp only [targetQuery, sourceQuery]
    rw [setup.commitRecoveryNoMissInformation_erased,
      setup.commitRecoveryNoMissInformation_erased, same]
  let castChoice : setup.commitRecoveryModel.Choice focal targetQuery →
      setup.commitRecoveryModel.Choice focal sourceQuery :=
    Equiv.cast (congrArg (setup.commitRecoveryModel.Choice focal) keys)
  let selected := (law.map (setup.commitRecoveryNoMissErasedChoice focal target.1)).map castChoice
  let changed := setup.commitRecoveryNoMissErasedProfile
    (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) limit.strategy focal
      ((limit.strategy focal).withLaw sourceQuery selected))
  have targetLaw : changed focal target.1 = law := by
    apply pmf_map_injective Subtype.val_injective
    rw [setup.commitRecoveryNoMissErasedProfile_raw, Profile.update_same]
    have queryEq := keys
    change setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal target.1) = sourceQuery at queryEq
    rw [queryEq, InformationModel.BehavioralPolicy.withLaw_self]
    change selected.map Subtype.val = law.map Subtype.val
    dsimp only [selected]
    simp only [PMF.map_comp]
    congr 1
    funext choice
    change (castChoice ((setup.commitRecoveryNoMissErasedChoice focal target.1) choice)).val = _
    exact setup.cast_choice_raw focal keys _
  have shared := setup.commitRecovery_normalized_limit_gain_eq sequence limit converges mixed bayes
    omission bad omissionNonnegative omissionBounded badNonnegative badBounded values prescribed
    utility excludedPayoff focal target source same selected
  dsimp only at shared
  change _ = _ - _ at shared
  have sourceBound := sub_nonpos.mpr (sourceOptimal (changed focal source.1))
  have targetBound := shared ▸ sourceBound
  change (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories target
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw target.1 (changed focal target.1)) -
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories target
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) ≤ 0 at targetBound
  rw [targetLaw] at targetBound
  exact sub_nonpos.mp targetBound

end Copies

end Vegas.SourceProgram.Setup
