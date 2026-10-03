/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceEffectiveImmediateComparator
import Vegas.Game.SourceServiceFreeRationality
import GameTheoryExtensions.Analysis.Protocol.BehavioralContinuity

/-! # A clean value floor from actual varying native pins

The actual uniform/WAIT/immediate pin equation recovers the varying immediate
laws at compatible sites in the returned native subsequence. Finite genuine
own sites admit a common comparator subsequence. Its limit agrees with the
assessment at compatible sites, so rational free continuations bound its
whole value. Authentic zero collection for every actual immediate comparator
then gives the assessment the base-payoff minimum. Disclosure normalization
need not converge at transcripts of zero source probability.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "menu" => service.bounds.menu (runtime service.setup) service.leaks
local notation "model" => ReactiveApplication.ResponseMenu.information
  (service.bounds.menu (runtime service.setup) service.leaks)
  (initialLaw service.setup) service.horizon service.scheduler

local instance pin_history_nonempty : Nonempty (((menu).protocol (initialLaw service.setup)
    service.horizon service.scheduler).History) :=
  ⟨((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).initHistory⟩

private theorem immediate_limit_from_pins
    (profiles : Nat → BehavioralProfile service.setup.program)
    (weight : Nat → Player → (app).Info → ℝ)
    (weightNonnegative : ∀ n who info, 0 ≤ weight n who info)
    (weightSmall : ∀ n who info, weight n who info ≤ 1)
    (delta : Nat → ℝ) (deltaNonnegative : ∀ n, 0 ≤ delta n)
    (deltaSmall : ∀ n, delta n ≤ 1) (deltaVanishes : Tendsto delta atTop (nhds 0))
    (sequence : Nat → (model).BehavioralAssessment) (assessment : (model).BehavioralAssessment)
    (index : Nat → Nat) (increasing : StrictMono index)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise
      (fun n => sequence (index n)) assessment)
    (pinned : ∀ n who (site : (model).InformationSite who),
      service.sourceCompatibleInfo who site.1 →
        (sequence n).strategy who site.1 =
          mix (delta n) (deltaNonnegative n) (deltaSmall n)
            ((menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler
              who site.1)
            (mix (weight n who site.1) (weightNonnegative n who site.1)
              (weightSmall n who site.1)
              (((menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler
                who (app).silentPolicy) site.1)
              (service.effectiveImmediateComparator (profiles n) who site.1)))
    (who : Player) (site : (model).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (weightVanishes : Tendsto (fun n => weight n who site.1) atTop (nhds 0)) :
    PMFConvergesPointwise
      (fun n => service.effectiveImmediateComparator (profiles (index n)) who site.1)
      (assessment.strategy who site.1) := by
  apply pmfConvergesPointwise_iff_toReal.mpr
  intro choice
  let uniform := (((menu).uniformPolicy (initialLaw service.setup) service.horizon
    service.scheduler who site.1) choice).toReal
  let silent := ((((menu).restrictPolicy (initialLaw service.setup) service.horizon
    service.scheduler who (app).silentPolicy) site.1) choice).toReal
  let factor n := (1 - delta (index n)) * (1 - weight (index n) who site.1)
  let rest n := delta (index n) * uniform +
    ((1 - delta (index n)) * weight (index n) who site.1) * silent
  have deltaAlong := deltaVanishes.comp increasing.tendsto_atTop
  have waitAlong := weightVanishes.comp increasing.tendsto_atTop
  have one : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have factorLimit : Tendsto factor atTop (nhds 1) := by
    simpa only [factor, Function.comp_def, sub_zero, one_mul] using
      (one.sub deltaAlong).mul (one.sub waitAlong)
  have restLimit : Tendsto rest atTop (nhds 0) := by
    simpa only [rest, Function.comp_def, zero_mul, sub_zero, one_mul, zero_add] using
      (deltaAlong.mul_const uniform).add (((one.sub deltaAlong).mul waitAlong).mul_const silent)
  have formula (n : Nat) : ((sequence (index n)).strategy who site.1 choice).toReal =
      rest n + factor n *
        (service.effectiveImmediateComparator (profiles (index n)) who site.1 choice).toReal := by
    rw [pinned (index n) who site compatible, mix_apply_toReal, mix_apply_toReal]
    dsimp only [rest, factor, uniform, silent]
    ring
  have atomLimit := (converges.strategy who site).toReal choice
  have divided : Tendsto (fun n =>
      (((sequence (index n)).strategy who site.1 choice).toReal - rest n) / factor n)
      atTop (nhds (assessment.strategy who site.1 choice).toReal) := by
    convert (atomLimit.sub restLimit).div factorLimit (by norm_num : (1 : ℝ) ≠ 0) using 1
    simp only [sub_zero, div_one]
  have positive : ∀ᶠ n in atTop, 0 < factor n :=
    (tendsto_order.mp factorLimit).1 0 (by norm_num)
  apply divided.congr'
  filter_upwards [positive] with n nonzero
  apply (div_eq_iff nonzero.ne').mpr
  linarith [formula n]

open Classical in
/-- The actual varying pin equation, returned assessment convergence, and
rational free continuations give a base-payoff floor at every compatible
site. No global normalized source-policy limit or source belief is supplied. -/
theorem sourceCompatibleInfo_pin_value_lower
    (profiles : Nat → BehavioralProfile service.setup.program)
    (permitted : ∀ n who, (profiles n who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (weight : Nat → Player → (app).Info → ℝ)
    (weightNonnegative : ∀ n who info, 0 ≤ weight n who info)
    (weightSmall : ∀ n who info, weight n who info ≤ 1)
    (bound : Nat → ℝ) (bounded : ∀ n who info, service.sourceCompatibleInfo who info →
      weight n who info ≤ bound n) (boundVanishes : Tendsto bound atTop (nhds 0))
    (delta : Nat → ℝ) (deltaNonnegative : ∀ n, 0 ≤ delta n)
    (deltaSmall : ∀ n, delta n ≤ 1) (deltaVanishes : Tendsto delta atTop (nhds 0))
    (sequence : Nat → (model).BehavioralAssessment) (assessment : (model).BehavioralAssessment)
    (index : Nat → Nat) (increasing : StrictMono index)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise
      (fun n => sequence (index n)) assessment)
    (consistent : assessment.IsSequentiallyConsistent
      ((menu).decisionInformationAntichain (initialLaw service.setup) service.horizon
        service.scheduler))
    (pinned : ∀ n who (site : (model).InformationSite who),
      service.sourceCompatibleInfo who site.1 →
        (sequence n).strategy who site.1 =
          mix (delta n) (deltaNonnegative n) (deltaSmall n)
            ((menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler
              who site.1)
            (mix (weight n who site.1) (weightNonnegative n who site.1)
              (weightSmall n who site.1)
              (((menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler
                who (app).silentPolicy) site.1)
              (service.effectiveImmediateComparator (profiles n) who site.1)))
    (base : (app).ProtocolState → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) :
    let certificate := ((menu).bounded (initialLaw service.setup) service.horizon
      service.scheduler).wellFoundedHistories
    let payoff := fun player (final : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History) => TerminalAudit.utility base
        ((runtime service.setup).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample) deposit final.state player
    (∀ who (site : (model).InformationSite who), ¬ service.sourceCompatibleInfo who site.1 →
      ∀ law : PMF ((model).Choice who site.1),
        (assessment.continuationContext certificate site (payoff who)).value
          ((assessment.strategy who).withLaw site.1 law) ≤
        (assessment.continuationContext certificate site (payoff who)).value
          (assessment.strategy who)) →
    ∀ who (site : (model).InformationSite who), service.sourceCompatibleInfo who site.1 →
      FinitePayoffBounds.lower (fun final : ((menu).protocol (initialLaw service.setup)
        service.horizon service.scheduler).History => base final.state who) ≤
        (assessment.continuationContext certificate site (payoff who)).value
          (assessment.strategy who) := by
  intro certificate payoff freeOptimal who site compatible
  classical
  let comparator (n : Nat) := service.effectiveImmediateComparator (profiles (index n)) who
  obtain ⟨laws, further, furtherIncreasing, limits⟩ :=
    exists_subseq_pmfConvergesPointwise_pi
      (fun n (current : (model).InformationSite who) => comparator n current.1)
  let limitPolicy : (model).BehavioralPolicy who := fun info =>
    if current : (model).IsDecisionInfo who info then laws ⟨info, current⟩ else comparator 0 info
  have policyLimits (current : (model).InformationSite who) : PMFConvergesPointwise
      (fun n => comparator (further n) current.1) (limitPolicy current.1) := by
    simp only [limitPolicy, current.2, ↓reduceDIte]
    exact limits current
  have agrees (current : (model).InformationSite who)
      (currentCompatible : service.sourceCompatibleInfo who current.1) :
      limitPolicy current.1 = assessment.strategy who current.1 := by
    have waitVanishes : Tendsto (fun n => weight n who current.1) atTop (nhds 0) :=
      squeeze_zero (fun n => weightNonnegative n who current.1)
        (fun n => bounded n who current.1 currentCompatible) boundVanishes
    have actualLimit := service.immediate_limit_from_pins profiles weight weightNonnegative
      weightSmall delta deltaNonnegative deltaSmall deltaVanishes sequence assessment index
        increasing converges pinned who current currentCompatible waitVanishes
    exact (policyLimits current).unique (actualLimit.subseq furtherIncreasing)
  have comparison := service.sourceCompatibleInfo_agree_continuation_le (menu) assessment
    consistent certificate payoff freeOptimal who site limitPolicy agrees
  let extremum := fun final : ((menu).protocol (initialLaw service.setup) service.horizon
    service.scheduler).History => base final.state who
  have floor (n : Nat) : FinitePayoffBounds.lower extremum ≤
      (assessment.continuationContext certificate site (payoff who)).value
        (comparator (further n)) := by
    have clean := service.effectiveImmediateComparator_charge_zero_at_information
      (profiles (index (further n))) who (permitted (index (further n)) who) certificate
        assessment.strategy site compatible sample authentic
    have tower := assessment.continuationContextWith_value_tower
      ((model).runBehavioralTerminalFrom certificate) site (payoff who)
      (comparator (further n)) (payoffIntegrable_of_finite _ _)
    change FinitePayoffBounds.lower extremum ≤
      (assessment.continuationContextWith ((model).runBehavioralTerminalFrom certificate)
        site (payoff who)).value (comparator (further n))
    rw [tower, ← expect_constant (assessment.belief who site) (FinitePayoffBounds.lower extremum)]
    apply expect_mono _ (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
    intro history _
    let law := (model).runBehavioralTerminalFrom certificate
      (Profile.update (sig := (model).behavioralSignature) assessment.strategy who
        (comparator (further n))) history.1
    rw [← expect_constant law (FinitePayoffBounds.lower extremum)]
    apply expect_mono _ (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
    intro final supported
    have zero := clean history final supported
    change FinitePayoffBounds.lower extremum ≤ base final.state who -
      TerminalAudit.charge ((runtime service.setup).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample) final.state who * deposit who
    rw [zero, zero_mul, sub_zero]
    exact FinitePayoffBounds.lower_le extremum final
  let _ := Fintype.ofFinite (((menu).protocol (initialLaw service.setup) service.horizon
    service.scheduler).History)
  let total := ∑ final : ((menu).protocol (initialLaw service.setup) service.horizon
    service.scheduler).History, |payoff who final|
  have totalBound (final : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History) : |payoff who final| ≤ total :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff who other)) (Finset.mem_univ final)
  have totalNonnegative : 0 ≤ total := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have values := (model).continuationContext_value_tendsto_of_bounded_terminal certificate
    (sequence := fun _ => assessment) (target := assessment)
    (fun player current => pmfConvergesPointwise_const (assessment.strategy player current.1))
    who site (pmfConvergesPointwise_const (assessment.belief who site)) policyLimits (payoff who)
      total totalNonnegative (fun final _ => totalBound final)
  exact (le_of_tendsto_of_tendsto tendsto_const_nhds values
    (Eventually.of_forall floor)).trans comparison

end Vegas.AsyncServiceSpec
