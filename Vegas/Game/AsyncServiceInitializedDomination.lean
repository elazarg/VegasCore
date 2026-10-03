/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServicePrescribedCompletion
import GameTheory.Analysis.Protocol.RestrictionDomination
import GameTheoryExtensions.Math.Probability.TotalVariation

/-! # Actual-support initialized domination and native completion loss

The actual first-turn support supplies risk clarity and genuine coverage of
the geometric response law. Uniform native trembles retain a fixed fraction
of each supported first-turn choice. Finite execution therefore retains that
fraction of every complete history, independently of the source profile's
unreachable laws and all completion play after departure.

The same supported-choice kernel also permits information-dependent timing
rates, provided their actual choice laws supply a uniform lower bound.

These are unconditional initialized bounds. They do not compare beliefs
conditioned on rare information values or prove prescribed-site rationality.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
private abbrev dominationMenu : (app).ResponseMenu :=
  service.bounds.riskMenu (runtime service.setup) service.leaks service.bound

local notation "menu" => dominationMenu service
local notation "model" => ReactiveApplication.ResponseMenu.information
  (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound)
  (initialLaw service.setup) service.horizon service.scheduler

/-- The actual geometric timing policy, represented in the finite risk menu.
Coverage is derived when its initialized comparison is used. -/
def geometricProfile (profile : BehavioralProfile service.setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1) :
    ∀ who, (model).BehavioralPolicy who := fun who =>
  (menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
    (sourceServiceTurnPolicy service.setup service.leaks service.bound service.horizon
      (geometricTiming service.setup service.horizon weight nonnegative small) profile who)

open Classical in
/-- Prescribed sites use the real geometric policy with uniform trembles.
The supplied continuation is unrestricted outside the compatible classifier. -/
def completedGeometricProfile (profile : BehavioralProfile service.setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1)
    (delta : ℝ) (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1)
    (continuation : ∀ who, (model).BehavioralPolicy who) :
    ∀ who, (model).BehavioralPolicy who := fun who info =>
  if service.sourceCompatibleInfo who info then
    mix delta deltaNonnegative deltaSmall
      ((menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler who info)
      (service.geometricProfile profile weight nonnegative small who info)
  else continuation who info

private theorem bind_supported_domination {α : Type*}
    (source target : PMF α) (sourceStep targetStep : α → PMF α)
    (initialFactor stepFactor : ℝ) (initialNonnegative : 0 ≤ initialFactor)
    (initialLower : ∀ value, initialFactor * (source value).toReal ≤ (target value).toReal)
    (stepLower : ∀ prior ∈ source.support, ∀ value,
      stepFactor * (sourceStep prior value).toReal ≤ (targetStep prior value).toReal)
    (value : α) :
    (initialFactor * stepFactor) * ((source.bind sourceStep) value).toReal ≤
      ((target.bind targetStep) value).toReal := by
  rw [toReal_bind_apply, toReal_bind_apply]
  calc
    _ = initialFactor * expect source
        (fun prior => stepFactor * (sourceStep prior value).toReal) := by
      rw [expect_const_mul]
      ring
    _ ≤ initialFactor * expect source (fun prior => (targetStep prior value).toReal) :=
      mul_le_mul_of_nonneg_left (expect_mono
        (fun prior supported => stepLower prior supported value)
        (payoffIntegrable_of_bounded _ _ (C := |stepFactor|) fun prior => by
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          exact mul_le_of_le_one_right (abs_nonneg _) (pmf_toReal_apply_le_one _ _))
        (payoffIntegrable_toReal_apply source targetStep value)) initialNonnegative
    _ ≤ expect target (fun prior => (targetStep prior value).toReal) :=
      mul_expect_le_of_prob_le source target initialFactor initialLower _
        (fun _ => ENNReal.toReal_nonneg) (payoffIntegrable_toReal_apply target targetStep value)

private theorem withinTV_of_domination {α : Type*} (source target : PMF α)
    (factor : ℝ) (small : factor ≤ 1)
    (lower : ∀ value, factor * (source value).toReal ≤ (target value).toReal) :
    PMF.WithinTV (1 - factor) source target := by
  intro event
  have first := probOf_domination source target factor lower event
  have second := probOf_domination_excess source target factor lower event
  have atMostOne : (source.toOuterMeasure event).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using outerMeasure_le_one source event)
  have missing : (1 - factor) * (source.toOuterMeasure event).toReal ≤ 1 - factor :=
    mul_le_of_le_one_right (sub_nonneg.mpr small) atMostOne
  have scaled : factor * (source.toOuterMeasure event).toReal ≤
      (source.toOuterMeasure event).toReal :=
    mul_le_of_le_one_left ENNReal.toReal_nonneg small
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem geometric_firstTurn_physical_lower
    (profile : BehavioralProfile service.setup.program)
    (weight : ℝ) (positive : 0 < weight) (small : weight < 1)
    (who : Player) (control : (app).Control)
    (trace : ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some control))
    (acting : control.actor = some who)
    (actual : (app).RoundSupported (initialLaw service.setup) service.horizon service.scheduler
      (sourceServiceTurnPolicy service.setup service.leaks service.bound service.horizon
        (firstTurnTiming service.setup service.horizon) profile) (some control))
    (response : (app).Action) :
    (1 - weight) * ((sourceServiceTurnPolicy service.setup service.leaks service.bound
      service.horizon (firstTurnTiming service.setup service.horizon) profile who
        (control.execution.recall who) (control.execution.observe (app) who)) response).toReal ≤
      ((sourceServiceTurnPolicy service.setup service.leaks service.bound service.horizon
        (geometricTiming service.setup service.horizon weight positive.le small.le) profile who
          (control.execution.recall who)
          (control.execution.observe (app) who)) response).toReal := by
  have clear (player : Player) := sourceServiceFirstTurn_serviceRisk_clear_roundSupported
    service.contract service.timely _ player service.horizon profile rfl control actual
  have persistent (player : Player) := ((runtime service.setup).serviceRisk_clear_iff
    service.leaks service.bound player (control.execution.recall player)
      (control.execution.observe (app) player)).mp (clear player) |>.1
  rw [← sourceServiceImmediatePolicy_firstTurn_roundSupported service service.horizon profile
    control who actual]
  cases turn : (control.execution.observe (app) who).application.publicView.ownTurn? who with
  | none =>
      simp only [sourceServiceImmediatePolicy, clear, ↓reduceIte, turn,
        sourceServiceTurnPolicy]
      exact mul_le_of_le_one_left ENNReal.toReal_nonneg (by linarith)
  | some event =>
      rw [sourceServiceImmediatePolicy_at_event (clear who) turn]
      by_cases recorded : (runtime service.setup).eventRecorded service.leaks
          (control.execution.recall who) event = true
      · rw [sourceServiceTurnPolicy_recorded_silent service service.horizon _ profile who _ _
          event turn recorded]
        simp only [sourceServiceCanonicalOpportunity, recorded, ↓reduceIte,
          ReactiveApplication.silentPolicy]
        exact mul_le_of_le_one_left ENNReal.toReal_nonneg (by linarith)
      · have current : control = ⟨control.remaining, some who, control.execution⟩ := by
          cases control
          simp_all only
        have activeTrace :
            ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
              (some ⟨control.remaining, some who, control.execution⟩) := current ▸ trace
        rw [sourceServiceDecision_clear_geometric_response service.bounds service.bound profile
          who control.execution activeTrace persistent event (Bool.eq_false_of_not_eq_true recorded)
            turn weight positive small, mix_apply_toReal]
        exact le_add_of_nonneg_left (mul_nonneg positive.le ENNReal.toReal_nonneg)

/-- Geometric timing retains the prescribed first-turn choice at every actual
initialized input. Its off-path policy need not converge or be covered. -/
theorem geometricProfile_firstTurn_choice_lower
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (weight : ℝ) (positive : 0 < weight) (small : weight < 1)
    (fuel : Nat)
    (history :
      ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).History)
    (reached : history ∈ ((model).runBehavioral
      (service.firstTurnProfile service.horizon profile) fuel).support)
    (who : Player) (choice : (model).Choice who ((model).infoOf who history.trace)) :
    (1 - weight) * ((service.firstTurnProfile service.horizon profile who
      ((model).infoOf who history.trace)) choice).toReal ≤
      ((service.geometricProfile profile weight positive.le small.le who
        ((model).infoOf who history.trace)) choice).toReal := by
  classical
  by_cases active : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).active history.state who
  · have actual := service.firstTurnProfile_initialized_roundSupported service.horizon profile
      permitted fuel history reached
    have atState : (model).infoOf who history.trace = (app).observe who history.state :=
      (menu).info (initialLaw service.setup) service.horizon service.scheduler who history.trace
    obtain ⟨state, trace⟩ := history
    cases state with
    | none => cases active
    | some control =>
        have acting : control.actor = some who := active
        have input : (model).infoOf who trace =
            some (control.execution.recall who, control.execution.observe (app) who) := by
          rw [atState]
          simp only [ReactiveApplication.observe, acting, ↓reduceIte]
        revert choice
        rw [input]
        intro choice
        obtain ⟨response, _retained, named⟩ := choice.2
        have clear := sourceServiceFirstTurn_serviceRisk_clear_roundSupported service.contract
          service.timely _ who service.horizon profile rfl control actual
        let baseline := sourceServiceTurnPolicy service.setup service.leaks service.bound
          service.horizon (firstTurnTiming service.setup service.horizon) profile who
        let geometric := sourceServiceTurnPolicy service.setup service.leaks service.bound
          service.horizon (geometricTiming service.setup service.horizon weight positive.le
            small.le)
            profile who
        have baselineMap := (menu).restrictPolicy_map_val (initialLaw service.setup) service.horizon
          service.scheduler who baseline _ _ (fun response chosen =>
            service.firstTurnProfile_response_covered service.horizon profile permitted who control
              trace actual response chosen)
        have geometricMap := (menu).restrictPolicy_map_val (initialLaw service.setup)
          service.horizon
          service.scheduler who geometric _ _ (fun response chosen =>
            sourceServiceTurnPolicy_risk_retained service.bounds service.values
              service.initialValues
              service.capacity service.bound service.horizon _ profile who (permitted who) control
                trace clear response chosen)
        have baselineAt := congrArg (fun law => law choice.1) baselineMap
        have geometricAt := congrArg (fun law => law choice.1) geometricMap
        rw [pmf_map_apply_of_injective _ Subtype.val_injective] at baselineAt geometricAt
        rw [named] at baselineAt geometricAt
        have baselineSome := pmf_map_apply_of_injective
          (baseline (control.execution.recall who) (control.execution.observe (app) who))
          (Option.some_injective (app).Action) response
        have geometricSome := pmf_map_apply_of_injective
          (geometric (control.execution.recall who) (control.execution.observe (app) who))
          (Option.some_injective (app).Action) response
        have baselineAtom := baselineAt.trans baselineSome
        have geometricAtom := geometricAt.trans geometricSome
        change (1 - weight) * (((menu).restrictPolicy (initialLaw service.setup) service.horizon
          service.scheduler who baseline (some (control.execution.recall who,
            control.execution.observe (app) who))) choice).toReal ≤
          (((menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
            geometric (some (control.execution.recall who,
              control.execution.observe (app) who))) choice).toReal
        rw [baselineAtom, geometricAtom]
        exact geometric_firstTurn_physical_lower service profile weight positive small who control
          trace acting actual response
  · rw [(model).behavioral_eq_of_not_active
      (service.firstTurnProfile service.horizon profile who)
      (service.geometricProfile profile weight positive.le small.le who) history.trace active]
    exact mul_le_of_le_one_left ENNReal.toReal_nonneg (by linarith)

private theorem completionFactor_nonnegative
    (weight delta : ℝ) (small : weight ≤ 1) (deltaSmall : delta ≤ 1) :
    0 ≤ (1 - delta) * (1 - weight) :=
  mul_nonneg (sub_nonneg.mpr deltaSmall) (sub_nonneg.mpr small)

private theorem completionFactor_small
    (weight delta : ℝ) (nonnegative : 0 ≤ weight)
    (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1) :
    (1 - delta) * (1 - weight) ≤ 1 := by
  have product := mul_le_of_le_one_right (sub_nonneg.mpr deltaSmall)
    (show 1 - weight ≤ 1 by linarith)
  linarith

/-- The bound is independent of every free continuation and of every source
kernel at inputs absent from initialized first-turn play. -/
theorem completedGeometricProfile_firstTurn_choice_lower
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (weight : ℝ) (positive : 0 < weight) (small : weight < 1)
    (delta : ℝ) (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1)
    (continuation : ∀ who, (model).BehavioralPolicy who)
    (fuel : Nat)
    (history :
      ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).History)
    (reached : history ∈ ((model).runBehavioral
      (service.firstTurnProfile service.horizon profile) fuel).support)
    (who : Player) (choice : (model).Choice who ((model).infoOf who history.trace)) :
    ((1 - delta) * (1 - weight)) * ((service.firstTurnProfile service.horizon profile who
      ((model).infoOf who history.trace)) choice).toReal ≤
      ((service.completedGeometricProfile profile weight positive.le small.le delta deltaNonnegative
        deltaSmall continuation who ((model).infoOf who history.trace)) choice).toReal := by
  classical
  by_cases active : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).active history.state who
  · have compatible := service.firstTurnProfile_sourceCompatibleInfo service.horizon profile
      permitted effective fuel history reached who active
    simp only [completedGeometricProfile, compatible, ↓reduceIte, mix_apply_toReal]
    have lower := mul_le_mul_of_nonneg_left
      (service.geometricProfile_firstTurn_choice_lower profile permitted weight positive small
        fuel history reached who choice) (sub_nonneg.mpr deltaSmall)
    rw [← mul_assoc] at lower
    exact lower.trans (le_add_of_nonneg_left
      (mul_nonneg deltaNonnegative ENNReal.toReal_nonneg))
  · rw [(model).behavioral_eq_of_not_active
      (service.firstTurnProfile service.horizon profile who)
      (service.completedGeometricProfile profile weight positive.le small.le delta deltaNonnegative
        deltaSmall continuation who) history.trace active]
    exact mul_le_of_le_one_left ENNReal.toReal_nonneg
      (completionFactor_small weight delta positive.le deltaNonnegative deltaSmall)

private theorem firstTurnProfile_step_lower_of_choice
    (profile : BehavioralProfile service.setup.program)
    (target : ∀ who, (model).BehavioralPolicy who)
    (factor : ℝ) (nonnegative : 0 ≤ factor)
    (history :
      ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).History)
    (lower : ∀ who choice,
      factor * ((service.firstTurnProfile service.horizon profile who
        ((model).infoOf who history.trace)) choice).toReal ≤
          ((target who ((model).infoOf who history.trace)) choice).toReal)
    (next :
      ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).History) :
    factor ^ Fintype.card Player *
        (((model).runBehavioralFrom (service.firstTurnProfile service.horizon profile) 1 history)
          next).toReal ≤
      (((model).runBehavioralFrom target 1 history) next).toReal := by
  rw [(model).runBehavioralFrom_one_localStep, (model).runBehavioralFrom_one_localStep]
  apply prob_bind_ge_mul _ _ _ _ ((model).localStep history) next
  intro choices
  have lower := prob_pi_ge_prod_mul
    (fun who => service.firstTurnProfile service.horizon profile who
      ((model).infoOf who history.trace))
    (fun who => target who ((model).infoOf who history.trace))
    (fun _ => factor) (fun _ => nonnegative) lower choices
  simpa only [Finset.prod_const, Finset.card_univ] using lower

/-- Choice domination is required only at actual initialized first-turn
histories. The target may use arbitrary policies after leaving that support. -/
theorem firstTurnProfile_initialized_domination_of_choice
    (profile : BehavioralProfile service.setup.program)
    (target : ∀ who, (model).BehavioralPolicy who)
    (factor : ℝ) (nonnegative : 0 ≤ factor)
    (lower : ∀ fuel history,
      history ∈ ((model).runBehavioral
        (service.firstTurnProfile service.horizon profile) fuel).support → ∀ who choice,
      factor * ((service.firstTurnProfile service.horizon profile who
        ((model).infoOf who history.trace)) choice).toReal ≤
          ((target who ((model).infoOf who history.trace)) choice).toReal)
    (fuel : Nat)
    (next :
      ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).History) :
    factor ^ (Fintype.card Player * fuel) *
        (((model).runBehavioral (service.firstTurnProfile service.horizon profile) fuel)
          next).toReal ≤
      (((model).runBehavioral target fuel) next).toReal := by
  let baseline := service.firstTurnProfile service.horizon profile
  let stepFactor := factor ^ Fintype.card Player
  have stepNonnegative : 0 ≤ stepFactor := pow_nonneg nonnegative _
  have retained (count : Nat) (last :
      ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).History) :
      stepFactor ^ count * (((model).runBehavioral baseline count) last).toReal ≤
        (((model).runBehavioral target count) last).toReal := by
    induction count generalizing last with
    | zero => simp only [pow_zero, one_mul]; exact le_rfl
    | succ count ih =>
        unfold InformationModel.runBehavioral
        rw [(model).runBehavioralFrom_add baseline count 1,
          (model).runBehavioralFrom_add target count 1, pow_succ]
        apply bind_supported_domination _ _ _ _ (stepFactor ^ count) stepFactor
          (pow_nonneg stepNonnegative _) (fun last => ih last)
        intro history reached next
        exact firstTurnProfile_step_lower_of_choice service profile target factor nonnegative
          history (lower count history reached) next
  simpa only [stepFactor, ← pow_mul] using retained fuel next

/-- The supported-choice bound controls every event of whole initialized
histories, including private recall and pending-message observations. -/
theorem firstTurnProfile_initialized_close_of_choice
    (profile : BehavioralProfile service.setup.program)
    (target : ∀ who, (model).BehavioralPolicy who)
    (factor : ℝ) (nonnegative : 0 ≤ factor) (small : factor ≤ 1)
    (lower : ∀ fuel history,
      history ∈ ((model).runBehavioral
        (service.firstTurnProfile service.horizon profile) fuel).support → ∀ who choice,
      factor * ((service.firstTurnProfile service.horizon profile who
        ((model).infoOf who history.trace)) choice).toReal ≤
          ((target who ((model).infoOf who history.trace)) choice).toReal)
    (fuel : Nat) :
    PMF.WithinTV (1 - factor ^ (Fintype.card Player * fuel))
      ((model).runBehavioral (service.firstTurnProfile service.horizon profile) fuel)
      ((model).runBehavioral target fuel) := by
  apply withinTV_of_domination _ _ _ (pow_le_one₀ nonnegative small)
  exact service.firstTurnProfile_initialized_domination_of_choice profile target factor
    nonnegative lower fuel

/-- Geometric completion retains a uniform fraction of each exact first-turn
history. Its supported-choice bound is derived from the actual runtime. -/
theorem completedGeometricProfile_initialized_domination
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (weight : ℝ) (positive : 0 < weight) (small : weight < 1)
    (delta : ℝ) (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1)
    (continuation : ∀ who, (model).BehavioralPolicy who) (fuel : Nat)
    (next :
      ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).History) :
    ((1 - delta) * (1 - weight)) ^ (Fintype.card Player * fuel) *
        (((model).runBehavioral (service.firstTurnProfile service.horizon profile) fuel)
          next).toReal ≤
      (((model).runBehavioral (service.completedGeometricProfile profile weight positive.le small.le
        delta deltaNonnegative deltaSmall continuation) fuel) next).toReal := by
  exact service.firstTurnProfile_initialized_domination_of_choice profile _ _
    (completionFactor_nonnegative weight delta small.le deltaSmall)
    (service.completedGeometricProfile_firstTurn_choice_lower profile permitted effective weight
      positive small delta deltaNonnegative deltaSmall continuation) fuel next

/-- The same uniform loss controls every initialized event of complete
histories, with no lower bound on any particular history's probability. -/
theorem completedGeometricProfile_initialized_close
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (weight : ℝ) (positive : 0 < weight) (small : weight < 1)
    (delta : ℝ) (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1)
    (continuation : ∀ who, (model).BehavioralPolicy who) (fuel : Nat) :
    PMF.WithinTV (1 - ((1 - delta) * (1 - weight)) ^ (Fintype.card Player * fuel))
      ((model).runBehavioral (service.firstTurnProfile service.horizon profile) fuel)
      ((model).runBehavioral (service.completedGeometricProfile profile weight positive.le small.le
        delta deltaNonnegative deltaSmall continuation) fuel) := by
  exact service.firstTurnProfile_initialized_close_of_choice profile _ _
    (completionFactor_nonnegative weight delta small.le deltaSmall)
    (completionFactor_small weight delta positive.le deltaNonnegative deltaSmall)
    (service.completedGeometricProfile_firstTurn_choice_lower profile permitted effective weight
      positive small delta deltaNonnegative deltaSmall continuation) fuel

end Vegas.AsyncServiceSpec
