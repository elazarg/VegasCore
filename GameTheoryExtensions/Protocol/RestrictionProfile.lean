/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.RestrictionExecution
import GameTheory.Analysis.Protocol.Sequential
import GameTheoryExtensions.Math.Probability.Convergence
import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Retained decision laws and their vanishing perturbations

Only information values corresponding to actual source decisions are pinned.
Target decisions created solely by departures remain free for rational
completion. Perturbations use the target's ordinary full-support reference law.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability Filter

variable {Player : Type} {E T : ExecutionProtocol Player}
  {M : InformationModel E} {N : InformationModel T} (restriction : M.ActionRestriction N)

private theorem apply_transport {Index : Type*} {Value : Index → Type*}
    (values : ∀ index, Value index) {first second : Index} (same : first = second) :
    Eq.mp (congrArg Value same) (values first) = values second := by
  subst second
  rfl

def Retained (who : Player) (info : N.InfoState who) : Prop :=
  ∃ site : M.InformationSite who, restriction.information who site.1 = info

theorem retained_site (who : Player) (site : M.InformationSite who) :
    restriction.Retained who (restriction.information who site.1) := ⟨site, rfl⟩

/-- The source law at a retained target information value. Injectivity makes
the selected source site unique; no hidden history is inspected. -/
def retainedLaw (source : ∀ who, M.BehavioralPolicy who) (who : Player)
    (info : N.InfoState who) (retained : restriction.Retained who info) :
    PMF (N.Choice who info) :=
  Eq.mp (congrArg (fun value => PMF (N.Choice who value)) retained.choose_spec)
    ((source who retained.choose.1).map (restriction.choice who retained.choose.1))

@[simp] theorem retainedLaw_at (source : ∀ who, M.BehavioralPolicy who)
    (who : Player) (site : M.InformationSite who)
    (retained : restriction.Retained who (restriction.information who site.1)) :
    restriction.retainedLaw source who (restriction.information who site.1) retained =
      (source who site.1).map (restriction.choice who site.1) := by
  have chosen : retained.choose = site :=
    Subtype.ext ((restriction.information who).injective retained.choose_spec)
  exact apply_transport
    (fun original : M.InformationSite who =>
      (source who original.1).map (restriction.choice who original.1)) chosen

/-- Fill new information values with any supplied target profile. -/
def extendProfile (source : ∀ who, M.BehavioralPolicy who)
    (fallback : ∀ who, N.BehavioralPolicy who) : ∀ who, N.BehavioralPolicy who := by
  classical
  exact fun who info => if retained : restriction.Retained who info then
    restriction.retainedLaw source who info retained else fallback who info

theorem extendProfile_extends (source : ∀ who, M.BehavioralPolicy who)
    (fallback : ∀ who, N.BehavioralPolicy who) :
    restriction.ExtendsProfile source (restriction.extendProfile source fallback) := by
  intro who site
  simp only [extendProfile, dite_eq_left (restriction.retained_site who site), retainedLaw_at]

/-- Pinned laws for the simultaneous agent completion. New sites temporarily
use the reference; the free-agent construction subsequently replaces them. -/
def perturbProfile (source : ∀ who, M.BehavioralPolicy who)
    (reference : ∀ who, N.BehavioralPolicy who)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) :
    ∀ who, N.BehavioralPolicy who := by
  classical
  exact fun who info => if retained : restriction.Retained who info then
    mix epsilon nonnegative small (reference who info)
      (restriction.retainedLaw source who info retained)
    else reference who info

def PerturbsProfile (source : ∀ who, M.BehavioralPolicy who)
    (reference target : ∀ who, N.BehavioralPolicy who)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) : Prop :=
  ∀ who (site : M.InformationSite who),
    target who (restriction.information who site.1) =
      mix epsilon nonnegative small
        (reference who (restriction.information who site.1))
        ((source who site.1).map (restriction.choice who site.1))

theorem perturbProfile_perturbs (source : ∀ who, M.BehavioralPolicy who)
    (reference : ∀ who, N.BehavioralPolicy who)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) :
    restriction.PerturbsProfile source reference
      (restriction.perturbProfile source reference epsilon nonnegative small)
      epsilon nonnegative small := by
  intro who site
  simp only [perturbProfile, dite_eq_left (restriction.retained_site who site), retainedLaw_at]

theorem perturbProfile_fullSupport (source : ∀ who, M.BehavioralPolicy who)
    (reference : ∀ who, N.BehavioralPolicy who)
    (epsilon : ℝ) (positive : 0 < epsilon) (small : epsilon ≤ 1)
    (who : Player) (info : N.InfoState who) (full : FullSupport (reference who info)) :
    FullSupport (restriction.perturbProfile source reference epsilon positive.le small
      who info) := by
  classical
  intro choice
  unfold perturbProfile
  split
  · exact mem_support_mix_left epsilon positive.le small positive (full choice)
  · exact full choice

private theorem transport_map {Index : Type*} {Value : Index → Type*}
    (laws : ∀ index, PMF (Value index)) {first second : Index} (same : first = second) :
    (laws first).map (fun value => Eq.mp (congrArg Value same) value) = laws second := by
  subst second
  exact PMF.map_id _

theorem perturbs_at_history (source : ∀ who, M.BehavioralPolicy who)
    (reference target : ∀ who, N.BehavioralPolicy who)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (perturbs : restriction.PerturbsProfile source reference target epsilon nonnegative small)
    (original : E.History) (running : ¬ E.terminal original.state) (who : Player) :
    target who (N.infoOf who (restriction.history original).trace) =
      mix epsilon nonnegative small
        (reference who (N.infoOf who (restriction.history original).trace))
        ((source who (M.infoOf who original.trace)).map (restriction.choiceAt who original)) := by
  by_cases active : E.active original.state who
  · obtain ⟨decision, observed⟩ := M.exists_informationSite_of_active who original running active
    have indexed : target who (restriction.information who (M.infoOf who original.trace)) =
        mix epsilon nonnegative small
          (reference who (restriction.information who (M.infoOf who original.trace)))
          ((source who (M.infoOf who original.trace)).map
            (restriction.choice who (M.infoOf who original.trace))) := by
      rcases decision with ⟨info, permitted⟩
      dsimp only at observed
      subst info
      exact perturbs who ⟨_, permitted⟩
    calc
      _ = (target who (restriction.information who (M.infoOf who original.trace))).map
          (fun action => Eq.mp
            (congrArg (N.Choice who) (restriction.observed who original).symm) action) :=
        (transport_map (target who) (restriction.observed who original).symm).symm
      _ = _ := by
        rw [indexed, mix_map,
          transport_map (reference who) (restriction.observed who original).symm,
          PMF.map_comp]
        rfl
  · have inactive : ¬ T.active (restriction.history original).state who :=
      fun enabled => active ((restriction.active original who).mp enabled)
    let _ := N.subsingleton_choice_of_not_active (restriction.history original).trace inactive
    obtain ⟨witness, _⟩ :=
      (target who (N.infoOf who (restriction.history original).trace)).support_nonempty
    exact (eq_pure_of_subsingleton _ witness).trans
      (eq_pure_of_subsingleton _ witness).symm

/-- Convergent source laws and vanishing pinned trembles force the target
limit to extend the source profile at every retained decision site. -/
theorem extendsProfile_of_perturbs_converges
    (reference : ∀ who, N.BehavioralPolicy who)
    (sourceSequence : ℕ → M.BehavioralAssessment) (source : M.BehavioralAssessment)
    (targetSequence : ℕ → N.BehavioralAssessment) (target : N.BehavioralAssessment)
    (sourceMixed : (sourceSequence 0).IsFullyMixed)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (targetConverges : BehavioralAssessmentConvergesPointwise targetSequence target)
    (epsilon : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ epsilon n) (small : ∀ n, epsilon n ≤ 1)
    (vanishes : Tendsto epsilon atTop (nhds 0))
    (perturbs : ∀ n, restriction.PerturbsProfile (sourceSequence n).strategy reference
      (targetSequence n).strategy (epsilon n) (nonnegative n) (small n)) :
    restriction.ExtendsProfile source.strategy target.strategy := by
  intro who site
  let _ : Finite (M.Choice who site.1) := (sourceMixed who site).finite
  have sourceLaws := (sourceConverges.strategy who site).map (restriction.choice who site.1)
  have targetLaws := targetConverges.strategy who (restriction.site who site)
  apply pmf_ext_toReal
  intro action
  have convergence := (vanishes.mul_const
    (((reference who (restriction.information who site.1)) action).toReal)).add
      (((tendsto_const_nhds (x := (1 : ℝ))).sub vanishes).mul (sourceLaws action))
  simp only [zero_mul, sub_zero, one_mul, zero_add] at convergence
  have same (n : ℕ) :
      (((targetSequence n).strategy who (restriction.information who site.1)) action).toReal =
      epsilon n * (((reference who (restriction.information who site.1)) action).toReal) +
        (1 - epsilon n) *
          ((((sourceSequence n).strategy who site.1).map
            (restriction.choice who site.1)) action).toReal := by
    rw [perturbs n who site, mix_apply_toReal]
  exact tendsto_nhds_unique (targetLaws action)
    (convergence.congr' (Eventually.of_forall fun n => (same n).symm))

end GameTheory.Protocol.InformationModel.ActionRestriction
