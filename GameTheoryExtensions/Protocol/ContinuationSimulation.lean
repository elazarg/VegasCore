/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.Sequential
import GameTheoryExtensions.Protocol.SequentialIncentives

/-! # Continuation simulation by finite mixtures

A certificate represents each target continuation comparison by one finite
mixture of source comparisons for the same player. Both prescribed and deviating
outcome laws use the same mixture. This is a sufficient, compositional condition
for preserving incentives for every utility, without requiring finite outcomes.

The certificate is indexed by continuation comparisons, not by runtime states.
Its use with protocol assessments still requires constructing those assessments
and proving target belief consistency separately. Exact law matching is stronger
than the incentive-cone criterion; it is not claimed to be necessary.
-/

noncomputable section

namespace GameTheory

open Math.Probability

universe uι uo us ut ur

/-- A whole target deviation is simulated by a finite mixture of source
continuation comparisons. The source comparison may start at a different
information site in each branch. Matching both laws with the same weights
ensures that the prescribed continuation receives the same treatment as the
deviation. No source or target belief consistency follows from this data. -/
structure ContinuationSimulation {ι : Type uι} {Outcome : Type uo}
    {Source : ι → Type us} {Target : ι → Type ut}
    (source : ∀ who, Source who → IncentiveComparison Outcome)
    (target : ∀ who, Target who → IncentiveComparison Outcome) where
  alternatives : ∀ who, Target who → FinDist (Source who)
  prescribed : ∀ who deviation, (target who deviation).prescribed =
    (alternatives who deviation).bind fun original => (source who original).prescribed
  alternative : ∀ who deviation, (target who deviation).alternative =
    (alternatives who deviation).bind fun original => (source who original).alternative

namespace ContinuationSimulation

variable {ι : Type uι} {Outcome : Type uo}
  {Source : ι → Type us} {Target : ι → Type ut} {Third : ι → Type ur}
  {source : ∀ who, Source who → IncentiveComparison Outcome}
  {target : ∀ who, Target who → IncentiveComparison Outcome}
  {third : ∀ who, Third who → IncentiveComparison Outcome}

/-- Direct simulation is the point-mass case. -/
def ofMap (decode : ∀ who, Target who → Source who)
    (prescribed : ∀ who deviation, (target who deviation).prescribed =
      (source who (decode who deviation)).prescribed)
    (alternative : ∀ who deviation, (target who deviation).alternative =
      (source who (decode who deviation)).alternative) :
    ContinuationSimulation source target where
  alternatives who deviation := FinDist.pure (decode who deviation)
  prescribed who deviation := by simpa only [FinDist.pure_bind] using prescribed who deviation
  alternative who deviation := by simpa only [FinDist.pure_bind] using alternative who deviation

/-- Equality of every continuation expectation supplies the same certificate
as equality of laws. Indicator payoffs suffice to recover each point mass. -/
def ofMap_expect (decode : ∀ who, Target who → Source who)
    (prescribed : ∀ who deviation utility,
      (target who deviation).prescribed.expect utility =
        (source who (decode who deviation)).prescribed.expect utility)
    (alternative : ∀ who deviation utility,
      (target who deviation).alternative.expect utility =
        (source who (decode who deviation)).alternative.expect utility) :
    ContinuationSimulation source target := by
  refine ofMap decode ?_ ?_
  · intro who deviation
    apply FinDist.ext_of_prob
    intro outcome
    exact (FinDist.expect_prob_pure _ outcome).symm.trans
      ((prescribed who deviation _).trans (FinDist.expect_prob_pure _ outcome))
  · intro who deviation
    apply FinDist.ext_of_prob
    intro outcome
    exact (FinDist.expect_prob_pure _ outcome).symm.trans
      ((alternative who deviation _).trans (FinDist.expect_prob_pure _ outcome))

def refl (source : ∀ who, Source who → IncentiveComparison Outcome) :
    ContinuationSimulation source source :=
  ofMap (fun _ => id) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Composition expands intermediate comparison mixtures. In particular, it
does not strengthen randomized backtranslation to one source continuation. -/
def trans (first : ContinuationSimulation source target)
    (second : ContinuationSimulation target third) :
    ContinuationSimulation source third where
  alternatives who deviation :=
    (second.alternatives who deviation).bind (first.alternatives who)
  prescribed who deviation := by
    rw [second.prescribed, FinDist.bind_bind]
    exact FinDist.bind_congr (fun original _ => first.prescribed who original)
  alternative who deviation := by
    rw [second.alternative, FinDist.bind_bind]
    exact FinDist.bind_congr (fun original _ => first.alternative who original)

/-- A common outcome decoder preserves a law-pair certificate. This changes
the observation on which utility depends; it does not change what players
observe during play, their information sites, or their assessment beliefs. -/
def map {Observed : Type*} (simulation : ContinuationSimulation source target)
    (observe : Outcome → Observed) :
    ContinuationSimulation
      (fun who original =>
        ⟨(source who original).prescribed.map observe,
          (source who original).alternative.map observe⟩)
      (fun who deviation =>
        ⟨(target who deviation).prescribed.map observe,
          (target who deviation).alternative.map observe⟩) where
  alternatives := simulation.alternatives
  prescribed who deviation := by rw [simulation.prescribed, FinDist.map_bind]
  alternative who deviation := by rw [simulation.alternative, FinDist.map_bind]

/-- Every source incentive inequality implies the simulated target inequality.
The source comparisons may involve different information sites and deviations. -/
theorem preserves (simulation : ContinuationSimulation source target)
    (utility : Outcome → ι → ℝ)
    (respected : ∀ who deviation, (source who deviation).Holds (utility · who)) :
    ∀ who deviation, (target who deviation).Holds (utility · who) := by
  intro who deviation
  simp only [IncentiveComparison.Holds, simulation.prescribed,
    simulation.alternative, FinDist.expect_bind]
  exact FinDist.expect_mono (fun original _ => respected who original)

/-- For finite outcomes, law-pair simulation supplies the exact semantic
criterion's cone inclusion. The simulation theorem itself needs no finiteness
assumption on the outcome carrier. -/
theorem difference_mem_cone [Fintype Outcome]
    (simulation : ContinuationSimulation source target) (who : ι) (deviation : Target who) :
    (target who deviation).difference ∈ IncentiveComparison.cone (source who) := by
  rw [IncentiveComparison.mem_cone_iff]
  intro utility respected
  simp only [IncentiveComparison.Holds, simulation.prescribed,
    simulation.alternative, FinDist.expect_bind]
  exact FinDist.expect_mono (fun original _ => respected original)

section Protocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E T : Protocol.ExecutionProtocol Player}
  {M : Protocol.InformationModel E} {N : Protocol.InformationModel T}
  {Observation : Type*}
  {sourceObserve : E.History → Observation} {targetObserve : T.History → Observation}
  {sourceFuel targetFuel : Nat}
  {sourceAssessment : M.BehavioralAssessment} {targetAssessment : N.BehavioralAssessment}

/-- Utility-independent continuation-law certificates imply sequential
rationality against all whole-policy deviations. Assessments are supplied;
this theorem constructs neither strategies nor beliefs. -/
theorem sequentialRationality
    (simulation : ContinuationSimulation
      (M.assessmentComparison sourceObserve sourceFuel sourceAssessment)
      (N.assessmentComparison targetObserve targetFuel targetAssessment))
    (utility : Observation → Player → ℝ)
    (rational : sourceAssessment.IsSequentiallyRationalWithin
      (fun who history => utility (sourceObserve history) who) sourceFuel) :
    targetAssessment.IsSequentiallyRationalWithin
      (fun who history => utility (targetObserve history) who) targetFuel := by
  rw [N.isSequentiallyRationalWithin_iff_comparisons targetObserve targetFuel]
  apply simulation.preserves utility
  exact (M.isSequentiallyRationalWithin_iff_comparisons sourceObserve sourceFuel
    sourceAssessment utility).mp rational

variable
  [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)]
  [∀ who (site : N.InformationSite who), Fintype (N.InformationHistory who site.1)]

/-- Consistency is the separate analytic obligation. Once it is proved for
the target assessment, the continuation certificate transports sequential
equilibrium for arbitrary utilities of the chosen observation. This statement
does not assert equality of the initialized outcome laws. -/
theorem sequentialEquilibrium
    (simulation : ContinuationSimulation
      (M.assessmentComparison sourceObserve sourceFuel sourceAssessment)
      (N.assessmentComparison targetObserve targetFuel targetAssessment))
    (sourceAntichain : M.DecisionInformationAntichain)
    (targetAntichain : N.DecisionInformationAntichain)
    (targetConsistent : targetAssessment.IsSequentiallyConsistent targetAntichain)
    (utility : Observation → Player → ℝ)
    (equilibrium : sourceAssessment.IsSequentialEquilibriumFor sourceAntichain
      (fun who site => sourceAssessment.continuationContext site
        (fun history => utility (sourceObserve history) who) sourceFuel)) :
    targetAssessment.IsSequentialEquilibriumFor targetAntichain
      (fun who site => targetAssessment.continuationContext site
        (fun history => utility (targetObserve history) who) targetFuel) :=
  ⟨simulation.sequentialRationality utility equilibrium.1, targetConsistent⟩

end Protocol

end ContinuationSimulation
end GameTheory
