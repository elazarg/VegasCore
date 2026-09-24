/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAliasStrategy
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion

/-! # Consistency from compatible alias perturbations

The split raw strategies admit canonical Bayes beliefs at every decision site.
If those beliefs project to the source approximants, one common subsequence
gives consistent raw beliefs projecting to the prescribed source beliefs.

The exact Bayes projection is a premise here, to be supplied by the history
and focal-recall argument. This analytic composition does not establish that
premise or continuation rationality.
-/

noncomputable section

namespace Interaction.ReactiveApplication.SubmissionNormalization

open GameTheory.Protocol GameTheory.Math.Probability Filter
open GameTheory.Protocol.InformationModel

variable {Principal : Type} [Fintype Principal] [DecidableEq Principal]
  {app : ReactiveApplication Principal}
  (normal : app.SubmissionNormalization) (raw : app.ResponseMenu)
  (stable : ∀ who past view,
    raw.actions who (normal.recall who past) view = raw.actions who past view)
  (closed : ∀ who past view response, response ∈ raw.actions who past view →
    normal.action who past view response ∈ raw.actions who past view)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

def splitBayes
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (mixed : source.IsFullyMixed) (weight : ℝ) (positive : 0 < weight)
    (atMostOne : weight ≤ 1) :
    (raw.information initial horizon scheduler).BehavioralAssessment :=
  (BehavioralAssessment.ofStrategy fun who =>
    normal.splitPolicy raw stable closed initial horizon scheduler who (source.strategy who)
      weight positive.le atMostOne).bayes
        (normal.split_fullyMixed raw stable closed initial horizon scheduler
          source mixed weight positive.le atMostOne positive)
        (raw.decisionInformationAntichain initial horizon scheduler)

theorem splitBayes_fullyMixed
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (mixed : source.IsFullyMixed) (weight : ℝ) (positive : 0 < weight)
    (atMostOne : weight ≤ 1) :
    (normal.splitBayes raw stable closed initial horizon scheduler
      source mixed weight positive atMostOne).IsFullyMixed :=
  normal.split_fullyMixed raw stable closed initial horizon scheduler
    source mixed weight positive.le atMostOne positive

theorem splitBayes_bayes
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (mixed : source.IsFullyMixed) (weight : ℝ) (positive : 0 < weight)
    (atMostOne : weight ≤ 1) :
    BehavioralAssessment.IsBayesConsistent (raw.information initial horizon scheduler)
      (normal.splitBayes raw stable closed initial horizon scheduler
        source mixed weight positive atMostOne)
      (raw.decisionInformationAntichain initial horizon scheduler) :=
  BehavioralAssessment.bayes_isBayesConsistent _ _ _

/-- The compatibility premise is required at every raw information site for
every perturbation, including sites outside the limiting profile's support. -/
theorem consistent_of_splitBayes_projection
    (sequence : Nat →
      ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (converges : BehavioralAssessmentConvergesPointwise sequence source)
    (weight : Nat → ℝ) (positive : ∀ n, 0 < weight n) (atMostOne : ∀ n, weight n ≤ 1)
    (vanishes : Tendsto weight atTop (nhds 0))
    (projects : ∀ n who
      (original : (raw.information initial horizon scheduler).InformationSite who),
      ((normal.splitBayes raw stable closed initial horizon scheduler
          (sequence n) (mixed n) (weight n) (positive n) (atMostOne n)).belief who original).map
        (normal.informationHistory raw stable initial horizon scheduler who original.1) =
      (sequence n).belief who (normal.site raw stable initial horizon scheduler who original)) :
    ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
      target.strategy = (fun who => normal.canonicalPolicy raw stable closed
        initial horizon scheduler who (source.strategy who)) ∧
      target.IsSequentiallyConsistent (raw.decisionInformationAntichain initial horizon scheduler) ∧
      ∀ who (original : (raw.information initial horizon scheduler).InformationSite who),
        (target.belief who original).map
          (normal.informationHistory raw stable initial horizon scheduler who original.1) =
        source.belief who (normal.site raw stable initial horizon scheduler who original) := by
  apply BehavioralAssessment.exists_consistent_completion_preserving
    (raw.decisionInformationAntichain initial horizon scheduler)
    (fun who => normal.canonicalPolicy raw stable closed
      initial horizon scheduler who (source.strategy who))
    (fun n => normal.splitBayes raw stable closed initial horizon scheduler
      (sequence n) (mixed n) (weight n) (positive n) (atMostOne n))
    (fun n => normal.splitBayes_fullyMixed raw stable closed initial horizon scheduler
      (sequence n) (mixed n) (weight n) (positive n) (atMostOne n))
    (fun n => normal.splitBayes_bayes raw stable closed initial horizon scheduler
      (sequence n) (mixed n) (weight n) (positive n) (atMostOne n))
    (fun who original => normal.split_strategy_converges raw stable closed
      initial horizon scheduler sequence source converges weight
        (fun n => (positive n).le) atMostOne vanishes who original)
    (fun who original => normal.informationHistory raw stable
      initial horizon scheduler who original.1)
    (fun who original => source.belief who
      (normal.site raw stable initial horizon scheduler who original))
  intro who original
  simpa only [projects] using
    converges.belief who (normal.site raw stable initial horizon scheduler who original)

end Interaction.ReactiveApplication.SubmissionNormalization
