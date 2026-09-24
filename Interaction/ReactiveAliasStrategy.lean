/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveNormalHistory
import Interaction.ReactiveFiniteAssessment
import GameTheoryExtensions.Math.Probability.ActionSplitting

/-! # Common fully mixed strategies for private response aliases

The same perturbation weight splits every normalized choice into its finite
raw fiber. Raw information states retain all private response names, while
the prescribed normalized strategy reads their projected recall. These laws
give full support and strategy convergence simultaneously at every reached
information site. Bayes-belief compatibility and continuation incentives
require additional proofs.
-/

noncomputable section

namespace Interaction.ReactiveApplication.SubmissionNormalization

open GameTheory.Protocol GameTheory.Math.Probability Filter

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (normal : app.SubmissionNormalization) (raw : app.ResponseMenu)
  (stable : ∀ who past view,
    raw.actions who (normal.recall who past) view = raw.actions who past view)
  (closed : ∀ who past view response, response ∈ raw.actions who past view →
    normal.action who past view response ∈ raw.actions who past view)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

def canonicalPolicy (who : Principal)
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who) :
    (raw.information initial horizon scheduler).BehavioralPolicy who := fun observed =>
  (source (normal.info who observed)).map
    (normal.canonicalChoice raw stable closed initial horizon scheduler who observed)

def aliasKernel (who : Principal) (observed : app.Info)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    ((normal.menu raw).information initial horizon scheduler).Choice who
      (normal.info who observed) →
        FinDist ((raw.information initial horizon scheduler).Choice who observed) := by
  let := Fintype.ofFinite ((raw.information initial horizon scheduler).Choice who observed)
  exact FinDist.splitKernel
    (normal.choice raw stable initial horizon scheduler who observed)
    (normal.canonicalChoice raw stable closed initial horizon scheduler who observed)
    (normal.choice_canonicalChoice raw stable closed initial horizon scheduler who observed)
    weight nonnegative atMostOne

def splitPolicy (who : Principal)
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    (raw.information initial horizon scheduler).BehavioralPolicy who := fun observed =>
  (source (normal.info who observed)).bind
    (normal.aliasKernel raw stable closed initial horizon scheduler who observed
      weight nonnegative atMostOne)

theorem splitPolicy_project (who : Principal)
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) (observed : app.Info) :
    ((normal.splitPolicy raw stable closed initial horizon scheduler who source
      weight nonnegative atMostOne) observed).map
        (normal.choice raw stable initial horizon scheduler who observed) =
      source (normal.info who observed) := by
  let := Fintype.ofFinite ((raw.information initial horizon scheduler).Choice who observed)
  exact FinDist.split_project _ _ _ _ weight nonnegative atMostOne

/-- Each raw choice contributes its normalized choice probability times an
alias factor independent of the source profile. This includes zero masses. -/
theorem splitPolicy_prob (who : Principal)
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) (observed : app.Info)
    (chosen : (raw.information initial horizon scheduler).Choice who observed) :
    ((normal.splitPolicy raw stable closed initial horizon scheduler who source
      weight nonnegative atMostOne) observed).prob chosen =
      (source (normal.info who observed)).prob
          (normal.choice raw stable initial horizon scheduler who observed chosen) *
        (normal.aliasKernel raw stable closed initial horizon scheduler who observed
          weight nonnegative atMostOne
          (normal.choice raw stable initial horizon scheduler who observed chosen)).prob chosen :=
    by
  let := Fintype.ofFinite ((raw.information initial horizon scheduler).Choice who observed)
  exact FinDist.split_prob _ _ _ _ weight nonnegative atMostOne chosen

theorem canonicalPolicy_project (who : Principal)
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (observed : app.Info) :
    ((normal.canonicalPolicy raw stable closed initial horizon scheduler who source)
      observed).map (normal.choice raw stable initial horizon scheduler who observed) =
        source (normal.info who observed) := by
  rw [canonicalPolicy, FinDist.map_comp]
  change (source (normal.info who observed)).map
    (fun action => normal.choice raw stable initial horizon scheduler who observed
      (normal.canonicalChoice raw stable closed initial horizon scheduler who observed action)) = _
  simp only [choice_canonicalChoice]
  exact FinDist.map_id _

theorem splitPolicy_fullSupport (who : Principal)
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) (positive : 0 < weight)
    (observed : app.Info) (mixed : (source (normal.info who observed)).FullSupport) :
    ((normal.splitPolicy raw stable closed initial horizon scheduler who source
      weight nonnegative atMostOne) observed).FullSupport := by
  let := Fintype.ofFinite ((raw.information initial horizon scheduler).Choice who observed)
  exact FinDist.split_fullSupport _ _ _ _ mixed weight nonnegative atMostOne positive

theorem splitPolicy_converges (who : Principal)
    (sequence : Nat →
      ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (observed : app.Info)
    (converges : FinDistConvergesPointwise (fun n => sequence n (normal.info who observed))
      (source (normal.info who observed)))
    (weight : Nat → ℝ) (nonnegative : ∀ n, 0 ≤ weight n) (atMostOne : ∀ n, weight n ≤ 1)
    (vanishes : Tendsto weight atTop (nhds 0)) :
    FinDistConvergesPointwise
      (fun n => (normal.splitPolicy raw stable closed initial horizon scheduler who
        (sequence n) (weight n) (nonnegative n) (atMostOne n)) observed)
      ((normal.canonicalPolicy raw stable closed initial horizon scheduler who source) observed) :=
    by
  let := Fintype.ofFinite ((raw.information initial horizon scheduler).Choice who observed)
  exact FinDist.split_converges _ _ _ _ _ converges weight nonnegative atMostOne vanishes

/-- A fully mixed normalized assessment induces full support at every raw
decision site, with one common weight across all players and information sets. -/
theorem split_fullyMixed
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (mixed : source.IsFullyMixed)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) (positive : 0 < weight) :
    (InformationModel.BehavioralAssessment.ofStrategy fun who =>
      normal.splitPolicy raw stable closed initial horizon scheduler who (source.strategy who)
        weight nonnegative atMostOne).IsFullyMixed := by
  intro who original
  apply normal.splitPolicy_fullSupport raw stable closed initial horizon scheduler who
    (source.strategy who) weight nonnegative atMostOne positive original.1
  exact mixed who (normal.site raw stable initial horizon scheduler who original)

/-- Strategy coordinates of a single source assessment sequence converge at
all raw decision sites. This does not assert convergence of raw beliefs. -/
theorem split_strategy_converges
    (sequence : Nat →
      ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence source)
    (weight : Nat → ℝ) (nonnegative : ∀ n, 0 ≤ weight n) (atMostOne : ∀ n, weight n ≤ 1)
    (vanishes : Tendsto weight atTop (nhds 0)) (who : Principal)
    (original : (raw.information initial horizon scheduler).InformationSite who) :
    FinDistConvergesPointwise
      (fun n => (normal.splitPolicy raw stable closed initial horizon scheduler who
        ((sequence n).strategy who) (weight n) (nonnegative n) (atMostOne n)) original.1)
      ((normal.canonicalPolicy raw stable closed initial horizon scheduler who
        (source.strategy who)) original.1) :=
  normal.splitPolicy_converges raw stable closed initial horizon scheduler who
    (fun n => (sequence n).strategy who) (source.strategy who) original.1
    (converges.strategy who (normal.site raw stable initial horizon scheduler who original))
    weight nonnegative atMostOne vanishes

end Interaction.ReactiveApplication.SubmissionNormalization
