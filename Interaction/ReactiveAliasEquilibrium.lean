/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAliasBayes
import Interaction.ReactiveAliasIncentives
import GameTheory.Analysis.Protocol.Incentives
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support

/-! # Sequential equilibrium under private response aliases

The two finite-menu games use the same application, scheduler, observations,
packets, and time bound. They differ only in the private names of responses
that have identical effects. This result concerns that operational quotient;
it does not compile a source-language game into a communication environment.
-/

noncomputable section

namespace Interaction.ReactiveApplication.SubmissionNormalization

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open GameTheory.Protocol.InformationModel

variable {Principal : Type} [Fintype Principal] [DecidableEq Principal]
  {app : ReactiveApplication Principal}
  (normal : app.SubmissionNormalization) (raw : app.ResponseMenu)
  (stable : ∀ who past view,
    raw.actions who (normal.recall who past) view = raw.actions who past view)
  (closed : ∀ who past view response, response ∈ raw.actions who past view →
    normal.action who past view response ∈ raw.actions who past view)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

theorem canonical_initial_stateLaw
    (source : ∀ who,
      ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) :
    (((raw.information initial horizon scheduler).runBehavioral
      (fun who => normal.canonicalPolicy raw stable closed initial horizon scheduler who
        (source who)) fuel).map (fun history => normal.state history.state)) =
      (((normal.menu raw).information initial horizon scheduler).runBehavioral source fuel).map
        History.state := by
  have law := normal.runBehavioral_projection raw stable initial horizon scheduler
    (fun who => normal.canonicalPolicy raw stable closed initial horizon scheduler who
      (source who)) source
    (fun who observed => normal.canonicalPolicy_project raw stable closed initial horizon scheduler
      who (source who) observed) fuel (raw.protocol initial horizon scheduler).initHistory
  have projected := congrArg (fun law => law.map History.state) law
  rw [PMF.map_comp] at projected
  exact projected

/-- At every raw information site, the prescribed continuation's normalized
final-state law is the source continuation's final-state law. -/
theorem canonical_assessmentLaw
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (target : (raw.information initial horizon scheduler).BehavioralAssessment)
    (strategy : target.strategy = (fun player => normal.canonicalPolicy raw stable closed
      initial horizon scheduler player (source.strategy player)))
    (who : Principal) (original : (raw.information initial horizon scheduler).InformationSite who)
    (beliefs : (target.belief who original).map
        (normal.informationHistory raw stable initial horizon scheduler who original.1) =
      source.belief who (normal.site raw stable initial horizon scheduler who original)) :
    ((raw.information initial horizon scheduler).assessmentLawWith ((raw.information initial
        horizon scheduler).truncatedRunner (2 * horizon + 1)) target original
        (target.strategy who)).map (fun history => normal.state history.state) =
      (((normal.menu raw).information initial horizon scheduler).assessmentLawWith (((normal.menu
          raw).information initial horizon scheduler).truncatedRunner (2 * horizon + 1))
        source (normal.site raw stable initial horizon scheduler who original)
          (source.strategy who)).map History.state := by
  simp only [assessmentLawWith, GameTheory.Profile.update_eq_self]
  rw [strategy, ← beliefs, PMF.bind_map, PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  have law := normal.runBehavioral_projection raw stable initial horizon scheduler
    (fun player => normal.canonicalPolicy raw stable closed initial horizon scheduler
      player (source.strategy player)) source.strategy
    (fun player observed => normal.canonicalPolicy_project raw stable closed initial horizon
      scheduler player (source.strategy player) observed) (2 * horizon + 1) history.1
  have mapped := congrArg (PMF.map History.state) law
  rw [PMF.map_comp] at mapped
  exact mapped

/-- A raw whole-policy deviation and its alias-erased source deviation induce
the same normalized final-state law at every raw information site. -/
theorem aliasDeviation_assessmentLaw
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (target : (raw.information initial horizon scheduler).BehavioralAssessment)
    (strategy : target.strategy = (fun player => normal.canonicalPolicy raw stable closed
      initial horizon scheduler player (source.strategy player)))
    (who : Principal) (original : (raw.information initial horizon scheduler).InformationSite who)
    (beliefs : (target.belief who original).map
        (normal.informationHistory raw stable initial horizon scheduler who original.1) =
      source.belief who (normal.site raw stable initial horizon scheduler who original))
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : original.1 = some (past, view))
    (alternative : (raw.information initial horizon scheduler).BehavioralPolicy who) :
    ((raw.information initial horizon scheduler).assessmentLawWith ((raw.information initial
        horizon scheduler).truncatedRunner (2 * horizon + 1)) target original
        alternative).map (fun history => normal.state history.state) =
      (((normal.menu raw).information initial horizon scheduler).assessmentLawWith (((normal.menu
          raw).information initial horizon scheduler).truncatedRunner (2 * horizon + 1))
        source (normal.site raw stable initial horizon scheduler who original)
          (normal.aliasDeviation raw initial horizon scheduler who past alternative)).map
            History.state := by
  simp only [assessmentLawWith]
  rw [strategy, ← beliefs, PMF.bind_map, PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  have law := normal.aliasDeviation_historyLaw raw stable closed initial horizon scheduler
    source.strategy who alternative history.1 past view (history.2.trans observed)
  rw [PMF.map_comp] at law
  exact law

/-- Erasing ineffective private response names supplies a deterministic
continuation simulation at every raw information site. The deviator's entire
future policy is represented, including behavior conditioned on remembered
private aliases. The proof uses projected beliefs, not equality of raw recall. -/
def aliasIncentiveSimulation
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (target : (raw.information initial horizon scheduler).BehavioralAssessment)
    (strategy : target.strategy = (fun player => normal.canonicalPolicy raw stable closed
      initial horizon scheduler player (source.strategy player)))
    (beliefs : ∀ who (original : (raw.information initial horizon scheduler).InformationSite who),
      (target.belief who original).map
          (normal.informationHistory raw stable initial horizon scheduler who original.1) =
        source.belief who (normal.site raw stable initial horizon scheduler who original)) :
    GameTheory.IncentiveSimulation
      (((normal.menu raw).information initial horizon scheduler).assessmentComparisonWith
        (((normal.menu raw).information initial horizon scheduler).truncatedRunner
          (2 * horizon + 1)) History.state source)
      ((raw.information initial horizon scheduler).assessmentComparisonWith
        ((raw.information initial horizon scheduler).truncatedRunner (2 * horizon + 1))
        (fun history => normal.state history.state) target) := by
  have hasData (who : Principal)
      (original : (raw.information initial horizon scheduler).InformationSite who) :
      ∃ data, original.1 = some data := by
    obtain ⟨_reference, _running, response, member⟩ := original.2
    cases observed : original.1 with
    | none =>
        rw [observed] at member
        change some response = none at member
        contradiction
    | some data => exact ⟨data, rfl⟩
  let data who original := Classical.choose (hasData who original)
  refine GameTheory.IncentiveSimulation.ofMap
    (fun who deviation =>
      (normal.site raw stable initial horizon scheduler who deviation.1,
        normal.aliasDeviation raw initial horizon scheduler who
          (data who deviation.1).1 deviation.2)) ?_ ?_
  · intro who deviation
    exact normal.canonical_assessmentLaw raw stable closed initial horizon scheduler
      source target strategy who deviation.1 (beliefs who deviation.1)
  · intro who deviation
    exact normal.aliasDeviation_assessmentLaw raw stable closed initial horizon scheduler
      source target strategy who deviation.1 (beliefs who deviation.1)
        (data who deviation.1).1 (data who deviation.1).2
          (Classical.choose_spec (hasData who deviation.1)) deviation.2

/-- Adding private response aliases preserves sequential equilibrium for
utilities of the normalized final state. Consistency uses one common fully
mixed sequence; rationality compares every whole continuation-policy deviation.
The conclusion retains all projected information-set beliefs and the complete
initialized final-state law. -/
theorem exists_canonical_sequentialEquilibrium [app.FiniteNature initial scheduler]
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (payoff : Principal → app.ProtocolState → ℝ)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((normal.menu raw).decisionInformationAntichain initial horizon scheduler)
      (fun who original => source.truncatedContinuationContext original
        (fun history => payoff who history.state) (2 * horizon + 1))) :
    ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
      target.strategy = (fun who => normal.canonicalPolicy raw stable closed
        initial horizon scheduler who (source.strategy who)) ∧
      target.IsSequentialEquilibriumFor
        (raw.decisionInformationAntichain initial horizon scheduler)
        (fun who original => target.truncatedContinuationContext original
          (fun history => payoff who (normal.state history.state)) (2 * horizon + 1)) ∧
      (∀ who (original : (raw.information initial horizon scheduler).InformationSite who),
        (target.belief who original).map
          (normal.informationHistory raw stable initial horizon scheduler who original.1) =
        source.belief who (normal.site raw stable initial horizon scheduler who original)) ∧
      (((raw.information initial horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).map (fun history => normal.state history.state)) =
        (((normal.menu raw).information initial horizon scheduler).runBehavioral source.strategy
          (2 * horizon + 1)).map History.state := by
  obtain ⟨target, strategy, consistent, beliefs⟩ :=
    normal.exists_canonical_consistent raw stable closed initial horizon scheduler source
      equilibrium.2
  refine ⟨target, strategy, ?_, beliefs, ?_⟩
  · have finiteMap {History State : Type} [Finite History] (law : PMF History)
        (observe : History → State) (utility : State → ℝ) :
        PayoffIntegrable (law.map observe) utility :=
      payoffIntegrable_of_finite_support _ _ (by
        rw [PMF.support_map]
        exact (Set.toFinite _).image _)
    exact InformationModel.sequentialEquilibrium_of_simulation _ _
      ((normal.menu raw).decisionInformationAntichain initial horizon scheduler)
      (raw.decisionInformationAntichain initial horizon scheduler) _ _ _ _ source target
      (normal.aliasIncentiveSimulation raw stable closed initial horizon scheduler
        source target strategy beliefs) consistent (fun state who => payoff who state)
      equilibrium (fun _ _ => ⟨finiteMap _ _ _, finiteMap _ _ _⟩)
      (fun _ _ => ⟨finiteMap _ _ _, finiteMap _ _ _⟩)
  · rw [strategy]
    exact normal.canonical_initial_stateLaw raw stable closed initial horizon scheduler
      source.strategy (2 * horizon + 1)

end Interaction.ReactiveApplication.SubmissionNormalization
