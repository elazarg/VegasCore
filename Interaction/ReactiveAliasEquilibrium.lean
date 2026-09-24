/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAliasBayes
import Interaction.ReactiveAliasIncentives
import GameTheoryExtensions.Protocol.ContinuationSimulation

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
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

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
  rw [FinDist.map_comp] at projected
  exact projected

/-- Erasing ineffective private response names supplies a deterministic
continuation simulation at every raw information site. The deviator's entire
future policy is represented, including behavior conditioned on remembered
private aliases. The proof uses projected beliefs, not equality of raw recall. -/
def aliasContinuationSimulation
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (target : (raw.information initial horizon scheduler).BehavioralAssessment)
    (strategy : target.strategy = (fun player => normal.canonicalPolicy raw stable closed
      initial horizon scheduler player (source.strategy player)))
    (beliefs : ∀ who (original : (raw.information initial horizon scheduler).InformationSite who),
      (target.belief who original).map
          (normal.informationHistory raw stable initial horizon scheduler who original.1) =
        source.belief who (normal.site raw stable initial horizon scheduler who original)) :
    GameTheory.ContinuationSimulation
      (((normal.menu raw).information initial horizon scheduler).assessmentComparison
        History.state (2 * horizon + 1) source)
      ((raw.information initial horizon scheduler).assessmentComparison
        (fun history => normal.state history.state) (2 * horizon + 1) target) := by
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
  refine GameTheory.ContinuationSimulation.ofMap_expect
    (fun who deviation =>
      (normal.site raw stable initial horizon scheduler who deviation.1,
        normal.aliasDeviation raw stable initial horizon scheduler who
          (data who deviation.1).1 deviation.2)) ?_ ?_
  · intro who deviation payoff
    simpa only [assessmentComparison, FinDist.expect_map, Context.value,
      BehavioralAssessment.continuationContext] using
      normal.canonical_context_value raw stable closed initial horizon scheduler
        source target strategy who deviation.1 (beliefs who deviation.1) payoff
  · intro who deviation payoff
    simpa only [assessmentComparison, FinDist.expect_map, Context.value,
      BehavioralAssessment.continuationContext] using
      normal.aliasDeviation_context_value raw stable closed initial horizon scheduler
        source target strategy who deviation.1 (beliefs who deviation.1)
          (data who deviation.1).1 (data who deviation.1).2
            (Classical.choose_spec (hasData who deviation.1)) payoff deviation.2

/-- Adding private response aliases preserves sequential equilibrium for
utilities of the normalized final state. Consistency uses one common fully
mixed sequence; rationality compares every whole continuation-policy deviation.
The conclusion retains all projected information-set beliefs and the complete
initialized final-state law. -/
theorem exists_canonical_sequentialEquilibrium
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (payoff : Principal → app.ProtocolState → ℝ)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((normal.menu raw).decisionInformationAntichain initial horizon scheduler)
      (fun who original => source.continuationContext original
        (fun history => payoff who history.state) (2 * horizon + 1))) :
    ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
      target.strategy = (fun who => normal.canonicalPolicy raw stable closed
        initial horizon scheduler who (source.strategy who)) ∧
      target.IsSequentialEquilibriumFor
        (raw.decisionInformationAntichain initial horizon scheduler)
        (fun who original => target.continuationContext original
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
  · exact (normal.aliasContinuationSimulation raw stable closed initial horizon scheduler
      source target strategy beliefs).sequentialEquilibrium
        ((normal.menu raw).decisionInformationAntichain initial horizon scheduler)
        (raw.decisionInformationAntichain initial horizon scheduler) consistent
          (fun state who => payoff who state) equilibrium
  · rw [strategy]
    exact normal.canonical_initial_stateLaw raw stable closed initial horizon scheduler
      source.strategy (2 * horizon + 1)

end Interaction.ReactiveApplication.SubmissionNormalization
