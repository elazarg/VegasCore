/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAliasBayes
import Interaction.ReactiveAliasIncentives

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
  refine ⟨target, strategy, ⟨?_, consistent⟩, beliefs, ?_⟩
  · intro who original alternative _allowed
    have hasData : ∃ past view, original.1 = some (past, view) := by
      obtain ⟨_reference, _running, response, member⟩ := original.2
      cases observed : original.1 with
      | none =>
          rw [observed] at member
          change some response = none at member
          contradiction
      | some data => exact ⟨data.1, data.2, rfl⟩
    obtain ⟨past, view, observed⟩ := hasData
    change (target.continuationContext original
      (fun history => payoff who (normal.state history.state)) (2 * horizon + 1)).value
        alternative ≤
      (target.continuationContext original
        (fun history => payoff who (normal.state history.state)) (2 * horizon + 1)).value
          (target.strategy who)
    rw [normal.aliasDeviation_context_value raw stable closed initial horizon scheduler source
        target strategy who original (beliefs who original) past view observed (payoff who)
          alternative,
      normal.canonical_context_value raw stable closed initial horizon scheduler source target
        strategy who original (beliefs who original) (payoff who)]
    exact equilibrium.1 who (normal.site raw stable initial horizon scheduler who original)
      (normal.aliasDeviation raw stable initial horizon scheduler who past alternative)
      (Set.mem_univ _)
  · rw [strategy]
    exact normal.canonical_initial_stateLaw raw stable closed initial horizon scheduler
      source.strategy (2 * horizon + 1)

end Interaction.ReactiveApplication.SubmissionNormalization
