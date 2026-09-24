/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAliasStrategy
import Interaction.ReactiveAliasLaw
import Interaction.ReactiveAliasBayes
import Interaction.ReactiveAliasEquilibrium
import Vegas.Pending.ReactiveResponseAliases

/-! # Sequential equilibrium with private native response aliases

The bounded native menus satisfy the recall and closure premises of generic
private-alias splitting. Every normalized policy has a canonical raw policy;
one positive noise weight covers all raw responses at every information set.
Vanishing noise preserves strategy convergence and lifts consistent beliefs
with exact projection at every decision site.

The source here is the normalized native game. Sequential equilibrium,
projected beliefs and initialized state laws are preserved by adding private
aliases. Correspondence with the source language is a separate theorem.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.MessageBounds

open Interaction GameTheory.Protocol GameTheory.Math.Probability Filter
open GameTheory.Protocol.InformationModel

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (bounds : MessageBounds graph) (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : FinDist (State graph)) (horizon : Nat)
  (scheduler : (runtime.reactiveApplication leaks).Scheduler)

def canonicalRawPolicy (who : Player)
    (source : BehavioralPolicy
      ((bounds.menu runtime leaks).information initial horizon scheduler) who) :
    ((bounds.rawMenu runtime leaks).information initial horizon scheduler).BehavioralPolicy who :=
  (runtime.reactiveNormalization leaks).canonicalPolicy (bounds.rawMenu runtime leaks)
    (bounds.rawMenu_recall runtime leaks) (bounds.rawMenu_closed runtime leaks)
    initial horizon scheduler who source

def splitRawPolicy (who : Player)
    (source : BehavioralPolicy
      ((bounds.menu runtime leaks).information initial horizon scheduler) who)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    ((bounds.rawMenu runtime leaks).information initial horizon scheduler).BehavioralPolicy who :=
  (runtime.reactiveNormalization leaks).splitPolicy (bounds.rawMenu runtime leaks)
    (bounds.rawMenu_recall runtime leaks) (bounds.rawMenu_closed runtime leaks)
    initial horizon scheduler who source weight nonnegative atMostOne

theorem splitRawPolicy_project (who : Player)
    (source : BehavioralPolicy
      ((bounds.menu runtime leaks).information initial horizon scheduler) who)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (observed : (runtime.reactiveApplication leaks).Info) :
    ((bounds.splitRawPolicy runtime leaks initial horizon scheduler who source
      weight nonnegative atMostOne) observed).map
        ((runtime.reactiveNormalization leaks).choice (bounds.rawMenu runtime leaks)
          (bounds.rawMenu_recall runtime leaks) initial horizon scheduler who observed) =
      source ((runtime.reactiveNormalization leaks).info who observed) :=
  (runtime.reactiveNormalization leaks).splitPolicy_project (bounds.rawMenu runtime leaks)
    (bounds.rawMenu_recall runtime leaks) (bounds.rawMenu_closed runtime leaks)
    initial horizon scheduler who source weight nonnegative atMostOne observed

theorem splitRaw_fullyMixed
    (source : BehavioralAssessment
      ((bounds.menu runtime leaks).information initial horizon scheduler))
    (mixed : source.IsFullyMixed) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) (positive : 0 < weight) :
    (BehavioralAssessment.ofStrategy fun who =>
      bounds.splitRawPolicy runtime leaks initial horizon scheduler who (source.strategy who)
        weight nonnegative atMostOne).IsFullyMixed :=
  (runtime.reactiveNormalization leaks).split_fullyMixed (bounds.rawMenu runtime leaks)
    (bounds.rawMenu_recall runtime leaks) (bounds.rawMenu_closed runtime leaks)
    initial horizon scheduler source mixed weight nonnegative atMostOne positive

theorem splitRaw_strategy_converges
    (sequence : Nat → BehavioralAssessment
      ((bounds.menu runtime leaks).information initial horizon scheduler))
    (source : BehavioralAssessment
      ((bounds.menu runtime leaks).information initial horizon scheduler))
    (converges : BehavioralAssessmentConvergesPointwise sequence source)
    (weight : Nat → ℝ) (nonnegative : ∀ n, 0 ≤ weight n) (atMostOne : ∀ n, weight n ≤ 1)
    (vanishes : Tendsto weight atTop (nhds 0)) (who : Player)
    (site : InformationSite
      ((bounds.rawMenu runtime leaks).information initial horizon scheduler) who) :
    FinDistConvergesPointwise
      (fun n => (bounds.splitRawPolicy runtime leaks initial horizon scheduler who
        ((sequence n).strategy who) (weight n) (nonnegative n) (atMostOne n)) site.1)
      ((bounds.canonicalRawPolicy runtime leaks initial horizon scheduler who
        (source.strategy who)) site.1) :=
  (runtime.reactiveNormalization leaks).split_strategy_converges (bounds.rawMenu runtime leaks)
    (bounds.rawMenu_recall runtime leaks) (bounds.rawMenu_closed runtime leaks)
    initial horizon scheduler sequence source converges weight nonnegative atMostOne
      vanishes who site

/-- Canonical raw policies preserve the complete projected continuation law
from every legal raw starting history. -/
theorem canonicalRaw_historyLaw
    (source : ∀ who, BehavioralPolicy
      ((bounds.menu runtime leaks).information initial horizon scheduler) who)
    (fuel : Nat)
    (current : ((bounds.rawMenu runtime leaks).protocol initial horizon scheduler).History) :
    (((bounds.rawMenu runtime leaks).information initial horizon scheduler).runBehavioralFrom
      (fun who => bounds.canonicalRawPolicy runtime leaks initial horizon scheduler who
        (source who)) fuel current).map
        ((runtime.reactiveNormalization leaks).history (bounds.rawMenu runtime leaks)
          (bounds.rawMenu_recall runtime leaks) initial horizon scheduler) =
      ((bounds.menu runtime leaks).information initial horizon scheduler).runBehavioralFrom
        source fuel ((runtime.reactiveNormalization leaks).history (bounds.rawMenu runtime leaks)
          (bounds.rawMenu_recall runtime leaks) initial horizon scheduler current) := by
  apply (runtime.reactiveNormalization leaks).runBehavioral_projection
    (bounds.rawMenu runtime leaks) (bounds.rawMenu_recall runtime leaks)
    initial horizon scheduler _ source _ fuel current
  intro who observed
  exact (runtime.reactiveNormalization leaks).canonicalPolicy_project (bounds.rawMenu runtime leaks)
    (bounds.rawMenu_recall runtime leaks) (bounds.rawMenu_closed runtime leaks)
    initial horizon scheduler who (source who) observed

/-- Alias perturbations change only private response names, at every finite
noise weight and every legal starting history. -/
theorem splitRaw_historyLaw
    (source : ∀ who, BehavioralPolicy
      ((bounds.menu runtime leaks).information initial horizon scheduler) who)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) (fuel : Nat)
    (current : ((bounds.rawMenu runtime leaks).protocol initial horizon scheduler).History) :
    (((bounds.rawMenu runtime leaks).information initial horizon scheduler).runBehavioralFrom
      (fun who => bounds.splitRawPolicy runtime leaks initial horizon scheduler who
        (source who) weight nonnegative atMostOne) fuel current).map
        ((runtime.reactiveNormalization leaks).history (bounds.rawMenu runtime leaks)
          (bounds.rawMenu_recall runtime leaks) initial horizon scheduler) =
      ((bounds.menu runtime leaks).information initial horizon scheduler).runBehavioralFrom
        source fuel ((runtime.reactiveNormalization leaks).history (bounds.rawMenu runtime leaks)
          (bounds.rawMenu_recall runtime leaks) initial horizon scheduler current) := by
  apply (runtime.reactiveNormalization leaks).runBehavioral_projection
    (bounds.rawMenu runtime leaks) (bounds.rawMenu_recall runtime leaks)
    initial horizon scheduler _ source _ fuel current
  intro who observed
  exact bounds.splitRawPolicy_project runtime leaks initial horizon scheduler who
    (source who) weight nonnegative atMostOne observed

/-- Native response bounds discharge every operational premise of the
consistency lift. Beliefs project correctly even at off-path raw sites. -/
theorem exists_canonicalRaw_consistent
    (source : BehavioralAssessment
      ((bounds.menu runtime leaks).information initial horizon scheduler))
    (consistent : source.IsSequentiallyConsistent
      ((bounds.menu runtime leaks).decisionInformationAntichain initial horizon scheduler)) :
    ∃ target : BehavioralAssessment
        ((bounds.rawMenu runtime leaks).information initial horizon scheduler),
      target.strategy = (fun who => bounds.canonicalRawPolicy runtime leaks
        initial horizon scheduler who (source.strategy who)) ∧
      target.IsSequentiallyConsistent
        ((bounds.rawMenu runtime leaks).decisionInformationAntichain initial horizon scheduler) ∧
      ∀ who (site : InformationSite
          ((bounds.rawMenu runtime leaks).information initial horizon scheduler) who),
        (target.belief who site).map
            ((runtime.reactiveNormalization leaks).informationHistory (bounds.rawMenu runtime leaks)
              (bounds.rawMenu_recall runtime leaks) initial horizon scheduler who site.1) =
          source.belief who ((runtime.reactiveNormalization leaks).site
            (bounds.rawMenu runtime leaks) (bounds.rawMenu_recall runtime leaks)
              initial horizon scheduler who site) :=
  (runtime.reactiveNormalization leaks).exists_canonical_consistent (bounds.rawMenu runtime leaks)
    (bounds.rawMenu_recall runtime leaks) (bounds.rawMenu_closed runtime leaks)
    initial horizon scheduler source consistent

/-- An SE of the complete normalized native menu remains an SE when every
bounded raw response alias is available. The source-language interpretation
of this native game is a separate obligation. -/
theorem exists_canonicalRaw_sequentialEquilibrium
    (source : BehavioralAssessment
      ((bounds.menu runtime leaks).information initial horizon scheduler))
    (payoff : Player → (runtime.reactiveApplication leaks).ProtocolState → ℝ)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((bounds.menu runtime leaks).decisionInformationAntichain initial horizon scheduler)
      (fun who site => source.continuationContext site
        (fun history => payoff who history.state) (2 * horizon + 1))) :
    ∃ target : BehavioralAssessment
        ((bounds.rawMenu runtime leaks).information initial horizon scheduler),
      target.strategy = (fun who => bounds.canonicalRawPolicy runtime leaks
        initial horizon scheduler who (source.strategy who)) ∧
      target.IsSequentialEquilibriumFor
        ((bounds.rawMenu runtime leaks).decisionInformationAntichain initial horizon scheduler)
        (fun who site => target.continuationContext site
          (fun history => payoff who ((runtime.reactiveNormalization leaks).state history.state))
          (2 * horizon + 1)) ∧
      (∀ who (site : InformationSite
          ((bounds.rawMenu runtime leaks).information initial horizon scheduler) who),
        (target.belief who site).map
            ((runtime.reactiveNormalization leaks).informationHistory (bounds.rawMenu runtime leaks)
              (bounds.rawMenu_recall runtime leaks) initial horizon scheduler who site.1) =
          source.belief who ((runtime.reactiveNormalization leaks).site
            (bounds.rawMenu runtime leaks) (bounds.rawMenu_recall runtime leaks)
              initial horizon scheduler who site)) ∧
      (((bounds.rawMenu runtime leaks).information initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).map
            (fun history => (runtime.reactiveNormalization leaks).state history.state) =
        (((bounds.menu runtime leaks).information initial horizon scheduler).runBehavioral
          source.strategy (2 * horizon + 1)).map
            GameTheory.Protocol.ExecutionProtocol.History.state :=
  (runtime.reactiveNormalization leaks).exists_canonical_sequentialEquilibrium
    (bounds.rawMenu runtime leaks) (bounds.rawMenu_recall runtime leaks)
    (bounds.rawMenu_closed runtime leaks) initial horizon scheduler source payoff equilibrium

end Vegas.EventGraphRuntime.MessageBounds
