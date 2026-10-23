/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

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
  (initial : PMF (State graph)) (horizon : Nat)
  (scheduler : (runtime.reactiveApplication leaks).Scheduler)

def canonicalRawPolicy (who : Player)
    (source : BehavioralPolicy
      ((bounds.menu runtime leaks).information initial horizon scheduler) who) :
    ((bounds.rawMenu runtime leaks).information initial horizon scheduler).BehavioralPolicy who :=
  (runtime.reactiveNormalization leaks).canonicalPolicy (bounds.rawMenu runtime leaks)
    (bounds.rawMenu_recall runtime leaks) (bounds.rawMenu_closed runtime leaks)
    initial horizon scheduler who source

/-- An SE of the complete normalized native menu remains an SE when every
bounded raw response alias is available. The source-language interpretation
of this native game is a separate obligation. -/
theorem exists_canonicalRaw_sequentialEquilibrium
    [(runtime.reactiveApplication leaks).FiniteNature initial scheduler]
    (source : BehavioralAssessment
      ((bounds.menu runtime leaks).information initial horizon scheduler))
    (payoff : Player → (runtime.reactiveApplication leaks).ProtocolState → ℝ)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((bounds.menu runtime leaks).decisionInformationAntichain initial horizon scheduler)
      (fun who site => source.truncatedContinuationContext site
        (fun history => payoff who history.state) (2 * horizon + 1))) :
    ∃ target : BehavioralAssessment
        ((bounds.rawMenu runtime leaks).information initial horizon scheduler),
      target.strategy = (fun who => bounds.canonicalRawPolicy runtime leaks
        initial horizon scheduler who (source.strategy who)) ∧
      target.IsSequentialEquilibriumFor
        ((bounds.rawMenu runtime leaks).decisionInformationAntichain initial horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
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
