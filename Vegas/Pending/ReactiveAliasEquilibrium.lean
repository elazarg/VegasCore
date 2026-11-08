/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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
  (bounds : MessageBounds graph) (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : PMF (State graph)) (horizon : Nat)
  (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)

def canonicalRawPolicy (who : Player)
    (source : BehavioralPolicy
      ((bounds.menu timeouts leaks).information initial horizon scheduler) who) :
    ((bounds.rawMenu timeouts leaks).information initial horizon scheduler).BehavioralPolicy who :=
  ((reactiveNormalization timeouts) leaks).canonicalPolicy (bounds.rawMenu timeouts leaks)
    (bounds.rawMenu_recall timeouts leaks) (bounds.rawMenu_closed timeouts leaks)
    initial horizon scheduler who source

/-- An SE of the complete normalized native menu remains an SE when every
bounded raw response alias is available. The source-language interpretation
of this native game is a separate obligation. -/
theorem exists_canonicalRaw_sequentialEquilibrium
    [((reactiveApplication timeouts) leaks).FiniteNature initial scheduler]
    (source : BehavioralAssessment
      ((bounds.menu timeouts leaks).information initial horizon scheduler))
    (payoff : Player → ((reactiveApplication timeouts) leaks).ProtocolState → ℝ)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((bounds.menu timeouts leaks).decisionInformationAntichain initial horizon scheduler)
      (fun who site => source.truncatedContinuationContext site
        (fun history => payoff who history.state) (2 * horizon + 1))) :
    ∃ target : BehavioralAssessment
        ((bounds.rawMenu timeouts leaks).information initial horizon scheduler),
      target.strategy = (fun who => bounds.canonicalRawPolicy timeouts leaks
        initial horizon scheduler who (source.strategy who)) ∧
      target.IsSequentialEquilibriumFor
        ((bounds.rawMenu timeouts leaks).decisionInformationAntichain initial horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => payoff who (((reactiveNormalization timeouts) leaks).state history.state))
          (2 * horizon + 1)) ∧
      (∀ who (site : InformationSite
          ((bounds.rawMenu timeouts leaks).information initial horizon scheduler) who),
        (target.belief who site).map
            (((reactiveNormalization timeouts) leaks).informationHistory (bounds.rawMenu timeouts
              leaks)
              (bounds.rawMenu_recall timeouts leaks) initial horizon scheduler who site.1) =
          source.belief who (((reactiveNormalization timeouts) leaks).site
            (bounds.rawMenu timeouts leaks) (bounds.rawMenu_recall timeouts leaks)
              initial horizon scheduler who site)) ∧
      (((bounds.rawMenu timeouts leaks).information initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).map
            (fun history => ((reactiveNormalization timeouts) leaks).state history.state) =
        (((bounds.menu timeouts leaks).information initial horizon scheduler).runBehavioral
          source.strategy (2 * horizon + 1)).map
            GameTheory.Protocol.ExecutionProtocol.History.state :=
  ((reactiveNormalization timeouts) leaks).exists_canonical_sequentialEquilibrium
    (bounds.rawMenu timeouts leaks) (bounds.rawMenu_recall timeouts leaks)
    (bounds.rawMenu_closed timeouts leaks) initial horizon scheduler source payoff equilibrium

end Vegas.EventGraphRuntime.MessageBounds
