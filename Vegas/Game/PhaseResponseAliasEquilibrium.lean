/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveAliasEquilibrium
import Vegas.Pending.PhaseResponseAliases

/-! # Sequential equilibrium with private counted phase response aliases

Every equilibrium of the actual normalized counted menu extends to the counted
menu containing all bounded private response aliases. Beliefs project exactly
at every decision site, and initialized play preserves the full normalized
protocol-state law. Payoff invariance removes normalization from the target
utility; no source-language or recovery-runtime correspondence is assumed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (initial : PMF (PhaseRuntimeState graph)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "normal" => normalization runtime leaks
local notation "raw" => onePacketMenu runtime leaks bounds
local notation "effective" =>
  ReactiveApplication.SubmissionNormalization.menu (normalization runtime leaks)
    (onePacketMenu runtime leaks bounds)

/-- The actual physical alias refinement preserves sequential rationality,
consistency, all decision-site projected beliefs and normalized full-state law. -/
theorem onePacket_alias_sequentialEquilibrium [(app).FiniteNature initial scheduler]
    (source : ((effective).information initial horizon scheduler).BehavioralAssessment)
    (payoff : Player → (app).ProtocolState → ℝ)
    (normalized : ∀ who state, payoff who ((normal).state state) = payoff who state)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((effective).decisionInformationAntichain initial horizon scheduler)
      (fun who site => source.truncatedContinuationContext site
        (fun history => payoff who history.state) (2 * horizon + 1))) :
    ∃ target : ((raw).information initial horizon scheduler).BehavioralAssessment,
      target.strategy = (fun who => (normal).canonicalPolicy (raw)
        (onePacketMenu_recall runtime leaks bounds) (onePacketMenu_closed runtime leaks bounds)
        initial horizon scheduler who (source.strategy who)) ∧
      target.IsSequentialEquilibriumFor
        ((raw).decisionInformationAntichain initial horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => payoff who history.state) (2 * horizon + 1)) ∧
      (∀ who (site : ((raw).information initial horizon scheduler).InformationSite who),
        (target.belief who site).map
            ((normal).informationHistory (raw) (onePacketMenu_recall runtime leaks bounds)
              initial horizon scheduler who site.1) =
          source.belief who ((normal).site (raw) (onePacketMenu_recall runtime leaks bounds)
            initial horizon scheduler who site)) ∧
      (((raw).information initial horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).map (fun history => (normal).state history.state) =
        (((effective).information initial horizon scheduler).runBehavioral source.strategy
          (2 * horizon + 1)).map History.state := by
  obtain ⟨target, strategy, sequential, beliefs, laws⟩ :=
    (normal).exists_canonical_sequentialEquilibrium (raw)
      (onePacketMenu_recall runtime leaks bounds) (onePacketMenu_closed runtime leaks bounds)
      initial horizon scheduler source payoff equilibrium
  refine ⟨target, strategy, ?_, beliefs, laws⟩
  simpa only [normalized] using sequential

end Vegas.EventGraphRuntime.PhaseCount
