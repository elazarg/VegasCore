/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceEquilibrium
import Vegas.Game.RevealServiceOrdinaryExtension
import Vegas.Game.RevealServiceDeposits

/-! # Source-to-raw sequential equilibrium preservation

For every initialized finite revelation sequence, one fixed bounded native
game preserves every source sequential equilibrium and its joint typed outcome
and payoff law. The native game admits all raw responses at the service's
activation opportunities. Deposits are determined by its finite payoff range
and a positive passive-observation coverage bound, before any equilibrium is
chosen. Withholding is a legal source choice and incurs no penalty.

The scope is the explicit revelation service: initial commitments are openable,
each source decision has its scheduled owner opportunity, and a distinct
indifferent reporter has reserved observation and inclusion opportunities.
This theorem does not remove those service assumptions or cover fresh source
commitments. Collection is represented by the terminal net utility; an escrow
or audit implementation must realize that payoff interpretation.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)
  (reveals : setup.program.RevealOnly)
  (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
  (admission : CommitmentInterface setup.program)
  [Finite (setup.executionProtocol admission).History]
  [∀ who (site : (setup.informationModel admission).InformationSite who),
    Fintype ((setup.informationModel admission).InformationHistory who site.1)]

include reveals observer openable in
/-- The game, response bound, observation rule and range-based deposits are
fixed before choosing the source equilibrium. Beliefs at all raw off-path
information sets satisfy the standard common-tremble consistency condition. -/
theorem source_raw_sequential_equilibrium_preserved
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (watcherZero : ∀ state, utility state watcher = 0)
    (probability : Player → ℝ)
    (positive : ∀ who, who ≠ watcher → 0 < probability who)
    (sampling : ∀ owner, owner ≠ watcher →
      ∀ pending (message : Message Player (WitnessedPacket (graph setup))), message ∈ pending →
        message.id.1 = owner → probability owner ≤ (leaks watcher pending).probOf
          {selected | message.id ∈ selected})
    (source : (setup.informationModel admission).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor (setup.decision_antichain admission)
      (fun who site => source.continuationContext site
        (fun final => (setup.protocolReadout final.state).elim 0 (fun state => utility state who))
        (instructionCount setup.program + 1))) :
    let extended := bounds.withInitialValues (initialLaw setup)
    let base := baseUtility setup leaks utility
    let deposit := rangeDeposit setup leaks extended watcher base probability
    let model := rawInformation setup leaks extended watcher
    ∃ target : model.BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((extended.rawMenu (runtime setup) leaks).decisionInformationAntichain
          (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher))
        (fun who site => target.continuationContext site
          (fun final => netUtility setup leaks watcher base deposit final.state who)
          (2 * horizon setup watcher + 1)) ∧
      (model.runBehavioral target.strategy (2 * horizon setup watcher + 1)).map
          (fun final => (sourceReadout setup leaks final.state,
            netUtility setup leaks watcher base deposit final.state)) =
        ((setup.informationModel admission).runBehavioral source.strategy
          (instructionCount setup.program + 1)).map
            (fun final => (setup.protocolReadout final.state,
              fun who => (setup.protocolReadout final.state).elim 0
                (fun state => utility state who))) := by
  classical
  intro extended base deposit model
  obtain ⟨retained, _compiled, retainedSE, sourceLaw⟩ :=
    source_sequential_equilibrium_preserved setup leaks bounds watcher reveals observer openable
      admission utility watcherZero source equilibrium
  have retainedNet := (sequential_equilibrium_net_iff setup leaks extended watcher reveals
    observer openable retained _ base deposit).mpr retainedSE
  obtain ⟨target, targetSE, targetLaw⟩ := ordinary_raw_equilibrium_extends setup leaks extended
    watcher reveals observer openable base deposit
    (historyPayoffLower setup leaks extended watcher base)
    (historyPayoffUpper setup leaks extended watcher base) probability
    (rangeDeposit_nonnegative setup leaks extended watcher base probability positive)
    (retained_historyPayoffLower_le setup leaks extended watcher base)
    (le_historyPayoffUpper setup leaks extended watcher base)
    (rangeDeposit_sufficient setup leaks extended watcher base probability positive)
    sampling (sourceReadout setup leaks) (sourceReadout_normalization setup leaks)
    (baseUtility_normalization setup leaks utility)
    (baseUtility_watcher setup leaks utility watcher watcherZero) retained retainedNet
  refine ⟨target, targetSE, targetLaw.trans ?_⟩
  trans ((information setup leaks extended watcher).runBehavioral retained.strategy
    (2 * horizon setup watcher + 1)).map
      (fun final => (sourceReadout setup leaks final.state, base final.state))
  · apply FinDist.map_congr_of_eq_on_support
    intro final supported
    congr 1
    funext who
    exact netUtility_clean setup leaks watcher who base deposit final.state
      (continuation_clean setup leaks extended watcher reveals observer openable
        retained.strategy _ final (2 * horizon setup watcher + 1) (Nat.sub_le ..) supported who)
  · exact sourceLaw

end Vegas.SourceProgram.RevealService
