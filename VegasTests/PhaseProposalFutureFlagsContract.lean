/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalNativeFutureFlags

/-! # Literal current-law gain-error contract -/

noncomputable section

namespace VegasTests

open Vegas Vegas.SourceProgram Vegas.EventGraph Vegas.EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (complete : leaks = MessageNetwork.completePendingObservation)
  (covered : bounds.CoversOutputValues)
  (maximal : plan.phases.IsChain fun first last =>
    first.kind ≠ last.kind ∨ first.kind = .sample)
  (values : ∀ who (key : setup.ProposalRecoveryComponent who),
    PMF (setup.CommitRecoveryValueChoice who key.1))
  (fullValues : ∀ who key, FullSupport (values who key))
  (rates : PhaseProposalRates)
  (waitingPositive : 0 < rates.waiting.val) (waitingBelow : rates.waiting.val < 1)
  (slotsPositive : 0 < rates.slots.val)
  (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan)
  (PMF.map encodeInputs setup.initialLaw)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds)
  (PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw))
    horizon scheduler
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds)
  (PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw))
    horizon scheduler
local notation "clean" => fun who =>
  ReactiveApplication.ResponseMenu.restrictPolicy (PhaseCount.onePacketMenu runtime leaks bounds)
    (PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw))
      horizon scheduler who
  (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who)
local notation "noisy" => phaseProposalReferenceStrategy setup mode runtime leaks bounds plan
  initial horizon scheduler values rates

include complete covered maximal fullValues waitingPositive waitingBelow slotsPositive
  badPositive badBelow

example
    (remaining : Nat) (who : Player) (execution : (app).Execution)
    (trace : (E).Trace (some ⟨remaining, some who, execution⟩))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (utilityBound : ∀ terminal owner, |utility terminal owner| ≤ bound)
    (excludedBound : |excludedPayoff who| ≤ bound) :
    let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
    ∃ kernel : (app).Action → PMF (E).History,
      (∀ profile : ∀ owner, (N).BehavioralPolicy owner,
        (N).runBehavioralFrom profile 1 ⟨some ⟨remaining, some who, execution⟩, trace⟩ =
          ((menu).decodeProfile initial horizon scheduler profile who (execution.recall who)
            (execution.observe app who)).bind kernel) ∧
      let payoff := fun final : (E).History => phaseExclusionBase setup mode runtime leaks utility
        excludedPayoff final.state who
      let cleanValue := fun law : PMF (app).Action =>
        expect ((law.bind kernel).bind fun history =>
          (N).runBehavioralTerminalFrom certificate clean history) payoff
      let noisyValue := fun law : PMF (app).Action =>
        expect ((law.bind kernel).bind fun history =>
          (N).runBehavioralTerminalFrom certificate noisy history) payoff
      let referenceClean := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan
        values who (execution.recall who) (execution.observe app who)
      let referenceNoisy := phaseProposalReferencePolicy setup mode runtime leaks bounds plan
        values rates who (execution.recall who) (execution.observe app who)
      ∀ law : PMF (app).Action,
        (noisyValue law - noisyValue referenceNoisy) -
            (cleanValue law - cleanValue referenceClean) ≤
          (2 * (Fintype.card Player * (2 * horizon + 1) : Nat) + 1) *
            rates.flagBound * (2 * bound) := by
  exact phaseProposal_current_gain_flag_error setup mode runtime leaks bounds plan complete covered
    maximal values fullValues rates waitingPositive waitingBelow slotsPositive badPositive badBelow
      horizon scheduler remaining who execution trace utility excludedPayoff bound nonnegative
        utilityBound excludedBound

end VegasTests
