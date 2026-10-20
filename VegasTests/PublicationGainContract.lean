/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalPublicationGain

/-! # Publication gain at the original full native information -/

noncomputable section

namespace VegasTests

open Vegas SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  {tapeLength : Nat} (prior : PMF (ReservedEpoch.Tape Player tapeLength))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)
local notation "horizon" => ReservedEpoch.executionHorizon runtime
local notation "scheduler" => ReactiveApplication.SchedulerImplementation.scheduler
  (ReservedEpoch.implementation runtime leaks (ReservedEpoch.packetCapacity runtime) prior)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

open Classical in
example
    [Fintype (E).History]
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (wellFormed : setup.WellFormed)
    (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support,
      tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
        activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1)
      (fun _ => processingGap + 1))
    (capacity : horizon ≤ bounds.candidateCount)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (rates : PhaseProposalRates)
    (waitingPositive : 0 < rates.waiting.val)
    (waitingBelow : rates.waiting.val < 1)
    (slotsPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val)
    (badBelow : rates.badPreparation.val < 1)
    (assessment : (N).BehavioralAssessment)
    (prescribed : assessment.strategy =
      phaseProposalReferenceStrategy setup mode runtime leaks bounds plan
        initial horizon scheduler values rates)
    (who : Player) (site : (N).InformationSite who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (information : site.1 = some (past, view))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (publication : (serviceGraph setup mode).outputLayout event = .publication payload)
    (requested : PhaseRuntimeState.requests view.application.2 who
      ⟨view.application.2.attempt, event⟩)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (utilityBound : ∀ terminal owner, |utility terminal owner| ≤ bound)
    (excludedBound : |excludedPayoff who| ≤ bound)
    (defaultFloor : excludedPayoff who ≤ 0)
    (terminalFloor : ∀ terminal, excludedPayoff who ≤ utility terminal who)
    (law : PMF ((N).Choice who site.1)) :
    let foreignPosterior :=
      ∑ history : (N).InformationHistory who site.1 with
        (∃ owner : Player, who ≠ owner ∧
          PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds
            initial horizon scheduler owner history.val),
        (assessment.belief who site history).toReal
    (N).localGain (2 * horizon + 1) (fun history => history.state)
      (phaseExclusionBase setup mode runtime leaks utility excludedPayoff)
        assessment site law ≤
      (2 * bound) * (foreignPosterior +
        (2 * (Fintype.card Player * (2 * horizon + 1) : Nat) + 1) * rates.flagBound) := by
  exact Vegas.phaseProposal_publication_gain_le setup mode runtime leaks bounds plan prior
    complete covered maximal wellFormed activationGap processingGap gaps margin capacity values
      fullValues rates waitingPositive waitingBelow slotsPositive badPositive badBelow assessment
        prescribed who site past view information event payload publication requested utility
          excludedPayoff bound nonnegative utilityBound excludedBound defaultFloor terminalFloor law

end VegasTests
