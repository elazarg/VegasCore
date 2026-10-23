/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalInitializedTerminal
import Vegas.Game.PhaseProposalNativeFutureFlags
import Vegas.Game.ProposalRecoveryFutureFlags

/-! # Initialized joint law error with separate native and source flags -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)
local notation "horizon" => ReservedEpoch.executionHorizon runtime

/-- The actual initialized reference and prescribed source sequence retain
the same original setup and domain laws. Their entire joint outcome error has
separate native and source flag bounds and no information-reach denominator. -/
theorem phaseProposal_initialized_joint_withinTV
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (initialValues : ∀ theta ∈ setup.initialLaw.support,
      ∀ {name : VarId} {owner : Player} {payload : L.Ty}
        (cell : HasVar setup.context name (.commitment owner payload)),
        ∃ value, theta.get cell = .success value)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (prior : PMF (ReservedEpoch.Tape Player length))
    (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support,
      tape.BoundedGaps (ReservedEpoch.completionCycles runtime) activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : horizon ≤ bounds.candidateCount)
    (nativeRates : PhaseProposalRates)
    (waitingPositive : 0 < nativeRates.waiting.val) (waitingBelow : nativeRates.waiting.val < 1)
    (slotsPositive : 0 < nativeRates.slots.val)
    (nativeBadPositive : 0 < nativeRates.badPreparation.val)
    (nativeBadBelow : nativeRates.badPreparation.val < 1)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (sourceBad : ℝ) (sourceBadNonnegative : 0 ≤ sourceBad) (sourceBadBounded : sourceBad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    let scheduler := (ReservedEpoch.implementation runtime leaks
      (ReservedEpoch.packetCapacity runtime) prior).scheduler
    let nativeReadout := fun state : (app).ProtocolState =>
      ((phaseSourceReadout setup mode runtime leaks state).map (initialState setup.program),
        state.map (fun current => current.execution.application.current.excluded),
        phaseSourceReadout setup mode runtime leaks state,
        fun who => phaseExclusionBase setup mode runtime leaks utility excludedPayoff state who)
    let sourceReadout := fun history : setup.proposalRecoveryProtocol.History =>
      ((setup.protocolReadout (setup.commitRecoverySourceState history.state)).map
          (initialState setup.program),
        history.state.map CommitRecoveryState.excluded,
        setup.protocolReadout (setup.commitRecoverySourceState history.state),
        fun who => setup.commitRecoveryPayoff utility excludedPayoff who
          ⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩)
    PMF.WithinTV
      (((Fintype.card Player * (2 * horizon + 1) : Nat) : ℝ) * nativeRates.flagBound +
        ((Fintype.card Player *
          ((Fintype.card Player + 1) * (instructionCount setup.program + 1)) : Nat) : ℝ) *
            (omission + sourceBad + delivery))
      (((app).finish initial horizon scheduler
        (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values nativeRates)
          none).map nativeReadout)
      ((setup.proposalRecoveryModel.runBehavioralTerminalFrom
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
          (setup.proposalRecoveryNormalizedTrembledProfile
            omission omissionNonnegative omissionBounded
            sourceBad sourceBadNonnegative sourceBadBounded
            delivery deliveryNonnegative deliveryBounded values)
              setup.proposalRecoveryProtocol.initHistory).map sourceReadout) := by
  intro scheduler nativeReadout sourceReadout
  have nativeClose := (phaseProposal_finish_future_flags_withinTV setup mode runtime leaks bounds
    plan complete covered maximal values fullValues nativeRates waitingPositive waitingBelow
      slotsPositive nativeBadPositive nativeBadBelow horizon scheduler
        ((menu).protocol initial horizon scheduler).initHistory).map nativeReadout
  change PMF.WithinTV
    (((Fintype.card Player * (2 * horizon + 1) : Nat) : ℝ) * nativeRates.flagBound)
    (((app).finish initial horizon scheduler
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) none).map
        nativeReadout)
    (((app).finish initial horizon scheduler
      (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values nativeRates)
        none).map nativeReadout) at nativeClose
  have ordinary := phaseProposalUnflagged_initialized_joint_readout setup mode runtime leaks
    bounds plan complete covered maximal initialValues values fullValues prior activationGap
      processingGap gaps margin capacity utility excludedPayoff
  change
    ((app).finish initial horizon scheduler
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) none).map
        nativeReadout =
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
          (setup.proposalRecoveryNormalizedTrembledProfile
            0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
              setup.proposalRecoveryProtocol.initHistory).map sourceReadout at ordinary
  rw [ordinary] at nativeClose
  have sourceClose := setup.proposalRecovery_future_flags_withinTV
    omission omissionNonnegative omissionBounded sourceBad sourceBadNonnegative sourceBadBounded
      delivery deliveryNonnegative deliveryBounded values
        setup.proposalRecoveryProtocol.initHistory
          ((Fintype.card Player + 1) * (instructionCount setup.program + 1))
  have sourceTerminal : PMF.WithinTV
      (((Fintype.card Player *
          ((Fintype.card Player + 1) * (instructionCount setup.program + 1)) : Nat) : ℝ) *
        (omission + sourceBad + delivery))
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
          (setup.proposalRecoveryNormalizedTrembledProfile
            0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
              setup.proposalRecoveryProtocol.initHistory)
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
          (setup.proposalRecoveryNormalizedTrembledProfile
            omission omissionNonnegative omissionBounded
            sourceBad sourceBadNonnegative sourceBadBounded
            delivery deliveryNonnegative deliveryBounded values)
              setup.proposalRecoveryProtocol.initHistory) := by
    simpa only [InformationModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
      setup.proposalRecoveryModel setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
        setup.proposalRecoveryProtocol_bounded] using sourceClose
  exact nativeClose.symm.trans (sourceTerminal.map sourceReadout)

end Vegas
