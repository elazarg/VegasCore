/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalInitializedLawError
import Vegas.Pending.ReactiveInitialValues

/-! # Exact initialized full-history and perturbation contracts -/

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

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)
local notation "horizon" => ReservedEpoch.executionHorizon runtime

example
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
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    let scheduler := (ReservedEpoch.implementation runtime leaks
      (ReservedEpoch.packetCapacity runtime) prior).scheduler
    let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let sourceProfile := setup.proposalRecoveryNormalizedTrembledProfile
      0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
    ∃ joint : PMF ((State L setup.context × ReservedEpoch.Tape Player length) ×
        ((app).ProtocolState × setup.proposalRecoveryProtocol.History)),
      joint.map Prod.fst = setup.initialLaw.bind (fun theta => prior.map (Prod.mk theta)) ∧
      joint.map (fun result => result.2.1) =
        (app).finish initial horizon scheduler players none ∧
      joint.map (fun result => result.2.2) =
        setup.proposalRecoveryModel.runBehavioralTerminalFrom
          setup.proposalRecoveryProtocol_bounded.wellFoundedHistories sourceProfile
            setup.proposalRecoveryProtocol.initHistory ∧
      ∀ result ∈ joint.support,
        result.1.1 ∈ setup.initialLaw.support ∧ result.1.2 ∈ prior.support ∧
        ∃ (ending : (app).Control)
          (next : RecoverySourceWitness setup mode plan ending.execution.application),
          result.2.1 = some ending ∧ ending.execution.application.phases = [] ∧
          result.2.2 = ⟨_, setup.proposalRecoveryLiftTrace
            (nativeArchiveLabels setup
              (PhaseProposal.sourceArchive ending.execution.network.inputs))
                next.checkpoint.trace⟩ ∧
          setup.proposalRecoveryProtocol.terminal result.2.2.state ∧
          ending.execution.application.current.native.config.inputs = encodeInputs result.1.1 ∧
          (setup.protocolReadout (setup.commitRecoverySourceState result.2.2.state)).map
            (initialState setup.program) = some result.1.1 ∧
          result.2.2.state.map CommitRecoveryState.excluded =
            some ending.execution.application.current.excluded ∧
          phaseSourceReadout setup mode runtime leaks (some ending) =
            setup.protocolReadout (setup.commitRecoverySourceState result.2.2.state) ∧
          (fun who => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            (some ending) who) = fun who => setup.commitRecoveryPayoff utility excludedPayoff who
              ⟨result.2.2.state, setup.proposalRecoveryEraseTrace result.2.2.trace⟩ := by
  exact phaseProposalUnflagged_initialized_terminal_coupling setup mode runtime leaks bounds plan
    complete covered maximal initialValues values fullValues prior activationGap processingGap
      gaps margin capacity utility excludedPayoff

example
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
  exact phaseProposal_initialized_joint_withinTV setup mode runtime leaks bounds plan
    complete covered maximal initialValues values fullValues prior activationGap processingGap
      gaps margin capacity nativeRates waitingPositive waitingBelow slotsPositive nativeBadPositive
        nativeBadBelow omission omissionNonnegative omissionBounded
          sourceBad sourceBadNonnegative sourceBadBounded
            delivery deliveryNonnegative deliveryBounded utility excludedPayoff

end VegasTests
