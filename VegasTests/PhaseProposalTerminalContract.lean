/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalFreshTerminalCoupling

/-! # Complete ordinary native and source terminal-history coupling contract -/

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

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "graph" => serviceGraph setup mode
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)
local notation "horizon" => ReservedEpoch.executionHorizon runtime

example
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : horizon ≤ bounds.candidateCount)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (anchor : (app).Control) (idle : anchor.actor = none)
    (anchorTrace : ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some anchor))
    (entryExcluded : anchor.execution.application.entry.excluded =
      anchor.execution.application.current.excluded)
    (fresh : ∀ who, ∀ record ∈ anchor.execution.recall who,
      record.beforeView.application.2.attempt ≠ anchor.execution.application.attempt)
    (witness : RecoverySourceWitness setup mode plan anchor.execution.application)
    (archived : witness.checkpoint.ArchivedProposals anchor.execution.network.inputs)
    (proper : ∀ who, who ∉ anchor.execution.application.current.excluded →
      witness.checkpoint.source.BindingsHoldValues who) :
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let model := (menu).information initial horizon scheduler
    let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who
      (ReactiveApplication.anchoredPolicy anchor.execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    let sourceProfile := setup.proposalRecoveryNormalizedTrembledProfile
      0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
    let sourceCertificate := setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
    let start : setup.proposalRecoveryProtocol.History :=
      ⟨_, setup.proposalRecoveryLiftTrace
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive anchor.execution.network.inputs))
          witness.checkpoint.trace⟩
    ∃ joint : PMF (((menu).protocol initial horizon scheduler).History ×
        setup.proposalRecoveryProtocol.History),
      joint.map Prod.fst = model.runBehavioralTerminalFrom certificate profile
        ⟨some anchor, anchorTrace⟩ ∧
      joint.map Prod.snd = setup.proposalRecoveryModel.runBehavioralTerminalFrom
        sourceCertificate sourceProfile start ∧
      ∀ pair ∈ joint.support,
        ∃ (ending : (app).Control)
          (next : RecoverySourceWitness setup mode plan ending.execution.application),
          pair.1.state = some ending ∧ ending.execution.application.phases = [] ∧
          TracePrefix anchorTrace pair.1.trace ∧ TracePrefix start.trace pair.2.trace ∧
          pair.2 = ⟨_, setup.proposalRecoveryLiftTrace
            (nativeArchiveLabels setup
              (PhaseProposal.sourceArchive ending.execution.network.inputs))
                next.checkpoint.trace⟩ ∧
          setup.proposalRecoveryProtocol.terminal pair.2.state ∧
          ending.execution.application.current.excluded =
            ending.execution.application.entry.excluded ∧
          pair.2.state.map CommitRecoveryState.excluded =
            some ending.execution.application.current.excluded ∧
          (∃ original ∈ setup.initialLaw.support,
            ending.execution.application.current.native.config.inputs = encodeInputs original ∧
            (setup.protocolReadout (setup.commitRecoverySourceState pair.2.state)).map
              (initialState setup.program) = some original) ∧
          phaseSourceReadout setup mode runtime leaks (some ending) =
            setup.protocolReadout (setup.commitRecoverySourceState pair.2.state) ∧
          (fun who => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            (some ending) who) = fun who => setup.commitRecoveryPayoff utility excludedPayoff who
              ⟨pair.2.state, setup.proposalRecoveryEraseTrace pair.2.trace⟩ :=
  RecoverySourceWitness.ordinary_fresh_terminal_coupling setup mode runtime leaks bounds plan
    complete covered maximal values fullValues tape activationGap processingGap gaps margin capacity
      utility excludedPayoff anchor idle anchorTrace entryExcluded fresh witness archived proper

end VegasTests
