/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochPublicationComparison

/-! # Full contract of the actual paired publication boundary -/

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

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)

example
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (remaining : Nat) (active : (app).Execution) (actor : Player)
    (material : WitnessedSubmission graph)
    (activeTrace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, some actor, active⟩))
    (offered : (⟨some material⟩ : (app).Action) ∈ (menu).actions actor
      (active.recall actor) (active.observe app actor))
    (phase : RuntimePhase graph) (installed : phase ∈ active.application.phases.head?)
    (kind : phase.kind = .reveal)
    (checkpoint : RecoverySourceCheckpoint setup mode active.application)
    (proper : ∀ who, who ∉ active.application.current.excluded →
      checkpoint.source.BindingsHoldValues who) :
    PairedPublicationBoundary setup mode runtime leaks bounds plan values tape remaining active
      actor material activeTrace phase checkpoint := by
  exact phaseProposalUnflagged_paired_publication_boundary setup mode runtime leaks bounds plan
    coveredValues maximal values tape activationGap processingGap gaps margin remaining active actor
      material activeTrace offered phase installed kind checkpoint proper

end VegasTests
