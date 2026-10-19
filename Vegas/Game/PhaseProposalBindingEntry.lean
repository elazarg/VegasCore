/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseEntryOwnRecall
import Vegas.Game.PhaseCountServiceForeignWord
import Vegas.Game.PhaseProposalHistory

/-! # The actual installed binding entry with its chosen source checkpoint -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Extract the actual first installation of the currently addressed phase.
Its checkpoint and complete proposal archive belong to that SAME prefix.
The original inputs, pending envelopes and complete own recall are retained. -/
theorem phaseProposal_binding_entry_checkpoint
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control))
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : control.execution.application.phases.head? = some phase) :
    ∃ (entry : (phaseApplication runtime leaks).Control)
      (entryTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).Trace (some entry))
      (witness : RecoverySourceWitness setup mode plan entry.execution.application),
      TracePrefix entryTrace trace ∧
      entry.execution.application.attempt = control.execution.application.attempt ∧
      entry.execution.application.phases.head? = some phase ∧
      entry.actor = none ∧
      entry.execution.application.entry.excluded = entry.execution.application.current.excluded ∧
      witness.checkpoint.ArchivedProposals entry.execution.network.inputs ∧
      ∀ who, ∀ record ∈ entry.execution.recall who,
        record.beforeView.application.2.attempt ≠ entry.execution.application.attempt := by
  let inputs := setup.initialLaw.map encodeInputs
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let counted : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some control) := trace
  obtain ⟨entry, entryTrace, retained, same, idle, excluded, fresh⟩ :=
    phase_attempt_installed_prefix runtime leaks (PhaseCount.onePacketMenu runtime leaks bounds)
      plan inputs horizon scheduler control counted
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
      scheduler entryTrace)
  have metadata := phase_attempt_metadata_of_prefix runtime leaks
    (PhaseCount.onePacketMenu runtime leaks bounds) initial initialized horizon scheduler entry
      control entryTrace counted retained ordered same
  have entryInstalled : entry.execution.application.phases.head? = some phase :=
    (congrArg (fun phases => phases.head?) (congrArg Prod.fst metadata)).trans installed
  have actualEntry : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some entry) := by
    dsimp only [initial, inputs] at entryTrace
    rw [PMF.map_comp] at entryTrace
    exact entryTrace
  obtain ⟨witness, archived⟩ := recoverySourceCheckpoint_proposalArchive_history setup mode runtime
    leaks bounds plan maximal horizon scheduler actualEntry
  exact ⟨entry, entryTrace, witness, retained, same, entryInstalled, idle, excluded,
    archived, fresh⟩

end Vegas
