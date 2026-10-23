/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalOwnBindingFailure
import Vegas.Game.PhaseProposalHistory
import Vegas.Game.PhaseProposalSavedDebt

/-! # Observable saved binding failures force actual native checkpoint debt

The selector reads the player's ordinary view. Its semantic consequence uses
the SAME chosen archive-aligned checkpoint from the actual counted history.
Current-attempt failures are retained as a separate, cancelable case.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)

/-- An observed saved failure gives this actual chosen checkpoint's debt.
The actual current store may contain further failures or pending packets. -/
theorem RecoverySourceWitness.checkpointDebt_of_observed_saved_binding
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (witness : RecoverySourceWitness setup mode plan control.execution.application)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (failed : phaseProposalSavedBindingFailure setup mode runtime leaks who event
      (control.execution.observe app who)) : witness.CheckpointDebt who := by
  have stored := (phaseProposalSavedBindingFailure_iff_of_seed_request setup mode runtime leaks
    plan maximal horizon scheduler trace witness.checkpoint witness.aligned who event payload
      binding request).mp failed
  exact Or.inr (Or.inr stored)

/-- At every actual counted callback the observable selector supplies actual
saved debt. No checkpoint, archive or source-counterpart premise is supplied. -/
theorem phaseProposalSavedBindingFailure_checkpointDebt
    (bounds : MessageBounds (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      initial horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (failed : phaseProposalSavedBindingFailure setup mode runtime leaks who event
      (control.execution.observe app who)) :
    PhaseCheckpointDebt setup mode plan who control.execution.application := by
  obtain ⟨witness, _archive⟩ := recoverySourceCheckpoint_proposalArchive_history setup mode runtime
    leaks bounds plan maximal horizon scheduler trace
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler
    trace
  exact ⟨witness, RecoverySourceWitness.checkpointDebt_of_observed_saved_binding setup mode runtime
    leaks plan maximal horizon scheduler raw witness who event payload binding request failed⟩

end Vegas
