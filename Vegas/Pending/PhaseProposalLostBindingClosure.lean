/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalLostBinding
import Vegas.Pending.PhaseAttemptReceiptSnapshot

/-! # Unaccepted fields in the original primitive closing result

The actual inclusion or environment witness precedes normalization. Its
accepted-table projection links a lost binding to every earlier owned callback.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability
  GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The genuine primitive result retains every previously accepted handle,
even when its actual normalized endpoint has restored an older checkpoint. -/
theorem PhaseClosingEffect.accepted_preserved
    {before after : (app).Execution} {current : RecoveryState graph}
    (effect : PhaseClosingEffect runtime leaks before after current)
    (field : graph.Field) (candidate : Handle graph)
    (accepted : before.application.current.native.accepted field = some candidate) :
    current.native.accepted field = some candidate := by
  rcases effect with ⟨_id, message, native, _found, _reached, handled, rfl⟩ |
    ⟨command, native, _reached, supported, rfl⟩
  · change native.accepted field = some candidate
    exact handle_preserves_accepted runtime before.application.current.native native
      ⟨message.id, message.payload.packet.call⟩ handled field candidate accepted
  · change native.accepted field = some candidate
    rw [(environmentStep_tables runtime before.application.current.native native command
      supported).1]
    exact accepted

end Vegas.EventGraphRuntime
