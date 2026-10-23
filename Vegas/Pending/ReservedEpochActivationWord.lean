/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochActiveSlot
import Interaction.ReactiveResponseAccounting

/-! # Exogenous owner response ordinals in actual reserved-service histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem command_actor_view_independent {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (cursor : Nat) (left right : (app).EnvironmentView) :
    (command runtime leaks packetBudget tape cursor left).actor? app =
      (command runtime leaks packetBudget tape cursor right).actor? app := by
  dsimp only [command]
  split_ifs <;> first
    | rfl
    | rw [process_actor_none, process_actor_none]
    | rw [sample_actor_none, sample_actor_none]

end Vegas.EventGraphRuntime.ReservedEpoch
