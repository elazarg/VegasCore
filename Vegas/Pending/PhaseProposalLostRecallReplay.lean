/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCountMenu
import Interaction.ReactiveOwnPlay

/-! # Actual transitions after replacing a lost private preparation

Only the designated sender's inert private alias is projected away. Both
endpoints remain genuine executions; the physical network, scheduler recall
and every other player's complete input are retained.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.HiddenSwap

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

local notation "app" => phaseApplication runtime leaks

/-- Actual counted traces read their complete own-action word from literal recall. -/
theorem phase_trace_ownPlay [Fintype Player]
    (bounds : MessageBounds graph) (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some control)) (who : Player) :
    ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon scheduler).ownPlay
        who trace = (app).recallOwnPlay (control.execution.recall who) := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  change (menu.signals initial horizon scheduler).ownPlay who trace = _
  rw [← menu.ownPlay_toRawTrace initial horizon scheduler who trace, (app).trace_ownPlay]
  rfl

end Vegas.EventGraphRuntime.HiddenSwap
