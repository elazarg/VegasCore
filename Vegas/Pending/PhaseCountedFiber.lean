/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCountedTrace
import Interaction.ReactiveCompleteInput

/-! # Actual counted representatives throughout a complete native input fiber -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks
local notation "raw" => rawMenu runtime leaks bounds
local notation "counted" => onePacketMenu runtime leaks bounds

/-- Complete packet observation determines count permission on every signed
input. Every raw history sharing a counted representative's full decision input
therefore admits a counted trace at that identical physical control. -/
theorem onePacketMenu_trace_of_completeInput
    (complete : leaks = MessageNetwork.completePendingObservation)
    (initial : PMF (app).State) (horizon : Nat)
    (sourceScheduler targetScheduler : (app).Scheduler) (source target : (app).Control)
    (sourceTrace : ((counted).protocol initial horizon sourceScheduler).Trace (some source))
    (targetTrace : ((raw).protocol initial horizon targetScheduler).Trace (some target))
    (owner : Player) (sourceActive : source.actor = some owner)
    (targetActive : target.actor = some owner)
    (recalled : source.execution.recall owner = target.execution.recall owner)
    (observed : source.execution.observe app owner = target.execution.observe app owner) :
    Nonempty (((counted).protocol initial horizon targetScheduler).Trace (some target)) := by
  have sourceRaw := (counted).toRawTrace initial horizon sourceScheduler sourceTrace
  have targetRaw := (raw).toRawTrace initial horizon targetScheduler targetTrace
  have inputs := (app).complete_decision_inputs_congr complete initial horizon
    sourceScheduler targetScheduler source target sourceRaw targetRaw owner sourceActive
      targetActive recalled observed
  have sourceClean := (onePacketMenu_countClean runtime leaks bounds
    sourceScheduler).history initial horizon
      (fun state _ => countClean_initial runtime leaks state) sourceTrace
  have clean : CountClean runtime leaks target.execution := by
    refine ⟨countRecall_history runtime leaks targetRaw, ?_⟩
    intro message member
    rw [permits_congr target.execution.network.inputs
      source.execution.network.inputs message (fun other => ?_)]
    · exact sourceClean.2 message ((inputs message).mpr member)
    · exact and_congr (inputs other).symm Iff.rfl
  exact onePacketMenu_trace_of_countClean runtime leaks bounds initial horizon
    targetScheduler target targetTrace clean

end Vegas.EventGraphRuntime.PhaseCount
