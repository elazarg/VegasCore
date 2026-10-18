/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastAudit
import Vegas.Pending.PhaseCountedTrace
import Interaction.ReactiveCompleteInput

/-! # Actual counted representatives throughout a complete native input fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Complete packet observation determines count permission on every signed
input. Every raw history sharing a counted representative's full decision input
therefore admits a counted trace at that identical physical control. -/
theorem counted_input_raw_fiber_trace
    (sourceScheduler targetScheduler : app.Scheduler) (source target : app.Control)
    (sourceTrace : (countedMenu.protocol initial horizon sourceScheduler).Trace (some source))
    (targetTrace : (rawMenu.protocol initial horizon targetScheduler).Trace (some target))
    (owner : Player) (sourceActive : source.actor = some owner)
    (targetActive : target.actor = some owner)
    (recalled : source.execution.recall owner = target.execution.recall owner)
    (observed : source.execution.observe app owner = target.execution.observe app owner) :
    Nonempty ((countedMenu.protocol initial horizon targetScheduler).Trace (some target)) := by
  have sourceRaw := countedMenu.toRawTrace initial horizon sourceScheduler sourceTrace
  have targetRaw := rawMenu.toRawTrace initial horizon targetScheduler targetTrace
  have inputs := app.complete_decision_inputs_congr rfl initial horizon
    sourceScheduler targetScheduler source target sourceRaw targetRaw owner sourceActive
      targetActive recalled observed
  have sourceClean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds
    sourceScheduler).history initial horizon
      (fun state _ => PhaseCount.countClean_initial runtime leaks state) sourceTrace
  have clean : PhaseCount.CountClean runtime leaks target.execution := by
    refine ⟨PhaseCount.countRecall_history runtime leaks targetRaw, ?_⟩
    intro message member
    rw [PhaseCount.permits_congr target.execution.network.inputs
      source.execution.network.inputs message (fun other => ?_)]
    · exact sourceClean.2 message ((inputs message).mpr member)
    · exact and_congr (inputs other).symm Iff.rfl
  exact PhaseCount.onePacketMenu_trace_of_countClean runtime leaks bounds initial horizon
    targetScheduler target targetTrace clean

end Vegas.Examples.CommitSeedBroadcast
