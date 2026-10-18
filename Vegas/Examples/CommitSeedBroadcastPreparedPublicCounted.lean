/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperInitialPacketFrame
import Vegas.Examples.CommitSeedBroadcastCountedFiber

/-! # Counted prepared frames throughout an original public-packet fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

open Classical in
/-- At the actual five-command frame, the retained initial public word is
exactly the current signed-input set, including every hidden preparation alias. -/
theorem prepared_public_packets_inputs (seed : Seeds) (players : Player → app.Policy)
    (frame : app.Execution)
    (reached : frame ∈ (app.runRounds (family seed) players 5 initialExecution).support) :
    initialPublicPackets frame = frame.network.inputs.toFinset := by
  rw [first_five_rounds] at reached
  obtain ⟨first, _first, secondReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨second, _second, thirdReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ secondReached)
  obtain ⟨third, _third, equal⟩ := PMF.support_map .. ▸ thirdReached
  subst frame
  exact initialClockTwo_public_packets first second third

/-- Equality of the observed original public word transports actual count
permission between prepared frames. The target's raw trace, recalled envelopes
and forbidden verdicts recover its counted prehistory at the identical control. -/
theorem prepared_public_alias_counted_trace
    (sourceSeed targetSeed : Seeds) (sourcePlayers targetPlayers : Player → app.Policy)
    (source target : app.Execution)
    (sourceReached : source ∈
      (app.runRounds (family sourceSeed) sourcePlayers 5 initialExecution).support)
    (targetReached : target ∈
      (app.runRounds (family targetSeed) targetPlayers 5 initialExecution).support)
    (sourceScheduler targetScheduler : app.Scheduler) (sourceFuel targetFuel : Nat)
    (sourceTrace : (countedMenu.protocol initial horizon sourceScheduler).Trace
      (some ⟨sourceFuel, none, source⟩))
    (targetTrace : (rawMenu.protocol initial horizon targetScheduler).Trace
      (some ⟨targetFuel, none, target⟩))
    (packets : initialPublicPackets source = initialPublicPackets target) :
    Nonempty ((countedMenu.protocol initial horizon targetScheduler).Trace
      (some ⟨targetFuel, none, target⟩)) := by
  classical
  have sameInputs : ∀ message, message ∈ source.network.inputs ↔
      message ∈ target.network.inputs := by
    have same := (prepared_public_packets_inputs sourceSeed sourcePlayers source
      sourceReached).symm.trans (packets.trans
        (prepared_public_packets_inputs targetSeed targetPlayers target targetReached))
    intro message
    have membership := Finset.ext_iff.mp same message
    simpa only [List.mem_toFinset] using membership
  have sourceClean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds
    sourceScheduler).history initial horizon
      (fun state _ => PhaseCount.countClean_initial runtime leaks state) sourceTrace
  have clean : PhaseCount.CountClean runtime leaks target := by
    refine ⟨PhaseCount.countRecall_history runtime leaks
      (rawMenu.toRawTrace initial horizon targetScheduler targetTrace), ?_⟩
    intro message member
    rw [PhaseCount.permits_congr target.network.inputs source.network.inputs message
      (fun other => and_congr (sameInputs other).symm Iff.rfl)]
    exact sourceClean.2 message ((sameInputs message).mpr member)
  exact PhaseCount.onePacketMenu_trace_of_countClean runtime leaks bounds initial horizon
    targetScheduler ⟨targetFuel, none, target⟩ targetTrace clean

end Vegas.Examples.CommitSeedBroadcast
