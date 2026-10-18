/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingOriginalEmissionPosition
import Vegas.Pending.PhaseSeedEmissionPrefix

/-! # Initial original emissions remain in the last predeadline query -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- An original clock-zero service envelope is already in the exact retained
query before the last original clock advance. No later packet is substituted. -/
theorem original_clock_zero_emission_before_nineteen (menu : app.ResponseMenu) (seeds : Seeds)
    (remaining : Nat) (execution : app.Execution)
    (trace : (menu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (bounded : 19 < execution.environmentRecall.length)
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : (0, message) ∈ (PhaseSeedScheduler.localInput runtime leaks
      (originalCoordinate owner) owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions) :
    (0, message) ∈ (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
      (execution.environmentRecall.take 19)
        execution.environmentRecall[19].beforeView).emissions := by
  classical
  let entry := execution.environmentRecall[19]
  have split : execution.environmentRecall = execution.environmentRecall.take 19 ++
      entry :: execution.environmentRecall.drop 20 := by
    rw [List.getElem_cons_drop bounded, List.take_append_drop]
  apply PhaseSeedScheduler.emission_mem_before_suffix runtime leaks (originalCoordinate owner)
    owner (execution.environmentRecall.take 19) entry (execution.environmentRecall.drop 20)
      (execution.observeEnvironment app) 0 message
  · rwa [← split]
  · intro record member callback zero
    change record ∈ execution.environmentRecall[19] :: execution.environmentRecall.drop 20
      at member
    rw [List.getElem_cons_drop bounded] at member
    obtain ⟨offset, found⟩ := List.mem_iff_getElem?.mp member
    rw [List.getElem?_drop] at found
    obtain ⟨actualBound, actualEntry⟩ := List.getElem?_eq_some_iff.mp found
    have actualCallback : PhaseSeedScheduler.callback runtime leaks (originalCoordinate owner)
        owner execution.environmentRecall[19 + offset] := by
      rw [actualEntry]
      exact callback
    have actualZero : PhaseSeedScheduler.elapsed runtime leaks (originalCoordinate owner)
        execution.environmentRecall[19 + offset].beforeView = 0 := by
      rw [actualEntry]
      exact zero
    have before := original_clock_zero_callback_before_two menu seeds remaining execution trace
      owner (19 + offset) actualBound actualCallback actualZero
    omega

end Vegas.Examples.CommitSeedSignalling
