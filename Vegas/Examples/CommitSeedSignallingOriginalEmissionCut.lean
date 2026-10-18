/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingOriginalEmissionPosition
import Vegas.Pending.PhaseSeedEmissionPrefix

/-! # Eligible original envelopes are present at their actual inclusion query -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- An eligible original envelope in a later complete physical history is
already in the exact local emission word at its selected include. The prefix
is an actual retained environment query, not a refreshed state or input law. -/
theorem original_eligible_emission_before_include (menu : app.ResponseMenu) (seeds : Seeds)
    (remaining : Nat) (execution : app.Execution)
    (trace : (menu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player)
    (bounded : lateIncludePosition owner (seeds.2 (originalAddress owner)) <
      execution.environmentRecall.length)
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : (lateClock owner (seeds.2 (originalAddress owner)), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        execution.environmentRecall (execution.observeEnvironment app)).emissions) :
    (lateClock owner (seeds.2 (originalAddress owner)), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        (execution.environmentRecall.take
          (lateIncludePosition owner (seeds.2 (originalAddress owner))))
        execution.environmentRecall[
          lateIncludePosition owner (seeds.2 (originalAddress owner))].beforeView).emissions := by
  classical
  let position := lateIncludePosition owner (seeds.2 (originalAddress owner))
  let entry := execution.environmentRecall[position]
  have split : execution.environmentRecall = execution.environmentRecall.take position ++
      entry :: execution.environmentRecall.drop (position + 1) := by
    rw [List.getElem_cons_drop bounded, List.take_append_drop]
  apply PhaseSeedScheduler.emission_mem_before_suffix runtime leaks (originalCoordinate owner)
    owner (execution.environmentRecall.take position) entry
      (execution.environmentRecall.drop (position + 1)) (execution.observeEnvironment app)
        (lateClock owner (seeds.2 (originalAddress owner))) message
  · rwa [← split]
  · intro record member callback eligible
    change record ∈ execution.environmentRecall[position] ::
      execution.environmentRecall.drop (position + 1) at member
    rw [List.getElem_cons_drop bounded] at member
    obtain ⟨offset, found⟩ := List.mem_iff_getElem?.mp member
    rw [List.getElem?_drop] at found
    obtain ⟨actualBound, actualEntry⟩ := List.getElem?_eq_some_iff.mp found
    have actualCallback : PhaseSeedScheduler.callback runtime leaks (originalCoordinate owner)
        owner execution.environmentRecall[position + offset] := by
      rw [actualEntry]
      exact callback
    have actualEligible : PhaseSeedScheduler.elapsed runtime leaks (originalCoordinate owner)
        execution.environmentRecall[position + offset].beforeView =
          lateClock owner (seeds.2 (originalAddress owner)) := by
      rw [actualEntry]
      exact eligible
    have before := original_eligible_callback_before_include menu seeds remaining execution trace
      owner (position + offset) actualBound actualCallback actualEligible
    change position + offset < position at before
    omega

end Vegas.Examples.CommitSeedSignalling
