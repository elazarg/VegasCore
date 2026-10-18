/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperAssessedFrameLaw
import Vegas.Examples.CommitSeedBroadcastPreparedPublicCounted
import Vegas.Examples.CommitSeedBroadcastHelperConditionalOriginalLaw

/-! # The actual assessed continuation conditioned on an original public word -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- At a valid single-helper public word, the actual incumbent original
observable kernel is constant across the entire original preparation posterior.
The joint retains that posterior in its first coordinate. Its mass may vanish
along a perturbation sequence; no lower bound on that initial mass is used. -/
theorem single_helper_assessed_public_kernel
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (initialProfile : ∀ owner, rawModel.BehavioralPolicy owner)
    (packets : Finset (Message Player app.Payload))
    (present : packets ∈ ((app.runRounds scheduler
      (rawMenu.decodeProfile initial horizon scheduler initialProfile) 5 initialExecution).map
        initialPublicPackets).support)
    (hidden : Player) (nonempty : packets.Nonempty)
    (owned : ∀ message ∈ packets, message.sender = hidden)
    (named : ∃ message ∈ packets,
      PhaseCount.event? message.payload = some (originalCoordinate hidden))
    (sourcePlayers : Player → app.Policy) (source : app.Execution)
    (sourceReached : source ∈ (app.runRounds scheduler sourcePlayers 5 initialExecution).support)
    (sourceTrace : countedProtocol.Trace (some ⟨horizon - 5, none, source⟩))
    (sourcePackets : initialPublicPackets source = packets)
    (count : Nat) (bounded : count ≤ 19) :
    (fiberPosterior (app.runRounds scheduler
      (rawMenu.decodeProfile initial horizon scheduler initialProfile) 5 initialExecution)
      initialPublicPackets packets).bind (fun frame =>
        ((app.runRounds scheduler
          (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) count frame).map
          (originalHelperObservation hidden)).map fun observation => (frame, observation)) =
    bindPairLaw (fiberPosterior (app.runRounds scheduler
      (rawMenu.decodeProfile initial horizon scheduler initialProfile) 5 initialExecution)
      initialPublicPackets packets) (fun _ =>
        (app.runRounds scheduler
          (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) count source).map
          (originalHelperObservation hidden)) := by
  classical
  let initialPlayers := rawMenu.decodeProfile initial horizon scheduler initialProfile
  obtain ⟨sourceSeed, sourceFixed⟩ :=
    prepared_mixed_fixed_support sourcePlayers source sourceReached
  obtain ⟨sourceMaterial, sourceEq⟩ := initial_single_helper_frame sourceSeed sourcePlayers source
    sourceFixed hidden (sourcePackets.symm ▸ nonempty)
      (by simpa only [sourcePackets] using owned)
  change _ = (fiberPosterior _ initialPublicPackets packets).bind _
  apply bind_congr_on_support
  intro frame supported
  have facts := mem_support_fiberPosterior present supported
  obtain ⟨seed, fixed⟩ := prepared_mixed_fixed_support initialPlayers frame facts.2
  obtain ⟨countedTrace⟩ := prepared_mixed_public_alias_counted_trace sourcePlayers initialProfile
    source frame sourceReached facts.2 sourceTrace (sourcePackets.trans facts.1.symm)
  obtain ⟨material, frameEq⟩ := initial_single_helper_frame seed initialPlayers frame fixed
    hidden (facts.1.symm ▸ nonempty) (by simpa only [facts.1] using owned)
  have packet := same_helper_public_packet hidden material sourceMaterial (by
    rw [← frameEq, ← sourceEq, facts.1, sourcePackets])
  have currentSent : ∃ message ∈ initialPublicPackets (initialHelperFrame hidden material),
      PhaseCount.event? message.payload = some (originalCoordinate hidden) := by
    simpa only [← frameEq, facts.1] using named
  have sourceSent : ∃ message ∈ initialPublicPackets (initialHelperFrame hidden sourceMaterial),
      PhaseCount.event? message.payload = some (originalCoordinate hidden) := by
    simpa only [← sourceEq, sourcePackets] using named
  have kernel := initial_helper_assessed_original_run_law assessment equilibrium hidden count
    bounded material sourceMaterial (frameEq ▸ countedTrace) (sourceEq ▸ sourceTrace)
    currentSent sourceSent packet
  rw [← frameEq, ← sourceEq] at kernel
  exact congrArg (fun law => law.map fun observation => (frame, observation)) kernel

end Vegas.Examples.CommitSeedBroadcast
