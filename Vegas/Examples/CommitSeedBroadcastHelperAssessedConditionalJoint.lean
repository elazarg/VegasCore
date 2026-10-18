/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperAssessedOriginalSeed
import Vegas.Examples.CommitSeedBroadcastPreparedPublicCounted
import Vegas.Examples.CommitSeedBroadcastPreparedProtocolPrefix
import Vegas.Examples.CommitSeedBroadcastHelperConditionalOriginalLaw

/-! # The original hidden frame and seed in the assessed public-word experiment -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- Conditioning the ORIGINAL initialized joint on a counted helper's public
word retains its entire hidden-frame posterior and immutable service seed.
The ACTUAL assessed original observable continuation is independent of the
hidden preparation alias. No helper-policy substitution remains in the result. -/
theorem single_helper_assessed_conditional_original_joint
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
    (fiberPosterior (nativeSeedLaw.bind fun seed =>
      (app.runRounds (family seed)
        (rawMenu.decodeProfile initial horizon scheduler initialProfile) 5 initialExecution).map
          fun frame => (frame, seed))
      (fun original => initialPublicPackets original.1) packets).bind (fun original =>
        ((app.runRounds (family original.2)
          (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
          count original.1).map (originalHelperObservation hidden)).map
            fun observation => (original.1, (original.2, observation))) =
    bindPairLaw (fiberPosterior (app.runRounds scheduler
      (rawMenu.decodeProfile initial horizon scheduler initialProfile) 5 initialExecution)
      initialPublicPackets packets) (fun _ => nativeSeedLaw.bind fun seed =>
        ((app.runRounds (family seed)
          (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) count source).map
          (originalHelperObservation hidden)).map fun observation => (seed, observation)) := by
  classical
  let initialPlayers := rawMenu.decodeProfile initial horizon scheduler initialProfile
  let reference : Seeds := Classical.choice (inferInstance : Nonempty Seeds)
  have fixedPresent : packets ∈ ((app.runRounds (family reference) initialPlayers
      5 initialExecution).map initialPublicPackets).support := by
    rw [← initial_mixed_five_rounds initialPlayers reference]
    exact present
  rw [initial_public_prefix_posterior initialPlayers reference packets fixedPresent,
    ← initial_mixed_five_rounds initialPlayers reference]
  simp only [bindPairLaw, PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp,
    Function.comp_def]
  obtain ⟨sourceSeed, sourceFixed⟩ :=
    prepared_mixed_fixed_support sourcePlayers source sourceReached
  obtain ⟨sourceMaterial, sourceEq⟩ := initial_single_helper_frame sourceSeed sourcePlayers source
    sourceFixed hidden (sourcePackets.symm ▸ nonempty)
      (by simpa only [sourcePackets] using owned)
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
  have joint := initial_helper_assessed_original_seed_law assessment equilibrium hidden count
    bounded material sourceMaterial (frameEq ▸ countedTrace) (sourceEq ▸ sourceTrace)
    currentSent sourceSent packet
  rw [← frameEq, ← sourceEq] at joint
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using
    congrArg (fun law => law.map fun outcome => (frame, outcome)) joint

end Vegas.Examples.CommitSeedBroadcast
