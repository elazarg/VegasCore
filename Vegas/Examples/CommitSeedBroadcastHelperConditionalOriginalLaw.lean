/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperInitialPacketFrame

/-! # Cancellation of the original hidden helper preparation at a public word -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

open Classical in
private theorem initial_helper_packet_set (hidden : Player)
    (material : WitnessedSubmission graph) :
    initialPublicPackets (initialHelperFrame hidden material) =
      {⟨(hidden, 0), app.packet (app.submit (initialCallback hidden).application hidden material)
        hidden ((initialCallback hidden).network.known hidden) material⟩} := by
  fin_cases hidden <;> rfl

private theorem same_helper_public_packet (hidden : Player)
    (first second : WitnessedSubmission graph)
    (same : initialPublicPackets (initialHelperFrame hidden first) =
      initialPublicPackets (initialHelperFrame hidden second)) :
    app.packet (app.submit (initialCallback hidden).application hidden first) hidden
        ((initialCallback hidden).network.known hidden) first =
      app.packet (app.submit (initialCallback hidden).application hidden second) hidden
        ((initialCallback hidden).network.known hidden) second := by
  rw [initial_helper_packet_set, initial_helper_packet_set] at same
  exact congrArg Message.payload (Finset.singleton_injective same)

/-- Condition the original initialized experiment on its actual public packet
word, then silence only the already-sent helper. The entire original hidden
frame posterior and the original service seed remain in the joint law. The
future observable kernel is constant over preparation and evidence aliases;
the conditional preparation law is not refreshed or discarded. -/
theorem single_helper_conditional_original_joint (players : Player → app.Policy)
    (reference : Seeds) (packets : Finset (Message Player app.Payload))
    (present : packets ∈ ((app.runRounds (family reference) players 5 initialExecution).map
      initialPublicPackets).support)
    (hidden : Player) (nonempty : packets.Nonempty)
    (owned : ∀ message ∈ packets, message.sender = hidden)
    (count : Nat) (bounded : count ≤ 16) :
    ∃ material : WitnessedSubmission graph,
      initialPublicPackets (initialHelperFrame hidden material) = packets ∧
      (fiberPosterior (nativeSeedLaw.bind fun seed =>
        (app.runRounds (family seed) players 5 initialExecution).map fun frame => (frame, seed))
        (fun outcome => initialPublicPackets outcome.1) packets).bind
        (fun original =>
          ((app.runRounds (family original.2)
            (Function.update players hidden (fun _ _ => PMF.pure ⟨none⟩)) count original.1).map
            (originalHelperObservation hidden)).map fun observation =>
              (original.1, (original.2, observation))) =
      bindPairLaw (fiberPosterior (app.runRounds (family reference) players 5 initialExecution)
        initialPublicPackets packets) (fun _ => nativeSeedLaw.bind fun seed =>
          ((app.runRounds (family seed)
            (Function.update players hidden (fun _ _ => PMF.pure ⟨none⟩)) count
            (initialHelperFrame hidden material)).map (originalHelperObservation hidden)).map
              fun observation => (seed, observation)) := by
  classical
  obtain ⟨frame, frameReached, samePackets⟩ := (PMF.mem_support_map_iff _ _ _).mp present
  obtain ⟨material, frameEq⟩ := initial_single_helper_frame reference players frame frameReached
    hidden (samePackets.symm ▸ nonempty) (by simpa only [samePackets] using owned)
  have referencePackets : initialPublicPackets (initialHelperFrame hidden material) = packets :=
    frameEq ▸ samePackets
  refine ⟨material, referencePackets, ?_⟩
  rw [initial_public_prefix_posterior players reference packets present]
  simp only [bindPairLaw, PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp,
    Function.comp_def]
  apply bind_congr_on_support
  intro current supported
  have currentFacts := mem_support_fiberPosterior present supported
  obtain ⟨currentMaterial, currentEq⟩ := initial_single_helper_frame reference players current
    currentFacts.2 hidden (currentFacts.1.symm ▸ nonempty)
      (by simpa only [currentFacts.1] using owned)
  subst current
  have packet := same_helper_public_packet hidden currentMaterial material
    (currentFacts.1.trans referencePackets.symm)
  apply congrArg (fun kernel => nativeSeedLaw.bind kernel)
  funext seed
  have sameKernel := initial_helper_original_run_law seed
    (Function.update players hidden (fun _ _ => PMF.pure ⟨none⟩)) hidden
    (by intro past view; rw [Function.update_self]) count bounded currentMaterial material packet
  simpa only [PMF.map_comp, Function.comp_def] using
    congrArg (fun law => law.map fun observation =>
      (initialHelperFrame hidden currentMaterial, (seed, observation))) sameKernel

end Vegas.Examples.CommitSeedBroadcast
