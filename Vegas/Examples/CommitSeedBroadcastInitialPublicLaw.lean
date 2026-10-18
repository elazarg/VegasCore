/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperPublicPackets
import Vegas.Examples.CommitSeedBroadcastPreparedPrefix
import GameTheory.Math.Probability.ConditionalObservation

/-! # The original initialized experiment conditioned on its public initial packets -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- The actual five-round prefix has not read the original order or good bits.
Its entire private preparation state remains in the same initialized joint law. -/
theorem initial_public_prefix_joint (players : Player → app.Policy) (reference : Seeds) :
    (nativeSeedLaw.bind fun seed =>
      (app.runRounds (family seed) players 5 initialExecution).map fun frame => (frame, seed)) =
    bindPairLaw (app.runRounds (family reference) players 5 initialExecution)
      (fun _ => nativeSeedLaw) := by
  calc
    _ = (bindPairLaw nativeSeedLaw (fun _ =>
        app.runRounds (family reference) players 5 initialExecution)).map Prod.swap := by
      simp only [bindPairLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
      apply congrArg (fun kernel => nativeSeedLaw.bind kernel)
      funext seed
      rw [first_five_seed_independent seed reference players]
      rfl
    _ = _ := bindPairLaw_const_map_swap nativeSeedLaw _

/-- Conditioning the original initialized experiment on its initial public
word retains the complete original preparation posterior and the full original
seed law together. Nothing is replaced by an independent refreshed preparation. -/
theorem initial_public_prefix_posterior (players : Player → app.Policy) (reference : Seeds)
    (packets : Finset (Message Player app.Payload))
    (present : packets ∈ ((app.runRounds (family reference) players 5 initialExecution).map
      initialPublicPackets).support) :
    fiberPosterior (nativeSeedLaw.bind fun seed =>
      (app.runRounds (family seed) players 5 initialExecution).map fun frame => (frame, seed))
      (fun outcome => initialPublicPackets outcome.1) packets =
    bindPairLaw (fiberPosterior (app.runRounds (family reference) players 5 initialExecution)
      initialPublicPackets packets) (fun _ => nativeSeedLaw) := by
  rw [initial_public_prefix_joint]
  exact fiberPosterior_bind_of_observation
    (app.runRounds (family reference) players 5 initialExecution)
    (fun frame => nativeSeedLaw.map (Prod.mk frame)) initialPublicPackets
    (fun outcome => initialPublicPackets outcome.1) (by
      intro frame _supported outcome produced
      obtain ⟨seed, _prior, equal⟩ := PMF.support_map .. ▸ produced
      rw [← equal]) packets present

end Vegas.Examples.CommitSeedBroadcast
