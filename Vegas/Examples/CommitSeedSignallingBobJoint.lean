/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingLateBeliefs

/-! # The original Bob seed and the complete late continuation joint -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player bob)

/-- Retain the original seed bit, every updated earlier physical field and
all other original addresses while continuing the same seeded execution. -/
def bobPrefixFinalJoint (players : Player → app.Policy) (future : Nat) :
    PMF (Bool × ((app.Execution × BobSeedRest) × app.Execution)) :=
  seedPrior.bind fun seed =>
    (bindPairLaw (app.runRounds (family seed) players 12 initialExecution)
      (app.runRounds (family seed) players future)).map fun pair =>
        (seedBits seed bob, (pair.1, bobSeedRest seed), pair.2)

/-- Independence is before Bob's first poll. The final continuation keeps
the same original bit rather than drawing another bit at the physical prefix. -/
theorem bobPrefixFinalJoint_eq (players : Player → app.Policy) (future : Nat) :
    bobPrefixFinalJoint players future =
      (beforeBobRemainderLaw players 12).bind fun remainder =>
        (PMF.uniformOfFintype Bool).bind fun bit =>
          (app.runRounds (family (joinBobSeed bit remainder.2)) players future remainder.1).map
            fun final => (bit, remainder, final) := by
  unfold bobPrefixFinalJoint
  rw [seedPrior_split_bob]
  simp only [PMF.bind_bind, PMF.bind_map, bindPairLaw, PMF.map_bind, PMF.map_comp,
    Function.comp_def]
  calc
    _ = (PMF.uniformOfFintype Bool).bind (fun bit =>
        (beforeBobRemainderLaw players 12).bind fun remainder =>
          (app.runRounds (family (joinBobSeed bit remainder.2)) players future remainder.1).map
            fun final => (bit, remainder, final)) := by
      apply bind_congr_on_support
      intro bit _
      unfold beforeBobRemainderLaw
      simp only [PMF.bind_bind, PMF.bind_map]
      apply bind_congr_on_support
      intro rest _
      rw [run_before_bob_seed players 12 (by omega) bit rest]
      simp only [joinBobSeed_bit, joinBobSeed_rest, Function.comp_def]
    _ = _ := PMF.bind_comm ..

/-- Erasing the original seed coordinates gives exactly the actual integrated
scheduler's joint of its complete pre-poll physical history and final history. -/
theorem bobPrefixFinalJoint_physical (players : Player → app.Policy) (future : Nat) :
    (bobPrefixFinalJoint players future).map (fun outcome => (outcome.2.1.1, outcome.2.2)) =
      bindPairLaw (app.runRounds scheduler players 12 initialExecution)
        (app.runRounds scheduler players future) := by
  unfold bobPrefixFinalJoint
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, bindPairLaw]
  calc
    _ = (seedPrior.bind fun seed =>
        (app.runRounds (family seed) players 12 initialExecution).map
          fun execution => (execution, seed)).bind (fun pair =>
            (app.runRounds (family pair.2) players future pair.1).map
              fun final => (pair.1, final)) := by
      simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
    _ = (app.runRounds scheduler players 12 initialExecution).bind (fun execution =>
        (implementation.posterior execution.environmentRecall).bind fun seed =>
          (app.runRounds (family seed) players future execution).map
            fun final => (execution, final)) := by
      rw [show initialExecution = ReactiveApplication.Execution.initial app initialState from rfl,
        app.schedulerMixture_joint seedPrior family players 12 initialState]
      simp only [PMF.bind_bind, PMF.bind_map]
      rfl
    _ = _ := by
      apply bind_congr_on_support
      intro execution _
      have realized : (implementation.posterior execution.environmentRecall).bind
          (fun seed => app.runRounds (family seed) players future execution) =
            app.runRounds scheduler players future execution := by
        have joint := implementation.realize players future execution
        simp only [implementation, app.schedulerMixture_runJoint, PMF.map_bind,
          PMF.map_comp, Function.comp_def] at joint
        change (implementation.posterior execution.environmentRecall).bind
          (fun seed => (app.runRounds (family seed) players future execution).map id) =
            app.runRounds scheduler players future execution at joint
        simpa only [PMF.map_id] using joint
      rw [← PMF.map_bind, realized]

end Vegas.Examples.CommitSeedSignalling
