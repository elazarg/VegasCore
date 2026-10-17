/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingInformation
import Interaction.ReactiveSchedulerTranscript
import Interaction.ReactiveSchedulerBeforeResponse

/-! # Original private seed laws at the actual native callbacks -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

def seedBits (seeds : Seeds) (owner : Player) : Bool :=
  seeds.2 (originalAddress owner)

def seedOfBits (bits : Player → Bool) : Seeds :=
  ((), fun address =>
    if address = originalAddress alice then bits alice
    else if address = originalAddress bob then bits bob else false)

def bitPrior : PMF (Player → Bool) :=
  independentProduct fun _ : Player => PMF.uniformOfFintype Bool

theorem originalAddress_injective : Function.Injective originalAddress := by
  intro first second equal
  have events := congrArg (fun address : PhaseSeedAddress graph => address.1.event.val) equal
  fin_cases first <;> fin_cases second
  · rfl
  · change 0 = 1 at events
    omega
  · change 1 = 0 at events
    omega
  · rfl

theorem originalAddress_ne : originalAddress alice ≠ originalAddress bob := by
  intro equal
  have := originalAddress_injective equal
  exact (by decide : alice ≠ bob) this

theorem seedBits_seedOfBits (bits : Player → Bool) : seedBits (seedOfBits bits) = bits := by
  funext owner
  fin_cases owner <;>
    simp [seedBits, seedOfBits, Ne.symm originalAddress_ne,
      OnePacketCommitRevealHypotheses.alice, OnePacketCommitRevealHypotheses.bob]

theorem seedLaws_original (owner : Player) :
    seedLaws (originalAddress owner) = PMF.uniformOfFintype Bool := by
  fin_cases owner <;>
    simp [seedLaws, OnePacketCommitRevealHypotheses.alice,
      OnePacketCommitRevealHypotheses.bob]

/-- This is an equality of the original full-address carrier, including every
degenerate coordinate. It does not install a new prior at a decision. -/
theorem seedPrior_eq_bitPrior : seedPrior = bitPrior.map seedOfBits := by
  classical
  let embedding : Player ↪ PhaseSeedAddress graph :=
    ⟨originalAddress, originalAddress_injective⟩
  have projection :
      (independentProduct seedLaws).map (fun values owner => values (originalAddress owner)) =
        bitPrior := by
    have projected := independentProduct_map_embedding embedding seedLaws
    change (independentProduct seedLaws).map
      (fun values owner => values (originalAddress owner)) =
        independentProduct (fun owner => seedLaws (originalAddress owner)) at projected
    simpa only [seedLaws_original, bitPrior] using projected
  calc
    seedPrior = (independentProduct seedLaws).map
        (fun values => seedOfBits (fun owner => values (originalAddress owner))) := by
      apply map_congr_on_support
      intro values supported
      unfold seedOfBits
      apply Prod.ext
      · rfl
      · funext address
        by_cases first : address = originalAddress alice
        · subst address
          simp only [ite_true]
        · by_cases second : address = originalAddress bob
          · subst address
            simp only [ite_eq_right first, ite_true]
          · have coordinate := (independentProduct_support_iff seedLaws values).mp supported address
            have fixed : values address = false := by
              simpa only [seedLaws, ite_eq_right (not_or.mpr ⟨first, second⟩),
                PMF.mem_support_pure_iff] using coordinate
            simpa only [ite_eq_right first, ite_eq_right second] using fixed
    _ = ((independentProduct seedLaws).map
        (fun values owner => values (originalAddress owner))).map seedOfBits :=
      by simpa only [Function.comp_def] using (PMF.map_comp _ _ _).symm
    _ = bitPrior.map seedOfBits := congrArg (fun law => law.map seedOfBits) projection

theorem seedPrior_bits : seedPrior.map seedBits = bitPrior := by
  rw [seedPrior_eq_bitPrior, PMF.map_comp]
  have identity : (fun bits => seedBits (seedOfBits bits)) = id := by
    funext bits
    exact seedBits_seedOfBits bits
  simp only [Function.comp_def, identity, PMF.map_id]

theorem seedPrior_bit (owner : Player) :
    seedPrior.map (fun seeds => seedBits seeds owner) = PMF.uniformOfFintype Bool := by
  have projected := congrArg (fun law : PMF (Player → Bool) =>
    law.map (fun bits => bits owner)) seedPrior_bits
  simpa only [PMF.map_comp, Function.comp_def, bitPrior, independentProduct_map_eval]
    using projected

/-- The original seed carrier, reduced only by an exact pushforward identity. -/
theorem four_seed_execution (players : Player → app.Policy) (count : Nat) :
    app.runRounds scheduler players count initialExecution =
      bitPrior.bind (fun bits => app.runRounds (family (seedOfBits bits)) players count
        initialExecution) := by
  unfold initialExecution
  rw [← original_realize, seedPrior_eq_bitPrior, PMF.bind_map]
  rfl

/-- The actual joint immediately after Bob's original activation, before his response. -/
def bobPrefixJoint (players : Player → app.Policy) : PMF (app.Execution × Seeds) :=
  seedPrior.bind fun seed =>
    (app.runRounds (family seed) players 1 initialExecution).bind fun execution =>
      (family seed execution.environmentRecall (execution.observeEnvironment app)).bind
        fun command => (execution.environmentStep app command).map fun next => (next, seed)

theorem bobPrefixJoint_eq (players : Player → app.Policy) :
    bobPrefixJoint players =
      bindPairLaw ((players alice [] (aliceFirst.observe app alice)).map bobFirst)
        (fun _ => seedPrior) := by
  have branch (seed : Seeds) :
      (app.runRounds (family seed) players 1 initialExecution).bind (fun execution =>
        (family seed execution.environmentRecall (execution.observeEnvironment app)).bind
          fun command => (execution.environmentStep app command).map fun next => (next, seed)) =
        (players alice [] (aliceFirst.observe app alice)).map
          fun response => (bobFirst response, seed) := by
    have mapped := congrArg (fun law : PMF (app.Command × app.Execution) =>
      law.map (fun outcome => (outcome.2, seed))) (bobFirst_command_law players seed)
    simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using mapped
  unfold bobPrefixJoint
  simp_rw [branch]
  rw [show (seedPrior.bind fun seed =>
      (players alice [] (aliceFirst.observe app alice)).map
        fun response => (bobFirst response, seed)) =
      (players alice [] (aliceFirst.observe app alice)).bind fun response =>
        seedPrior.map (fun seed => (bobFirst response, seed)) from
      PMF.bind_comm ..]
  simp only [bindPairLaw, PMF.bind_map, Function.comp_def]

/-- This equality connects the prefix experiment to the actual mixed scheduler;
the seeds are retained at their genuine command posterior. -/
theorem bobPrefixJoint_realize (players : Player → app.Policy) :
    bobPrefixJoint players =
      (app.runRounds scheduler players 1 initialExecution).bind fun execution =>
        (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind
          fun command => (execution.environmentStep app command).bind fun next =>
            (implementation.posterior next.environmentRecall).map (Prod.mk next) := by
  have joint := app.schedulerMixture_beforeResponse_joint seedPrior family players 1 initialState
  have projected := congrArg (fun law : PMF (app.Command × app.Execution × Seeds) =>
    law.map (fun outcome => (outcome.2.1, outcome.2.2))) joint
  simpa only [bobPrefixJoint, scheduler, implementation, initialExecution,
    PMF.map_bind, PMF.map_comp, Function.comp_def] using projected

def bobPrefixObserve (outcome : app.Execution × Seeds) : app.Info :=
  some (outcome.1.recall bob, outcome.1.observe app bob)

theorem bobPrefixJoint_observed (players : Player → app.Policy) :
    (bobPrefixJoint players).map (fun outcome => (bobPrefixObserve outcome, outcome.2)) =
      bindPairLaw ((players alice [] (aliceFirst.observe app alice)).map
        (fun response => some ((bobFirst response).recall bob,
          (bobFirst response).observe app bob))) (fun _ => seedPrior) := by
  rw [bobPrefixJoint_eq]
  simp only [bindPairLaw, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def,
    bobPrefixObserve]

/-- Conditioning on the complete second-callback input does not select seeds.
This is an exact prefix identity, with no reach-probability or limiting argument. -/
theorem bobPrefix_seed_of_full_input (players : Player → app.Policy) (input : app.Info)
    (present : input ∈ ((bobPrefixJoint players).map bobPrefixObserve).support) :
    (fiberPosterior (bobPrefixJoint players) bobPrefixObserve input).map Prod.snd = seedPrior := by
  let read : app.Execution × Seeds → app.Info × Seeds :=
    fun outcome => (bobPrefixObserve outcome, outcome.2)
  have transported := map_fiberPosterior_readout (bobPrefixJoint players) read Prod.fst input
    present
  have marginal := congrArg (fun law : PMF (app.Info × Seeds) => law.map Prod.snd) transported
  rw [PMF.map_comp] at marginal
  change (fiberPosterior (bobPrefixJoint players) bobPrefixObserve input).map Prod.snd =
    (fiberPosterior ((bobPrefixJoint players).map read) Prod.fst input).map Prod.snd at marginal
  rw [marginal]
  rw [show (bobPrefixJoint players).map read = _ from bobPrefixJoint_observed players]
  exact fiberPosterior_snd_bindPairLaw_const _ _ _

theorem bobPrefix_bit_of_full_input (players : Player → app.Policy) (input : app.Info)
    (present : input ∈ ((bobPrefixJoint players).map bobPrefixObserve).support) (owner : Player) :
    (fiberPosterior (bobPrefixJoint players) bobPrefixObserve input).map
        (fun outcome => seedBits outcome.2 owner) = PMF.uniformOfFintype Bool := by
  have projected := congrArg (fun law : PMF Seeds => law.map (fun seed => seedBits seed owner))
    (bobPrefix_seed_of_full_input players input present)
  simpa only [PMF.map_comp, Function.comp_def, seedPrior_bit] using projected

theorem aliceFirst_belief_state (assessment : rawModel.BehavioralAssessment) :
    (assessment.belief alice aliceFirstSite).map (fun history => history.1.state) =
      PMF.pure (some (⟨63, some alice, aliceFirst⟩ : app.Control)) := by
  calc
    _ = (assessment.belief alice aliceFirstSite).map
        (fun _ => some (⟨63, some alice, aliceFirst⟩ : app.Control)) := by
      apply map_congr_on_support
      intro history _
      exact aliceFirst_information_state history
    _ = _ := PMF.map_const _ _

theorem bobQuiet_belief_state (assessment : rawModel.BehavioralAssessment) :
    (assessment.belief bob bobQuietSite).map (fun history => history.1.state) =
      PMF.pure (some (⟨62, some bob, bobFirst ⟨none⟩⟩ : app.Control)) := by
  calc
    _ = (assessment.belief bob bobQuietSite).map
        (fun _ => some (⟨62, some bob, bobFirst ⟨none⟩⟩ : app.Control)) := by
      apply map_congr_on_support
      intro history _
      exact bobQuiet_information_state history
    _ = _ := PMF.map_const _ _

end Vegas.Examples.CommitSeedSignalling
