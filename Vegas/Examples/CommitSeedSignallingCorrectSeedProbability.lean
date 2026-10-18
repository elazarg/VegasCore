/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingFixedLateSuccess
import Vegas.Examples.CommitSeedSignallingAliceInitializedHalf

/-! # Initialized proper delivery from the original fair seed -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

theorem original_binding_accepted_runRounds (selected : app.Scheduler)
    (players : Player → app.Policy) (count : Nat) (before after : app.Execution)
    (reached : after ∈ (app.runRounds selected players count before).support)
    (owner : Player)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      before) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner after := by
  let property : app.Execution → Prop := fun current =>
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner current
  have invariant : app.ServiceInvariant selected property := by
    constructor
    · intro execution actor action valid
      obtain ⟨message, member, sender, attempt, event, receipt⟩ := valid
      refine ⟨message, ?_, sender, attempt, event, ?_⟩
      · rcases action with ⟨transmission⟩
        cases transmission with
        | none => exact member
        | some material => exact List.mem_append_left _ member
      · rwa [app.respond_receipts]
    · intro execution next command valid _selected moved
      obtain ⟨message, member, sender, attempt, event, receipt⟩ := valid
      refine ⟨message, ?_, sender, attempt, event, ?_⟩
      · rwa [app.environmentStep_inputs execution next command moved]
      · exact (app.environmentStep_receipts_prefix execution next command moved).subset receipt
  exact invariant.runRounds players count before after accepted reached

section Counted

variable (profile : ∀ who, countedModel.BehavioralPolicy who)

local notation "players" => countedMenu.decodeProfile initial horizon scheduler profile

/-- The original correct-seed receipt survives the entire actual continuation,
including retries, exclusions, old-attempt retirement and arbitrary later play. -/
theorem fixed_late_accepted_terminal (seed : Seeds) (owner : Player)
    (correct : seedBits seed owner = false)
    (ownerPolicy : players owner = fixedLatePolicy owner)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players horizon initialExecution).support) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final := by
  have whole : app.runRounds (family seed) players horizon initialExecution =
      (app.runRounds (family seed) players (firstLatePosition owner + 4)
        initialExecution).bind fun before =>
          app.runRounds (family seed) players (horizon - (firstLatePosition owner + 4)) before := by
    rw [← app.runRounds_add]
    congr 1
    fin_cases owner <;> rfl
  rw [whole, PMF.support_bind] at reached
  obtain ⟨before, prior, future⟩ := Set.mem_iUnion₂.mp reached
  exact original_binding_accepted_runRounds (family seed) players
    (horizon - (firstLatePosition owner + 4)) before final future owner
      (fixed_late_accepted_first_block profile seed owner correct ownerPolicy aliceWait bobWait
        before prior)

/-- At least half of the initialized original-seed experiment genuinely
accepts the fixed owner's proper original packet. The full original table is
split at its one original coordinate; its entire remainder is retained. -/
theorem fixed_late_acceptance_probability (owner : Player)
    (ownerPolicy : players owner = fixedLatePolicy owner)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩) :
    (1 / 2 : ℝ) ≤
      ((app.runRounds scheduler players horizon initialExecution).toOuterMeasure
        {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
          owner final}).toReal := by
  classical
  let Rest := {address : PhaseSeedAddress graph // address ≠ originalAddress owner} → Bool
  let restLaw : PMF Rest := independentProduct fun address => seedLaws address
  let join : Bool → Rest → Seeds := fun bit rest =>
    ((), (Equiv.piSplitAt (originalAddress owner)
      (fun _ : PhaseSeedAddress graph => Bool)).symm (bit, rest))
  have read (bit : Bool) (rest : Rest) : seedBits (join bit rest) owner = bit := by
    have equal := congrArg Prod.fst (Equiv.apply_symm_apply
      (Equiv.piSplitAt (originalAddress owner) (fun _ : PhaseSeedAddress graph => Bool))
        (bit, rest))
    exact equal
  have splitPrior : seedPrior =
      (PMF.uniformOfFintype Bool).bind fun bit => restLaw.map (join bit) := by
    unfold seedPrior
    rw [independentProduct_splitAt seedLaws (originalAddress owner)]
    simp only [seedLaws_original, PMF.map_bind, PMF.map_comp, Function.comp_def]
    rfl
  let accepted : Set app.Execution := {final |
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final}
  let falseLaw := restLaw.bind fun rest =>
    app.runRounds (family (join false rest)) players horizon initialExecution
  let trueLaw := restLaw.bind fun rest =>
    app.runRounds (family (join true rest)) players horizon initialExecution
  have falseAccepted : falseLaw.toOuterMeasure accepted = 1 := by
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro final supported
    change final ∈ (restLaw.bind _).support at supported
    rw [PMF.support_bind] at supported
    obtain ⟨rest, _positive, reached⟩ := Set.mem_iUnion₂.mp supported
    exact fixed_late_accepted_terminal profile (join false rest) owner (read false rest)
      ownerPolicy aliceWait bobWait final reached
  have mixture : app.runRounds scheduler players horizon initialExecution =
      (PMF.uniformOfFintype Bool).bind
        (fun bit => if bit then trueLaw else falseLaw) := by
    have realized := original_realize players horizon initialState
    change (seedPrior.bind fun seed =>
      app.runRounds (family seed) players horizon initialExecution) =
        app.runRounds scheduler players horizon initialExecution at realized
    rw [← realized, splitPrior]
    simp only [PMF.bind_bind, PMF.bind_map]
    apply bind_congr_on_support
    intro bit _
    cases bit <;> rfl
  change (1 / 2 : ℝ) ≤ ((app.runRounds scheduler players horizon initialExecution).toOuterMeasure
    accepted).toReal
  rw [mixture, toReal_toOuterMeasure_bind, expect_uniformOfFintype, Fintype.sum_bool]
  simp only [ite_true, Bool.false_eq_true, ite_false, Fintype.card_bool, falseAccepted,
    ENNReal.toReal_one]
  have positive : 0 ≤ (trueLaw.toOuterMeasure accepted).toReal := ENNReal.toReal_nonneg
  linarith


private theorem bob_correct_seed_continuation_mass
    (ownerPolicy : players bob = fixedLatePolicy bob)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (rest : BobSeedRest) (execution : app.Execution)
    (supported : (execution, rest) ∈ (beforeBobRemainderLaw players 12).support) :
    (app.runRounds (family (joinBobSeed false rest)) players 52 execution).toOuterMeasure
      {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob final} =
        1 := by
  rw [beforeBobRemainderLaw, PMF.support_bind] at supported
  obtain ⟨prior, _priorSupported, observed⟩ := Set.mem_iUnion₂.mp supported
  obtain ⟨before, reached, equal⟩ := PMF.support_map .. ▸ observed
  have sameExecution : before = execution := congrArg Prod.fst equal
  have sameRest : prior = rest := congrArg Prod.snd equal
  have prefixReached : execution ∈ (app.runRounds (family (joinBobSeed false rest)) players 12
      initialExecution).support := by
    simpa only [sameRest, sameExecution] using reached
  apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
  intro final future
  have whole : final ∈ (app.runRounds (family (joinBobSeed false rest)) players horizon
      initialExecution).support := by
    change final ∈ (app.runRounds (family (joinBobSeed false rest)) players (12 + 52)
      initialExecution).support
    rw [app.runRounds_add, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨execution, prefixReached, future⟩
  exact fixed_late_accepted_terminal profile (joinBobSeed false rest) bob
    (joinBobSeed_bit false rest) ownerPolicy aliceWait bobWait final whole

/-- The correct original Bob seed accepts on every supported continuation.
Any event determined before his first poll retains exactly its original weight
in the lower bound; no separate marginal probabilities are multiplied. -/
theorem bob_fixed_late_weighted_acceptance_probability
    (ownerPolicy : players bob = fixedLatePolicy bob)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (event : Set app.Execution) :
    (1 / 2) * ((app.runRounds scheduler players 12 initialExecution).toOuterMeasure
        event).toReal ≤
      ((bindPairLaw (app.runRounds scheduler players 12 initialExecution)
        (app.runRounds scheduler players 52)).toOuterMeasure
        {pair | pair.1 ∈ event ∧ PhaseService.BindingAccepted runtime leaks
          (originalCoordinate bob) bob pair.2}).toReal := by
  classical
  let remainders := beforeBobRemainderLaw players 12
  let accepted : Set app.Execution := {final |
    PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob final}
  let selected : Set (Bool × ((app.Execution × BobSeedRest) × app.Execution)) :=
    {outcome | outcome.2.1.1 ∈ event ∧ outcome.2.2 ∈ accepted}
  let branch := fun remainder : app.Execution × BobSeedRest =>
    (PMF.uniformOfFintype Bool).bind fun bit =>
      (app.runRounds (family (joinBobSeed bit remainder.2)) players 52 remainder.1).map
        fun final => (bit, remainder, final)
  have physical :
      (bindPairLaw (app.runRounds scheduler players 12 initialExecution)
        (app.runRounds scheduler players 52)).toOuterMeasure
          {pair | pair.1 ∈ event ∧ pair.2 ∈ accepted} =
        (bobPrefixFinalJoint players 52).toOuterMeasure selected := by
    rw [← bobPrefixFinalJoint_physical players 52, PMF.toOuterMeasure_map_apply]
    rfl
  have remainderPhysical : remainders.map Prod.fst =
      app.runRounds scheduler players 12 initialExecution := by
    calc
      _ = ((bindPairLaw (PMF.uniformOfFintype Bool) (fun _ => remainders)).map
          Prod.snd).map Prod.fst := by rw [bindPairLaw_map_snd, PMF.bind_const]
      _ = (beforeBobOriginalJoint players 12).map (fun outcome => outcome.2.1) := by
        rw [beforeBobOriginalJoint_eq players 12 le_rfl, PMF.map_comp]
        rfl
      _ = _ := beforeBobOriginalJoint_physical players 12
  have mapped (bit : Bool) (remainder : app.Execution × BobSeedRest) :
      ((app.runRounds (family (joinBobSeed bit remainder.2)) players 52 remainder.1).map
        (fun final => (bit, remainder, final))).toOuterMeasure selected =
          if remainder.1 ∈ event then
            (app.runRounds (family (joinBobSeed bit remainder.2)) players 52
              remainder.1).toOuterMeasure accepted else 0 := by
    have sets : (fun final : app.Execution => (bit, remainder, final)) ⁻¹' selected =
        if remainder.1 ∈ event then accepted else ∅ := by
      ext final
      by_cases member : remainder.1 ∈ event <;> simp [selected, member]
    rw [PMF.toOuterMeasure_map_apply, sets]
    by_cases member : remainder.1 ∈ event <;> simp [member]
  have branchMass (remainder : app.Execution × BobSeedRest) :
      ((branch remainder).toOuterMeasure selected).toReal =
        if remainder.1 ∈ event then
          (((app.runRounds (family (joinBobSeed false remainder.2)) players 52
              remainder.1).toOuterMeasure accepted).toReal +
            ((app.runRounds (family (joinBobSeed true remainder.2)) players 52
              remainder.1).toOuterMeasure accepted).toReal) / 2 else 0 := by
    dsimp only [branch]
    rw [toReal_toOuterMeasure_bind, expect_uniformOfFintype, Fintype.sum_bool]
    simp only [mapped, Fintype.card_bool]
    by_cases member : remainder.1 ∈ event
    · simp only [member, ite_true]
      ring
    · simp only [member, ite_false, ENNReal.toReal_zero, add_zero, zero_div]
  have branchBound (remainder : app.Execution × BobSeedRest)
      (supported : remainder ∈ remainders.support) :
      (if remainder.1 ∈ event then (1 / 2 : ℝ) else 0) ≤
        ((branch remainder).toOuterMeasure selected).toReal := by
    rw [branchMass]
    by_cases member : remainder.1 ∈ event
    · simp only [member, ite_true]
      have falseMass : (app.runRounds (family (joinBobSeed false remainder.2)) players 52
          remainder.1).toOuterMeasure accepted = 1 :=
        bob_correct_seed_continuation_mass profile ownerPolicy aliceWait bobWait
          remainder.2 remainder.1 supported
      rw [falseMass, ENNReal.toReal_one]
      have nonnegative : 0 ≤ ((app.runRounds (family (joinBobSeed true remainder.2)) players 52
          remainder.1).toOuterMeasure accepted).toReal := ENNReal.toReal_nonneg
      linarith
    · simp only [member, ite_false, le_refl]
  have bound := expect_mono branchBound
    (payoffIntegrable_of_bounded remainders
      (fun remainder => if remainder.1 ∈ event then (1 / 2 : ℝ) else 0)
      (C := 1) (by intro remainder; split_ifs <;> norm_num))
    (payoffIntegrable_toReal_toOuterMeasure remainders branch selected)
  have weight : (fun remainder : app.Execution × BobSeedRest =>
      if remainder.1 ∈ event then (1 / 2 : ℝ) else 0) =
        fun remainder => (1 / 2 : ℝ) * if remainder.1 ∈ event then 1 else 0 := by
    funext remainder
    split_ifs <;> norm_num
  rw [weight, expect_const_mul] at bound
  have indicator : expect remainders (fun remainder =>
      if remainder.1 ∈ event then (1 : ℝ) else 0) =
        (remainders.toOuterMeasure {remainder | remainder.1 ∈ event}).toReal :=
    expect_indicator remainders {remainder | remainder.1 ∈ event}
  rw [indicator] at bound
  have prefixMass : remainders.toOuterMeasure {remainder | remainder.1 ∈ event} =
      (app.runRounds scheduler players 12 initialExecution).toOuterMeasure event := by
    rw [← remainderPhysical, PMF.toOuterMeasure_map_apply]
    rfl
  rw [prefixMass] at bound
  change _ ≤ ((bindPairLaw (app.runRounds scheduler players 12 initialExecution)
    (app.runRounds scheduler players 52)).toOuterMeasure
      {pair | pair.1 ∈ event ∧ pair.2 ∈ accepted}).toReal
  rw [physical, bobPrefixFinalJoint_eq]
  change _ ≤ ((remainders.bind branch).toOuterMeasure selected).toReal
  rw [toReal_toOuterMeasure_bind]
  exact bound


end Counted

end Vegas.Examples.CommitSeedSignalling
