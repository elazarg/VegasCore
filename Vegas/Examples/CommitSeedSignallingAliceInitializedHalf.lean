/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingInitializedHalf
import Vegas.Examples.CommitSeedSignallingAlicePrePoll

/-! # Alice's initialized no-helper delivery bound -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

abbrev AliceSeedRest := {address : PhaseSeedAddress graph //
  address ≠ originalAddress alice} → Bool

def joinAliceSeed (bit : Bool) (rest : AliceSeedRest) : Seeds :=
  ((), (Equiv.piSplitAt (originalAddress alice) (fun _ : PhaseSeedAddress graph => Bool)).symm
    (bit, rest))

def aliceSeedRestLaw : PMF AliceSeedRest :=
  independentProduct fun address : {address : PhaseSeedAddress graph //
    address ≠ originalAddress alice} => seedLaws address

theorem joinAliceSeed_bit (bit : Bool) (rest : AliceSeedRest) :
    seedBits (joinAliceSeed bit rest) alice = bit := by
  have same := (Equiv.piSplitAt (originalAddress alice)
    (fun _ : PhaseSeedAddress graph => Bool)).apply_symm_apply (bit, rest)
  exact congrArg Prod.fst same

theorem seedPrior_split_alice : seedPrior =
    (PMF.uniformOfFintype Bool).bind fun bit => aliceSeedRestLaw.map (joinAliceSeed bit) := by
  unfold seedPrior
  rw [independentProduct_splitAt seedLaws (originalAddress alice)]
  simp only [seedLaws_original, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rfl

section Counted

variable (profile : ∀ who, countedModel.BehavioralPolicy who)

local notation "players" => countedMenu.decodeProfile initial horizon scheduler profile

/-- Before Alice's first poll the complete physical prefix has not read either
original bit. Both branches below retain all other original seed addresses. -/
theorem alice_initialized_prefix_half
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (rest : AliceSeedRest) (execution : app.Execution)
    (reachedPrefix : execution ∈ (app.runRounds (family (seedOfBits fun _ => false))
      players 4 initialExecution).support) :
    (((app.runRounds (family (joinAliceSeed false rest)) players 60 execution).toOuterMeasure
        {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate alice)
          alice final}).toReal +
      ((app.runRounds (family (joinAliceSeed true rest)) players 60 execution).toOuterMeasure
        {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate alice)
          alice final}).toReal) / 2 ≤ 1 / 2 := by
  classical
  have prefixAny (bit : Bool) : execution ∈
      (app.runRounds (family (joinAliceSeed bit rest)) players 4 initialExecution).support := by
    rw [run_before_alice_seed players 4 le_rfl (joinAliceSeed bit rest)
      (seedOfBits fun _ => false)]
    exact reachedPrefix
  have count : execution.environmentRecall.length = 4 := by
    have length := app.runRounds_environmentRecall_length (family (seedOfBits fun _ => false))
      players 4 initialExecution execution reachedPrefix
    simpa only [initialExecution, ReactiveApplication.Execution.initial, List.length_nil,
      Nat.zero_add] using length
  have whole (bit : Bool) (final : app.Execution)
      (reached : final ∈ (app.runRounds (family (joinAliceSeed bit rest)) players 60
        execution).support) :
      final ∈ (app.runRounds (family (joinAliceSeed bit rest)) players horizon
        initialExecution).support := by
    change final ∈ (app.runRounds (family (joinAliceSeed bit rest)) players (4 + 60)
      initialExecution).support
    rw [app.runRounds_add, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨execution, prefixAny bit, reached⟩
  obtain ⟨falseTrace⟩ := raw_counted_profile_trace profile (joinAliceSeed false rest) 4
    (by decide) execution (prefixAny false)
  obtain ⟨trueTrace⟩ := raw_counted_profile_trace profile (joinAliceSeed true rest) 4
    (by decide) execution (prefixAny true)
  have falseTrace : (rawMenu.protocol initial horizon (family (joinAliceSeed false rest))).Trace
      (some ⟨60, none, execution⟩) := falseTrace
  have trueTrace : (rawMenu.protocol initial horizon (family (joinAliceSeed true rest))).Trace
      (some ⟨60, none, execution⟩) := trueTrace
  have empty := quiet_snapshot_empty profile aliceWait bobWait (joinAliceSeed false rest)
    4 (by decide) execution (prefixAny false) alice
  by_cases resolved : (originalCoordinate alice).Resolved execution.application
  · have unaccepted := alice_binding_unaccepted_before_poll (joinAliceSeed false rest) 60
      execution falseTrace (by omega) empty
    have zero (bit : Bool) :
        (app.runRounds (family (joinAliceSeed bit rest)) players 60 execution).toOuterMeasure
          {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate alice)
            alice final} = 0 := by
      by_contra positive
      obtain ⟨final, accepted, reached⟩ := (toOuterMeasure_ne_zero_iff _ _).mp positive
      have trace : (rawMenu.protocol initial horizon (family (joinAliceSeed bit rest))).Trace
          (some ⟨60, none, execution⟩) := by
        cases bit
        · exact falseTrace
        · exact trueTrace
      exact resolved_unaccepted_binding_stays_unaccepted (family (joinAliceSeed bit rest))
        players 60 60 execution final
        (rawMenu.toRawTrace initial horizon (family (joinAliceSeed bit rest)) trace)
        le_rfl reached alice resolved unaccepted accepted
    rw [zero false, zero true]
    norm_num
  · have nativeTrace := rawMenu.toRawTrace initial horizon (family (joinAliceSeed false rest))
      falseTrace
    have request := original_binding_request_of_unresolved (family (joinAliceSeed false rest))
      ⟨60, none, execution⟩ nativeTrace alice resolved
    have original : execution.application.attempt = originalAttempt := request.1.symm
    have clock := original_clock_index (joinAliceSeed false rest) ⟨60, none, execution⟩
      nativeTrace original
    rw [count] at clock
    have timer := original_timer (family (joinAliceSeed false rest)) ⟨60, none, execution⟩
      nativeTrace original (bindingEvent alice) (Or.inl rfl) request.2.2.1.1
    have ready : ready alice (bindingEvent alice) (execution.observeEnvironment app) = true := by
      change decide (PhaseRuntimeState.requests execution.application.publicView alice
        ⟨execution.application.attempt, bindingEvent alice⟩) = true
      apply decide_eq_true
      apply (execution.application.requests_publicView
        (raw_native_valid (family (joinAliceSeed false rest)) ⟨60, none, execution⟩ nativeTrace)
          alice _).mpr
      simpa only [originalCoordinate, original] using request
    apply original_nohelper_acceptance_half (joinAliceSeed false rest) (joinAliceSeed true rest)
      players alice 57 execution (joinAliceSeed_bit false rest) (joinAliceSeed_bit true rest)
      original count clock timer ready
      (quiet_prefix_earlyCommand players (joinAliceSeed false rest) aliceWait bobWait 1 execution
        (prefixAny false) (markerOwner alice))
    · intro final reached
      obtain ⟨trace⟩ := raw_counted_profile_trace profile (joinAliceSeed false rest) horizon
        le_rfl final (whole false final reached)
      exact ⟨by simpa only [Nat.sub_self] using trace⟩
    · intro final reached
      obtain ⟨trace⟩ := raw_counted_profile_trace profile (joinAliceSeed true rest) horizon
        le_rfl final (whole true final reached)
      exact ⟨by simpa only [Nat.sub_self] using trace⟩
    · intro final reached
      exact quiet_snapshot_empty profile aliceWait bobWait (joinAliceSeed false rest) horizon
        (by decide) final (whole false final reached) alice
    · intro final reached
      exact quiet_snapshot_empty profile aliceWait bobWait (joinAliceSeed true rest) horizon
        (by decide) final (whole true final reached) alice
    · intro final reached
      exact counted_profile_emissions_one profile (joinAliceSeed true rest) final
        (whole true final reached) alice

/-- Averaging uses the original initialized seed experiment. No belief at a
deviation-reached late input is substituted for the physical continuation. -/
theorem alice_initialized_half
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩) :
    ((app.runRounds scheduler players horizon initialExecution).toOuterMeasure
      {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate alice)
        alice final}).toReal ≤ 1 / 2 := by
  classical
  let accepted : Set app.Execution := {final |
    PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice final}
  let prefixes := app.runRounds (family (seedOfBits fun _ => false)) players 4 initialExecution
  let branch := fun execution : app.Execution => aliceSeedRestLaw.bind fun rest =>
    (PMF.uniformOfFintype Bool).bind fun bit =>
      app.runRounds (family (joinAliceSeed bit rest)) players 60 execution
  have mixture : app.runRounds scheduler players horizon initialExecution =
      prefixes.bind branch := by
    have realized := original_realize players horizon initialState
    change (seedPrior.bind fun seed =>
      app.runRounds (family seed) players horizon initialExecution) =
        app.runRounds scheduler players horizon initialExecution at realized
    rw [← realized, seedPrior_split_alice]
    simp only [PMF.bind_bind, PMF.bind_map]
    change ((PMF.uniformOfFintype Bool).bind fun bit => aliceSeedRestLaw.bind fun rest =>
      app.runRounds (family (joinAliceSeed bit rest)) players (4 + 60) initialExecution) = _
    simp_rw [app.runRounds_add,
      run_before_alice_seed players 4 le_rfl _ (seedOfBits fun _ => false)]
    calc
      _ = (PMF.uniformOfFintype Bool).bind (fun bit => prefixes.bind fun execution =>
          aliceSeedRestLaw.bind fun rest =>
            app.runRounds (family (joinAliceSeed bit rest)) players 60 execution) := by
        apply bind_congr_on_support
        intro bit _
        exact PMF.bind_comm ..
      _ = prefixes.bind (fun execution => (PMF.uniformOfFintype Bool).bind fun bit =>
          aliceSeedRestLaw.bind fun rest =>
            app.runRounds (family (joinAliceSeed bit rest)) players 60 execution) :=
        PMF.bind_comm ..
      _ = _ := by
        apply bind_congr_on_support
        intro execution _
        exact PMF.bind_comm ..
  have branchBound (execution : app.Execution) (reached : execution ∈ prefixes.support) :
      ((branch execution).toOuterMeasure accepted).toReal ≤ 1 / 2 := by
    have bitMass (rest : AliceSeedRest) :
        (((PMF.uniformOfFintype Bool).bind fun bit =>
          app.runRounds (family (joinAliceSeed bit rest)) players 60 execution).toOuterMeasure
            accepted).toReal ≤ 1 / 2 := by
      rw [toReal_toOuterMeasure_bind, expect_uniformOfFintype, Fintype.sum_bool]
      simp only [Fintype.card_bool]
      have bound := alice_initialized_prefix_half profile aliceWait bobWait rest execution reached
      change (_ + _) / 2 ≤ 1 / 2 at bound
      linarith
    have bound := expect_mono (fun rest _ => bitMass rest)
      (payoffIntegrable_toReal_toOuterMeasure aliceSeedRestLaw
        (fun rest => (PMF.uniformOfFintype Bool).bind fun bit =>
          app.runRounds (family (joinAliceSeed bit rest)) players 60 execution) accepted)
      (payoffIntegrable_constant aliceSeedRestLaw (1 / 2))
    rw [expect_constant] at bound
    change ((aliceSeedRestLaw.bind _).toOuterMeasure accepted).toReal ≤ _
    rw [toReal_toOuterMeasure_bind]
    exact bound
  have bound := expect_mono branchBound
    (payoffIntegrable_toReal_toOuterMeasure prefixes branch accepted)
    (payoffIntegrable_constant prefixes (1 / 2))
  rw [expect_constant] at bound
  change ((app.runRounds scheduler players horizon initialExecution).toOuterMeasure
    accepted).toReal ≤ _
  rw [mixture, toReal_toOuterMeasure_bind]
  exact bound

end Counted

end Vegas.Examples.CommitSeedSignalling
