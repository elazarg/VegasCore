/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHalfSuccess
import Vegas.Examples.CommitSeedSignallingBobJoint
import Vegas.Examples.CommitSeedSignallingPrePoll
import Vegas.Examples.CommitSeedSignallingResolvedContinuation
import Vegas.Examples.CommitSeedSignallingCountedContinuation
import GameTheory.Math.Probability.Uniform

/-! # Initialized original-seed bounds against actual counted continuations -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

section Counted

variable (profile : ∀ who, countedModel.BehavioralPolicy who)

local notation "players" => countedMenu.decodeProfile initial horizon scheduler profile

private theorem counted_profile_covered (owner : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) (action : app.Action)
    (supported : action ∈ (players owner past view).support) :
    action ∈ countedMenu.actions owner past view :=
  countedMenu.decode_embedPolicy_covered initial horizon scheduler owner (profile owner)
    past view action supported

theorem counted_profile_trace (seed : Seeds) (count : Nat) (bounded : count ≤ horizon)
    (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed) players count initialExecution).support) :
    Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨horizon - count, none, execution⟩)) := by
  apply countedMenu.trace_roundsFrom initial horizon (family seed) players
    (counted_profile_covered profile) count bounded execution
  simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind,
    initialExecution] using reached

theorem raw_counted_profile_trace (seed : Seeds) (count : Nat)
    (bounded : count ≤ horizon) (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed) players count initialExecution).support) :
    Nonempty ((rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨horizon - count, none, execution⟩)) := by
  obtain ⟨trace⟩ := counted_profile_trace profile seed count bounded execution reached
  exact ⟨countedInRaw.trace initial horizon (family seed) trace⟩

/-- The one-packet emission bound follows from the selected finite-menu
profile's actual initialized trace, including every earlier raw packet. -/
theorem counted_profile_emissions_one (seed : Seeds) (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed) players horizon initialExecution).support)
    (owner : Player) :
    (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
      execution.environmentRecall (execution.observeEnvironment app)).emissions.length ≤ 1 := by
  obtain ⟨trace⟩ := counted_profile_trace profile seed horizon le_rfl execution reached
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds (family seed)).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have rawTrace := countedMenu.toRawTrace initial horizon (family seed) trace
  have words := PhaseSeedScheduler.runRounds_wordRecall runtime leaks (family seed) players
    horizon initialExecution execution
    (PhaseSeedScheduler.initial_wordRecall runtime leaks initialState) reached
  have identified := app.input_identifier_injective_history initial horizon (family seed)
    ⟨horizon - horizon, none, execution⟩ rawTrace
  have identifiers : ∀ first ∈ execution.network.inputs, ∀ second ∈ execution.network.inputs,
      first.id = second.id → first = second := by
    intro first firstMember second secondMember same
    exact identified first second firstMember secondMember same
  cases emissions : (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
      execution.environmentRecall (execution.observeEnvironment app)).emissions with
  | nil => simp only [List.length_nil, Nat.zero_le]
  | cons first rest =>
      have member : first ∈ (PhaseSeedScheduler.localInput runtime leaks
          (originalCoordinate owner) owner execution.environmentRecall
          (execution.observeEnvironment app)).emissions := by
        rw [emissions]
        exact List.mem_cons_self
      have singleton := PhaseSeedScheduler.localInput_emissions_eq_singleton runtime leaks
        execution (originalCoordinate owner) owner words clean identifiers first.1 first.2 member
      have same : first :: rest = [(first.1, first.2)] := emissions.symm.trans singleton
      rw [same]
      simp only [List.length_singleton, le_refl]

theorem quiet_snapshot_empty
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (seed : Seeds) (count : Nat) (late : 3 ≤ count) (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed) players count initialExecution).support)
    (owner : Player) :
    ∀ entry, execution.environmentRecall[2]? = some entry →
      ∀ message ∈ entry.beforeView.network.inputs, message.sender ≠ owner := by
  have supported : execution ∈ (app.runRounds (family seed) players (3 + (count - 3))
      initialExecution).support := by
    rwa [show 3 + (count - 3) = count by omega]
  intro entry selected message member
  rw [quiet_prefix_snapshot players seed aliceWait bobWait (count - 3) execution supported
    entry selected] at member
  exact (List.not_mem_nil member).elim

/-- The conditional late bound holds at every physical prefix in the original
initialized remainder law. Resolved prefixes are derived zero-acceptance
branches; unresolved prefixes supply the genuine ready native request. -/
theorem bob_initialized_prefix_half
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (rest : BobSeedRest) (execution : app.Execution)
    (reachedPrefix : execution ∈ (app.runRounds (family (joinBobSeed false rest)) players 12
      initialExecution).support) :
    (((app.runRounds (family (joinBobSeed false rest)) players 52 execution).toOuterMeasure
        {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate bob)
          bob final}).toReal +
      ((app.runRounds (family (joinBobSeed true rest)) players 52 execution).toOuterMeasure
        {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate bob)
          bob final}).toReal) / 2 ≤ 1 / 2 := by
  classical
  have prefixTrue : execution ∈ (app.runRounds (family (joinBobSeed true rest)) players 12
      initialExecution).support := by
    rw [run_before_bob_seed players 12 (by omega) true rest]
    exact reachedPrefix
  have prefixAny (bit : Bool) : execution ∈
      (app.runRounds (family (joinBobSeed bit rest)) players 12 initialExecution).support := by
    rw [run_before_bob_seed players 12 (by omega) bit rest]
    exact reachedPrefix
  have count : execution.environmentRecall.length = 12 := by
    have length := app.runRounds_environmentRecall_length (family (joinBobSeed false rest))
      players 12 initialExecution execution reachedPrefix
    simpa only [initialExecution, ReactiveApplication.Execution.initial, List.length_nil,
      Nat.zero_add] using length
  have whole (bit : Bool) (final : app.Execution)
      (reached : final ∈ (app.runRounds (family (joinBobSeed bit rest)) players 52
        execution).support) :
      final ∈ (app.runRounds (family (joinBobSeed bit rest)) players horizon
        initialExecution).support := by
    change final ∈ (app.runRounds (family (joinBobSeed bit rest)) players (12 + 52)
      initialExecution).support
    rw [app.runRounds_add, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨execution, prefixAny bit, reached⟩
  obtain ⟨falseTrace⟩ := raw_counted_profile_trace profile (joinBobSeed false rest) 12
    (by decide) execution reachedPrefix
  obtain ⟨trueTrace⟩ := raw_counted_profile_trace profile (joinBobSeed true rest) 12
    (by decide) execution prefixTrue
  have falseTrace : (rawMenu.protocol initial horizon (family (joinBobSeed false rest))).Trace
      (some ⟨52, none, execution⟩) := falseTrace
  have trueTrace : (rawMenu.protocol initial horizon (family (joinBobSeed true rest))).Trace
      (some ⟨52, none, execution⟩) := trueTrace
  have empty := quiet_snapshot_empty profile aliceWait bobWait (joinBobSeed false rest)
    12 (by decide) execution reachedPrefix bob
  by_cases resolved : (originalCoordinate bob).Resolved execution.application
  · have unaccepted := bob_binding_unaccepted_before_poll (joinBobSeed false rest) 52 execution
      falseTrace (by omega) empty
    have zero (bit : Bool) :
        (app.runRounds (family (joinBobSeed bit rest)) players 52 execution).toOuterMeasure
          {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate bob)
            bob final} = 0 := by
      by_contra positive
      obtain ⟨final, accepted, reached⟩ := (toOuterMeasure_ne_zero_iff _ _).mp positive
      have trace : (rawMenu.protocol initial horizon (family (joinBobSeed bit rest))).Trace
          (some ⟨52, none, execution⟩) := by
        cases bit
        · exact falseTrace
        · exact trueTrace
      exact resolved_unaccepted_binding_stays_unaccepted (family (joinBobSeed bit rest))
        players 52 52 execution final
        (rawMenu.toRawTrace initial horizon (family (joinBobSeed bit rest)) trace)
        le_rfl reached bob resolved unaccepted accepted
    rw [zero false, zero true]
    norm_num
  · have nativeTrace := rawMenu.toRawTrace initial horizon (family (joinBobSeed false rest))
      falseTrace
    have request := original_binding_request_of_unresolved (family (joinBobSeed false rest))
      ⟨52, none, execution⟩ nativeTrace bob resolved
    have original : execution.application.attempt = originalAttempt := request.1.symm
    have clock := original_clock_index (joinBobSeed false rest) ⟨52, none, execution⟩
      nativeTrace original
    rw [count] at clock
    have timer := original_timer (family (joinBobSeed false rest)) ⟨52, none, execution⟩
      nativeTrace original (bindingEvent bob) (Or.inr rfl) request.2.2.1.1
    have ready : ready bob (bindingEvent bob) (execution.observeEnvironment app) = true := by
      change decide (PhaseRuntimeState.requests execution.application.publicView bob
        ⟨execution.application.attempt, bindingEvent bob⟩) = true
      apply decide_eq_true
      apply (execution.application.requests_publicView
        (raw_native_valid (family (joinBobSeed false rest)) ⟨52, none, execution⟩ nativeTrace)
          bob _).mpr
      simpa only [originalCoordinate, original] using request
    apply original_nohelper_acceptance_half (joinBobSeed false rest) (joinBobSeed true rest)
      players bob 49 execution
      (by exact joinBobSeed_bit false rest) (by exact joinBobSeed_bit true rest)
      original count clock timer ready
      (quiet_prefix_earlyCommand players (joinBobSeed false rest) aliceWait bobWait 9 execution
        reachedPrefix (markerOwner bob))
    · intro final reached
      obtain ⟨trace⟩ := raw_counted_profile_trace profile (joinBobSeed false rest) horizon
        le_rfl final (whole false final reached)
      exact ⟨by simpa only [Nat.sub_self] using trace⟩
    · intro final reached
      obtain ⟨trace⟩ := raw_counted_profile_trace profile (joinBobSeed true rest) horizon
        le_rfl final (whole true final reached)
      exact ⟨by simpa only [Nat.sub_self] using trace⟩
    · intro final reached
      exact quiet_snapshot_empty profile aliceWait bobWait (joinBobSeed false rest) horizon
        (by decide) final (whole false final reached) bob
    · intro final reached
      exact quiet_snapshot_empty profile aliceWait bobWait (joinBobSeed true rest) horizon
        (by decide) final (whole true final reached) bob
    · intro final reached
      exact counted_profile_emissions_one profile (joinBobSeed true rest) final
        (whole true final reached) bob

private theorem bob_initialized_remainder_half
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (rest : BobSeedRest) (execution : app.Execution)
    (supported : (execution, rest) ∈ (beforeBobRemainderLaw players 12).support) :
    (((app.runRounds (family (joinBobSeed false rest)) players 52
          execution).toOuterMeasure
        {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate bob)
          bob final}).toReal +
      ((app.runRounds (family (joinBobSeed true rest)) players 52
          execution).toOuterMeasure
        {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate bob)
          bob final}).toReal) / 2 ≤ 1 / 2 := by
  rw [beforeBobRemainderLaw, PMF.support_bind] at supported
  obtain ⟨prior, _priorSupported, observed⟩ := Set.mem_iUnion₂.mp supported
  obtain ⟨before, reached, equal⟩ := PMF.support_map .. ▸ observed
  have sameExecution : before = execution := congrArg Prod.fst equal
  have sameRest : prior = rest := congrArg Prod.snd equal
  have prefixReached : execution ∈ (app.runRounds (family (joinBobSeed false rest)) players 12
      initialExecution).support := by
    simpa only [sameRest, sameExecution] using reached
  exact bob_initialized_prefix_half profile aliceWait bobWait rest execution prefixReached

/-- A physical event fixed before Bob's polls is retained jointly in the
half bound. In particular earlier Alice delivery need not be independent of
the updated remainder; it can be the event selected here. -/
theorem bob_initialized_weighted_half
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (event : Set app.Execution) :
    ((bindPairLaw (app.runRounds scheduler players 12 initialExecution)
        (app.runRounds scheduler players 52)).toOuterMeasure
      {pair | pair.1 ∈ event ∧ PhaseService.BindingAccepted runtime leaks
        (originalCoordinate bob) bob pair.2}).toReal ≤
      (1 / 2) * ((app.runRounds scheduler players 12 initialExecution).toOuterMeasure
        event).toReal := by
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
      ((branch remainder).toOuterMeasure selected).toReal ≤
        if remainder.1 ∈ event then (1 / 2 : ℝ) else 0 := by
    rw [branchMass]
    by_cases member : remainder.1 ∈ event
    · simp only [member, ite_true]
      have half :
          (((app.runRounds (family (joinBobSeed false remainder.2)) players 52
                remainder.1).toOuterMeasure accepted).toReal +
            ((app.runRounds (family (joinBobSeed true remainder.2)) players 52
                remainder.1).toOuterMeasure accepted).toReal) / 2 ≤ 1 / 2 :=
        bob_initialized_remainder_half profile aliceWait bobWait remainder.2 remainder.1 supported
      exact half
    · simp only [member, ite_false, le_refl]
  have bound := expect_mono branchBound
    (payoffIntegrable_toReal_toOuterMeasure remainders branch selected)
    (payoffIntegrable_of_bounded remainders
      (fun remainder => if remainder.1 ∈ event then (1 / 2 : ℝ) else 0)
      (C := 1) (by intro remainder; split_ifs <;> norm_num))
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
  change ((bindPairLaw (app.runRounds scheduler players 12 initialExecution)
    (app.runRounds scheduler players 52)).toOuterMeasure
      {pair | pair.1 ∈ event ∧ pair.2 ∈ accepted}).toReal ≤ _
  rw [physical, bobPrefixFinalJoint_eq]
  change ((remainders.bind branch).toOuterMeasure selected).toReal ≤ _
  rw [toReal_toOuterMeasure_bind]
  exact bound

end Counted

/-- Sequential rationality supplies the counted opponents used above on the
actual initialized native experiment. The focal replacement is the original
physical policy and the target opponents remain the assessed raw strategy. -/
theorem raw_equilibrium_initialized_counted_run
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ countedMenu.actions who past view) :
    app.runRounds scheduler
        (countedMenu.decodeProfile initial horizon scheduler
          (Function.update (countedAssessmentProfile assessment) who
            (countedMenu.restrictPolicy initial horizon scheduler who policy)))
        horizon initialExecution =
      app.runRounds scheduler
        (Function.update (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
          who policy) horizon initialExecution := by
  have enough : app.rank horizon countedProtocol.initHistory.state ≤ 2 * horizon + 1 := le_rfl
  have source := countedMenu.run_eq_finish initial horizon scheduler
    (Function.update (countedAssessmentProfile assessment) who
      (countedMenu.restrictPolicy initial horizon scheduler who policy))
    (2 * horizon + 1) countedProtocol.initHistory enough
  have target := countedInRaw.runFrom_restrictPolicy_finish initial horizon scheduler
    (countedAssessmentProfile assessment) assessment.strategy
    (raw_equilibrium_extends_counted assessment equilibrium) who policy covered
    (2 * horizon + 1) countedProtocol.initHistory enough
  have law := source.symm.trans target
  change app.finish initial horizon scheduler
      (countedMenu.decodeProfile initial horizon scheduler
        (Function.update (countedAssessmentProfile assessment) who
          (countedMenu.restrictPolicy initial horizon scheduler who policy))) none =
    app.finish initial horizon scheduler
      (Function.update (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        who policy) none at law
  have executions := congrArg (fun distribution : PMF app.ProtocolState =>
    distribution.map (fun state => state.elim initialExecution (fun current =>
      current.execution))) law
  simp only [ReactiveApplication.finish, initial_eq_pure,
    PMF.pure_bind, PMF.map_comp, Function.comp_def, ReactiveApplication.finished,
    Option.elim_some] at executions
  change (app.runRounds scheduler
      (countedMenu.decodeProfile initial horizon scheduler
        (Function.update (countedAssessmentProfile assessment) who
          (countedMenu.restrictPolicy initial horizon scheduler who policy)))
      horizon initialExecution).map id =
    (app.runRounds scheduler
      (Function.update (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        who policy) horizon initialExecution).map id at executions
  simpa only [PMF.map_id] using executions

end Vegas.Examples.CommitSeedSignalling
