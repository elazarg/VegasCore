/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRoundTrace
import Vegas.Examples.SelectiveAssociation.SupportedResponses

/-! # Actual response and reserved inclusion inside the native round evaluator -/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem native_decoded_covered (profile : ∀ who, nativeModel.BehavioralPolicy who)
    (who : Player) (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (response : nativeApp.Action)
    (supported : response ∈ (nativeMenu.decodeProfile (PMF.pure nativeInitial)
      nativeHorizon nativeScheduler profile who past view).support) :
    response ∈ nativeMenu.actions who past view := by
  obtain ⟨choice, _, selected⟩ := native_response_supported_choice profile who past view
    response supported
  obtain ⟨action, member, value⟩ := choice.2
  have same := Option.some.inj (selected.symm.trans value)
  exact same.symm ▸ member

theorem native_run_trace (players : Player → nativeApp.Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ nativeMenu.actions who past view)
    (count : Nat) (bounded : count ≤ nativeHorizon) (execution : nativeApp.Execution)
    (supported : execution ∈
      (nativeApp.runRounds nativeScheduler players count nativeRoot).support) :
    Nonempty (nativeArena.Trace (some ⟨nativeHorizon - count, none, execution⟩)) := by
  apply nativeMenu.trace_roundsFrom (PMF.pure nativeInitial) nativeHorizon nativeScheduler
    players covered count bounded execution
  simpa only [ReactiveApplication.roundsFrom, PMF.pure_bind, nativeRoot] using supported

theorem native_run_cursor (players : Player → nativeApp.Policy)
    (count : Nat) (execution : nativeApp.Execution)
    (supported : execution ∈
      (nativeApp.runRounds nativeScheduler players count nativeRoot).support) :
    execution.environmentRecall.length = count := by
  apply nativeApp.roundsFrom_recall (PMF.pure nativeInitial) nativeScheduler players
    count execution
  simpa only [ReactiveApplication.roundsFrom, PMF.pure_bind, nativeRoot] using supported

theorem native_reserved_selected (event : nativeGraph.EventId) :
    nativePlan[(nativeBeforeResponse event).length + 1]? =
      some (.includeLatest event (nativeOwner event)) := by
  fin_cases event <;> rfl

/-- Decompose an actual two-round response/inclusion suffix. Earlier raw
responses remain unrestricted; the returned trace certifies the actual view. -/
theorem native_response_execution (players : Player → nativeApp.Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ nativeMenu.actions who past view)
    (event : nativeGraph.EventId) (before final : nativeApp.Execution)
    (beforeMem : before ∈ (nativeApp.runRounds nativeScheduler players
      (nativeBeforeResponse event).length nativeRoot).support)
    (finalMem : final ∈ (nativeApp.runRounds nativeScheduler players 2 before).support) :
    ∃ (observed : nativeApp.Execution) (response : nativeApp.Action),
      observed ∈ (before.environmentStep nativeApp (.activate (nativeOwner event))).support ∧
      response ∈ (players (nativeOwner event) (observed.recall (nativeOwner event))
        (observed.observe nativeApp (nativeOwner event))).support ∧
      (observed.recall (nativeOwner event)).length = nativeTurnCount event ∧
      Nonempty (nativeArena.Trace (some
        ⟨nativeHorizon - ((nativeBeforeResponse event).length + 1),
          some (nativeOwner event), observed⟩)) ∧
      final ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
        (.includeLatest event (nativeOwner event))
        (observed.respond nativeApp (nativeOwner event) response)).support := by
  let count := (nativeBeforeResponse event).length
  have beforeCursor := native_run_cursor players count before beforeMem
  have beforeBound : count + 2 ≤ nativeHorizon := by fin_cases event <;> decide
  obtain ⟨trace⟩ := native_run_trace players covered count (by omega) before beforeMem
  have playerRound : nativeApp.round nativeScheduler players before =
      (before.environmentStep nativeApp (.activate (nativeOwner event))).bind
        (nativeApp.invoke players (nativeOwner event)) := by
    simp only [ReactiveApplication.round, serviceScheduler, beforeCursor, count,
      native_response_selected, interactionInstruction, PMF.pure_bind,
      ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
    rfl
  change final ∈ ((nativeApp.round nativeScheduler players before).bind fun after =>
    (nativeApp.round nativeScheduler players after).bind PMF.pure).support at finalMem
  simp only [PMF.bind_pure] at finalMem
  rw [playerRound, PMF.bind_bind] at finalMem
  obtain ⟨observed, observedMem, finalMem⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ finalMem)
  rw [ReactiveApplication.invoke, PMF.bind_map] at finalMem
  obtain ⟨response, chosen, included⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ finalMem)
  refine ⟨observed, response, observedMem, chosen, ?_, ?_, ?_⟩
  · rw [nativeApp.environmentStep_recall before observed _ observedMem]
    have exactPrefix := native_roundsFrom_prefix players (nativeBeforeResponse event)
      (.player (nativeOwner event) :: nativeAfterResponse event) (native_response_split event)
    have reached : before ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
        (nativeBeforeResponse event) nativeRoot).support := by
      rw [← exactPrefix]
      simpa only [ReactiveApplication.roundsFrom, PMF.pure_bind, nativeRoot] using beforeMem
    simpa only [nativeTurnCount, nativeRoot, ReactiveApplication.Execution.initial,
      List.length_nil, Nat.zero_add] using native_plan_recall_count players _ nativeRoot before
        (nativeOwner event) reached
  · have remaining : nativeHorizon - count = nativeHorizon - (count + 1) + 1 := by omega
    apply nativeMenu.trace_environment (PMF.pure nativeInitial) nativeHorizon nativeScheduler
      (nativeHorizon - (count + 1)) before observed (.activate (nativeOwner event))
      (by rwa [← remaining]) _ observedMem
    simp only [serviceScheduler, beforeCursor, count, native_response_selected,
      interactionInstruction, PMF.mem_support_pure_iff _ _]
  · have observedCursor : observed.environmentRecall.length = count + 1 := by
      obtain ⟨next, _, rfl⟩ := PMF.support_map .. ▸ observedMem
      simp only [List.length_append, List.length_singleton]
      exact congrArg (· + 1) beforeCursor
    have respondedCursor :
        (observed.respond nativeApp (nativeOwner event) response).environmentRecall.length =
          count + 1 := by
      rw [nativeApp.respond_environmentRecall]
      exact observedCursor
    simpa only [ReactiveApplication.round, serviceScheduler, respondedCursor, count,
      native_reserved_selected, interactionStep, Function.comp_apply] using included

end Vegas.Examples.SelectiveAssociation
