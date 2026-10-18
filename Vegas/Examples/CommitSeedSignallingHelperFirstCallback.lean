/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperPacketPermission
import Vegas.Examples.CommitSeedSignallingOriginalBindingExhaustion
import Interaction.ReactiveRoundTrace

/-! # The actual first informed callback after Bob sends the early helper -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

private theorem bob_early_family_trace (seed : Seeds) (material : app.Submission)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions bob []
      ((bobFirst ⟨none⟩).observe app bob)) :
    Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨62, none, (bobFirst ⟨none⟩).respond app bob ⟨some material⟩⟩)) := by
  obtain ⟨initialTrace⟩ := countedMenu.trace_initial initial horizon (family seed) initialState
    (by rw [initial_eq_pure]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  obtain ⟨first⟩ := countedMenu.trace_environment initial horizon (family seed) 63
    initialExecution aliceFirst (.activate alice) initialTrace
      (by rw [family_first]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
      (by rw [completeActivation_law]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seed) 63 aliceFirst
    alice ⟨none⟩ first (PhaseCount.silence_onePacket runtime leaks bounds alice _ _)
  obtain ⟨second⟩ := countedMenu.trace_environment initial horizon (family seed) 62
    (aliceResponded ⟨none⟩) (bobFirst ⟨none⟩) (.activate bob) responded
      (by rw [family_after_alice]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
      (by rw [completeActivation_law]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  exact countedMenu.trace_respond initial horizon (family seed) 62 (bobFirst ⟨none⟩) bob
    ⟨some material⟩ second offered

private theorem before_helper_command_passive (seed : Seeds) (extra : Nat)
    (early : extra < 2 + if seedBits seed alice then 2 else 0)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    (originalCommand seed (2 + extra) past view).actor? app = none ∧
      originalCommand seed (2 + extra) past view ≠ .application (.expire aliceBinding) := by
  cases bit : seedBits seed alice with
  | false =>
      simp only [bit, Bool.false_eq_true, ite_false] at early
      interval_cases extra <;> exact ⟨rfl, by intro impossible; cases impossible⟩
  | true =>
      simp only [bit, ite_true] at early
      interval_cases extra
      · exact ⟨rfl, by intro impossible; cases impossible⟩
      · exact ⟨rfl, by intro impossible; cases impossible⟩
      · change seed.2 (originalAddress alice) = true at bit
        simp only [originalCommand, pollCommand, bit, Bool.true_eq_false, ite_false]
        exact ⟨rfl, by intro impossible; cases impossible⟩
      · change (earlyCommand bob past view).actor? app = none ∧
          earlyCommand bob past view ≠ .application (.expire aliceBinding)
        unfold earlyCommand
        split
        · exact ⟨rfl, by intro impossible; cases impossible⟩
        · split
          · exact ⟨rfl, by intro impossible; cases impossible⟩
          · unfold pendingCommand
            split <;> exact ⟨rfl, by intro impossible; cases impossible⟩

/-- Before the first late Alice callback, her literal initial WAIT is still
her entire own word. The accepting Bob helper cannot consume her request. -/
theorem bob_early_before_helper (seed : Seeds) (material : app.Submission)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions bob []
      ((bobFirst ⟨none⟩).observe app bob))
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (extra : Nat) (early : extra ≤ 2 + if seedBits seed alice then 2 else 0)
    (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed) players extra
      ((bobFirst ⟨none⟩).respond app bob ⟨some material⟩)).support) :
    execution.application.SeedRequest alice (originalCoordinate alice) ∧
      execution.recall alice = [originalResponseEntry aliceFirst alice ⟨none⟩] := by
  classical
  let start := (bobFirst ⟨none⟩).respond app bob ⟨some material⟩
  obtain ⟨startTrace⟩ := bob_early_family_trace seed material offered
  have lengthStart : start.environmentRecall.length = 2 := by
    rw [ReactiveApplication.respond_environmentRecall, bobFirst_environmentRecall]
    rfl
  induction extra generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      refine ⟨respond_request runtime leaks (bobFirst ⟨none⟩) bob ⟨some material⟩ alice
        (originalCoordinate alice) (by
          change initialState.SeedRequest alice (originalCoordinate alice)
          exact initial_binding_request alice), ?_⟩
      change (start.recall alice) = _
      rw [app.respond_recall_other (bobFirst ⟨none⟩) bob alice (by decide)]
      change (aliceFirst.respond app alice ⟨none⟩).recall alice = _
      rw [respond_originalResponseEntry, aliceFirst_recall]
      rfl
  | succ extra ih =>
      rw [app.runRounds_succ_eq_bind_round, PMF.support_bind] at reached
      obtain ⟨before, prior, moved⟩ := Set.mem_iUnion₂.mp reached
      obtain ⟨request, recalled⟩ := ih (by omega) before prior
      have bounded : extra ≤ 62 := by
        have small : (if seedBits seed alice then 2 else 0) ≤ 2 := by split <;> omega
        omega
      have sourceTrace : (countedMenu.protocol initial horizon (family seed)).Trace
          (some ⟨(62 - extra) + extra, none, start⟩) := by
        rw [Nat.sub_add_cancel bounded]
        exact startTrace
      obtain ⟨beforeTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players
        covered (62 - extra) extra start before sourceTrace prior
      have raw := countedMenu.toRawTrace initial horizon (family seed) beforeTrace
      have length := app.runRounds_environmentRecall_length (family seed) players extra start
        before prior
      rw [lengthStart] at length
      obtain ⟨command, chosen, dispatched⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      have selected : command = originalCommand seed (2 + extra) before.environmentRecall
          (before.observeEnvironment app) := by
        rw [family_apply, choose_original seed _ _ request.1.symm, length] at chosen
        exact (PMF.mem_support_pure_iff _ _).mp chosen
      obtain ⟨passive, notExpiry⟩ := before_helper_command_passive seed extra (by omega)
        before.environmentRecall (before.observeEnvironment app)
      rw [← selected] at passive notExpiry
      obtain ⟨observed, environmentMoved, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      have unsent : ∀ message ∈ app.outputs (before.recall alice),
          PhaseCount.event? message.payload ≠ some (originalCoordinate alice) := by
        rw [recalled]
        simp only [ReactiveApplication.outputs, List.filterMap_cons, originalResponseEntry,
          Option.map_none, List.filterMap_nil]
        exact fun _ member => (List.not_mem_nil member).elim
      have requestAfter := (unsent_request_retained_or_expiry seed (62 - extra) before observed
        raw (originalCoordinate alice) alice request unsent command environmentMoved).resolve_right
          notExpiry
      simp only [ReactiveApplication.resume, passive, PMF.mem_support_pure_iff] at resumed
      subst execution
      exact ⟨requestAfter, (congrFun (app.environmentStep_recall before observed command
        environmentMoved) alice).trans recalled⟩

/-- The real early-helper prefix reaches Alice's first clock-two response.
Both seed placements retain the same earlier own word and an authentic visible
Bob envelope, with the same future response kernel. -/
theorem bob_early_first_helper_callback (seed : Seeds) (material : app.Submission)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions bob []
      ((bobFirst ⟨none⟩).observe app bob))
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (next : app.Execution)
    (reached : next ∈ (app.runRounds (family seed) players
      ((2 + if seedBits seed alice then 2 else 0) + 1)
        ((bobFirst ⟨none⟩).respond app bob ⟨some material⟩)).support) :
    ∃ before observed action marker,
      before ∈ (app.runRounds (family seed) players (2 + if seedBits seed alice then 2 else 0)
        ((bobFirst ⟨none⟩).respond app bob ⟨some material⟩)).support ∧
      observed = completeActivation before alice ∧
      family seed before.environmentRecall (before.observeEnvironment app) =
        PMF.pure (.activate alice) ∧
      Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
        (some ⟨61 - (2 + if seedBits seed alice then 2 else 0), some alice, observed⟩)) ∧
      observed.application.SeedRequest alice (originalCoordinate alice) ∧
      observed.application.current.native.clock = 2 ∧
      observed.recall alice = [originalResponseEntry aliceFirst alice ⟨none⟩] ∧
      marker ∈ observed.network.inputs ∧ marker.sender = bob ∧
      marker.payload.attempt = originalAttempt ∧
      (marker ∈ (observed.observe app alice).messages.leaked ∨
        marker ∈ (observed.observe app alice).messages.ledger) ∧
      action ∈ (players alice (observed.recall alice) (observed.observe app alice)).support ∧
      next = observed.respond app alice action := by
  classical
  let start := (bobFirst ⟨none⟩).respond app bob ⟨some material⟩
  let count := 2 + if seedBits seed alice then 2 else 0
  have bounded : count ≤ 4 := by dsimp only [count]; split <;> omega
  rw [app.runRounds_succ_eq_bind_round, PMF.support_bind] at reached
  obtain ⟨before, prior, moved⟩ := Set.mem_iUnion₂.mp reached
  obtain ⟨request, recalled⟩ := bob_early_before_helper seed material offered players covered count
    le_rfl before prior
  obtain ⟨startTrace⟩ := bob_early_family_trace seed material offered
  have sourceTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(62 - count) + count, none, start⟩) := by
    rw [Nat.sub_add_cancel (show count ≤ 62 by omega)]
    exact startTrace
  obtain ⟨beforeTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    (62 - count) count start before sourceTrace prior
  have raw := countedMenu.toRawTrace initial horizon (family seed) beforeTrace
  have length := app.runRounds_environmentRecall_length (family seed) players count start before
    prior
  have lengthStart : start.environmentRecall.length = 2 := by
    rw [ReactiveApplication.respond_environmentRecall, bobFirst_environmentRecall]
    rfl
  rw [lengthStart] at length
  have available : ready alice (bindingEvent alice) (before.observeEnvironment app) = true := by
    unfold ready
    change decide (PhaseRuntimeState.requests before.application.publicView alice
      ⟨before.application.attempt, bindingEvent alice⟩) = true
    have valid := raw_native_valid (family seed) ⟨62 - count, none, before⟩ raw
    have coordinateEq : (⟨before.application.attempt, bindingEvent alice⟩ :
        CommitAttemptEvent graph) = originalCoordinate alice := by
      rw [request.1.symm]
      rfl
    rw [coordinateEq]
    exact decide_eq_true ((before.application.requests_publicView valid alice
      (originalCoordinate alice)).mpr request)
  have command : family seed before.environmentRecall (before.observeEnvironment app) =
      PMF.pure (.activate alice) := by
    rw [family_apply, choose_original seed _ _ request.1.symm, length]
    cases bit : seedBits seed alice
    · change seed.2 (originalAddress alice) = false at bit
      simp only [count, seedBits, bit, Bool.false_eq_true, ite_false, originalCommand,
        pollCommand, ite_true, activateReady, available]
    · change seed.2 (originalAddress alice) = true at bit
      simp only [count, seedBits, bit, ite_true, originalCommand, pollCommand, activateReady,
        available]
  rw [ReactiveApplication.round, command, PMF.pure_bind, ReactiveApplication.dispatch,
    completeActivation_law, PMF.pure_bind] at moved
  obtain ⟨action, sampled, same⟩ := PMF.support_map .. ▸ moved
  let observed := completeActivation before alice
  have beforeBudget : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(61 - count) + 1, none, before⟩) := by
    rw [show (61 - count) + 1 = 62 - count by omega]
    exact beforeTrace
  have activated : observed ∈ (before.environmentStep app (.activate alice)).support := by
    rw [completeActivation_law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨observedTrace⟩ := countedMenu.trace_environment initial horizon (family seed)
    (61 - count) before observed (.activate alice) beforeBudget
      (by rw [command]; exact (PMF.mem_support_pure_iff _ _).mpr rfl) activated
  let entry := originalResponseEntry (bobFirst ⟨none⟩) bob ⟨some material⟩
  let marker : Message Player (CommitAttemptPacket graph) :=
    ⟨(bob, (bobFirst ⟨none⟩).network.nextSerial bob),
      app.packet (app.submit (bobFirst ⟨none⟩).application bob material) bob
        ((bobFirst ⟨none⟩).network.known bob) material⟩
  have emitted : entry.emitted = some marker := rfl
  have recorded : entry ∈ start.recall bob := by
    rw [respond_originalResponseEntry]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have retained := runRounds_recall_mono (family seed) players count start before prior bob recorded
  have input : marker ∈ before.network.inputs := by
    have output : marker ∈ app.outputs (before.recall bob) :=
      List.mem_filterMap.mpr ⟨entry, retained, emitted⟩
    rw [← app.history_inputRecall initial horizon (family seed) raw bob] at output
    exact (List.mem_filter.mp output).1
  have seen := app.complete_activation_submitted_visible rfl (family seed) initial horizon
    ⟨62 - count, none, before⟩ raw alice observed activated marker input
      (by change bob ≠ alice; decide)
  have afterInput : marker ∈ observed.network.inputs := input
  have addressed : marker.payload.attempt = originalAttempt := by
    change (((bobFirst ⟨none⟩).application.submit bob material).emit bob
      ((bobFirst ⟨none⟩).network.known bob) material).attempt = originalAttempt
    rw [PhaseCount.emit_after_submit]
    exact initialState_attempt
  have timer := original_clock_index seed ⟨62 - count, none, before⟩ raw request.1.symm
  have clock : observed.application.current.native.clock = 2 := by
    change before.application.current.native.clock = 2
    rw [timer, length]
    cases bit : seedBits seed alice <;> simp only [count, bit, Bool.false_eq_true, ite_false,
      ite_true] <;> rfl
  exact ⟨before, observed, action, marker, prior, rfl, command, ⟨observedTrace⟩, request, clock,
    recalled,
    afterInput, rfl, addressed, seen, sampled, same.symm⟩

end Vegas.Examples.CommitSeedSignalling
