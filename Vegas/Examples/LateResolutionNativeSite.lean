/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionContinuation
import Vegas.Pending.ReactiveRiskMenu
import Interaction.ReactiveRoundTrace

/-! # A legal native information site for the late-resolution continuation

The actual initialized silent prefix reaches the bounded risk menu's second
owner input. Its unrecorded resolution is unprotected, and evidence-free
withholding is a genuine available choice. These operational facts do not
assert a native sequential equilibrium or a preservation impossibility.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory.Math.Probability

abbrev nativeMenu (bounds : MessageBounds nativeGraph) :=
  bounds.riskMenu (runtime setup) leaks bound

abbrev nativeModel (bounds : MessageBounds nativeGraph) :=
  (nativeMenu bounds).information (initialLaw setup) horizon scheduler

theorem silence_risk (bounds : MessageBounds nativeGraph) (who : Player)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    (⟨none⟩ : app.Action) ∈ (nativeMenu bounds).actions who past view :=
  bounds.canonicalActions_subset_risk (runtime setup) leaks bound who past view
    (bounds.silence_canonical (runtime setup) leaks who past view)

theorem silent_risk_covered (bounds : MessageBounds nativeGraph) :
    ∀ who past view action, action ∈ (app.silentPolicy past view).support →
      action ∈ (nativeMenu bounds).actions who past view := by
  intro who past view action supported
  cases app.silentPolicy_cases past view action supported
  exact silence_risk bounds who past view

theorem exists_late_risk_turn (bounds : MessageBounds nativeGraph) :
    ∃ before execution : app.Execution,
      before ∈ (app.roundsFrom (initialLaw setup) scheduler
        (fun _ => app.silentPolicy) 5).support ∧
      (.activate owner : app.Command) ∈
        (scheduler before.environmentRecall (before.observeEnvironment app)).support ∧
      execution ∈ (before.environmentStep app (.activate owner)).support ∧
      Nonempty (((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨4, some owner, execution⟩)) ∧
      execution.environmentRecall.length = 6 ∧ execution.application.clock = 1 ∧
      execution.application.config.cut.Ready resolution ∧
      execution.application.activatedAt resolution = some 0 ∧
      execution.network = .empty := by
  obtain ⟨before, supported⟩ :=
    (app.roundsFrom (initialLaw setup) scheduler (fun _ => app.silentPolicy) 5).support_nonempty
  obtain ⟨trace⟩ := (nativeMenu bounds).trace_roundsFrom (initialLaw setup) horizon scheduler
    (fun _ => app.silentPolicy) (silent_risk_covered bounds) 5 (by decide) before supported
  have phase : Phase ⟨5, none, before⟩ :=
    phase_history ((nativeMenu bounds).toRawTrace (initialLaw setup) horizon scheduler trace)
  have position : before.environmentRecall.length = 5 := by
    have budget := phase.budget
    change 5 + before.environmentRecall.length = 10 at budget
    omega
  have unfinished := silent_rounds_unfinished 5 (by rfl) before supported
  have current : before.application.config.cut.IsPrefix 2 := by
    rcases phase.laterPrefix (by dsimp only; omega) with current | complete
    · exact current
    · exact (unfinished ((complete.2 resolution).mpr (by decide))).elim
  have ready := (ready_iff_rank setup _ 2 current resolution).mpr rfl
  have empty := silent_rounds_empty_network 5 before supported
  obtain ⟨after, moved⟩ := (before.environmentStep app (.activate owner)).support_nonempty
  have selected : (.activate owner : app.Command) ∈
      (scheduler before.environmentRecall (before.observeEnvironment app)).support := by
    simp only [scheduler, position, stageCommand, PMF.mem_support_pure_iff _ _]
  obtain ⟨afterTrace⟩ := (nativeMenu bounds).trace_environment (initialLaw setup) horizon scheduler
    4 before
    after (.activate owner) trace selected moved
  obtain ⟨updated, chosen, afterEq⟩ := PMF.support_map .. ▸ moved
  obtain ⟨sampled, sampleMem, updateEq⟩ := PMF.support_map .. ▸ chosen
  have sampledEq : sampled = ∅ := (PMF.mem_support_pure_iff _ _).mp sampleMem
  have applicationEq : after.application = before.application := by
    rw [← afterEq, ← updateEq]
  have nextPosition : after.environmentRecall.length = 6 := by
    rw [environmentStep_recall_append before after _ moved, List.length_append,
      List.length_singleton, position]
  refine ⟨before, after, supported, selected, moved, ⟨afterTrace⟩, nextPosition, ?_,
    applicationEq ▸ ready,
    applicationEq ▸ phase.entered current, ?_⟩
  · rw [applicationEq, phase.clock]
    change stageClock before.environmentRecall.length = 1
    rw [position]
    rfl
  · rw [← afterEq, ← updateEq]
    change before.network.learn owner sampled = .empty
    rw [sampledEq, MessageNetwork.learn_empty]
    exact empty

theorem empty_network_unrecorded (execution : app.Execution)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩)) (empty : execution.network = .empty) :
    (runtime setup).eventRecorded leaks (execution.recall owner) resolution = false := by
  have serials : execution.SerialRecall app :=
    app.serialRecall_history scheduler (initialLaw setup) horizon trace
  have serial := serials owner
  change execution.network.nextSerial owner = app.submissionCount (execution.recall owner)
    at serial
  rw [empty] at serial
  change 0 = (execution.recall owner).countP (fun entry => entry.action.isSubmission app)
    at serial
  have noSubmission := List.countP_eq_zero.mp serial.symm
  apply Bool.eq_false_of_not_eq_true
  intro recorded
  obtain ⟨entry, member, named⟩ :=
    ((runtime setup).eventRecorded_iff leaks _ resolution).mp recorded
  have absent := noSubmission entry member
  cases transmitted : entry.action.transmission with
  | none => simp [EventGraphRuntime.submittedEvent?, transmitted] at named
  | some submission =>
      simp [ReactiveApplication.Action.isSubmission, transmitted] at absent

theorem late_opportunity_risky (execution : app.Execution)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty) :
    (runtime setup).serviceRisk leaks bound owner (execution.recall owner)
      (execution.observe app owner) = true := by
  apply (runtime setup).serviceRisk_of_opportunity
  apply ((runtime setup).firstUnprotectedOpportunity_iff leaks bound owner _ _).mpr
  refine ⟨rfl, resolution, ?_, empty_network_unrecorded execution trace empty, ?_⟩
  · exact ownTurn?_of_ready setup execution.application ready resolution_actor
  · change ¬ match execution.application.activatedAt resolution with
      | none => False
      | some opened => execution.application.clock - opened + 2 < 3
    rw [entered, clock]
    decide

theorem late_withhold_available (bounds : MessageBounds nativeGraph) (execution : app.Execution)
    (trace : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty)
    (candidate : Handle nativeGraph) :
    lateResponse candidate false ∈ (nativeMenu bounds).actions owner
      (execution.recall owner) (execution.observe app owner) := by
  have rawTrace := (nativeMenu bounds).toRawTrace (initialLaw setup) horizon scheduler trace
  have risk := late_opportunity_risky execution rawTrace ready entered clock empty
  change lateResponse candidate false ∈ bounds.riskActions (runtime setup) leaks bound owner
    (execution.recall owner) (execution.observe app owner)
  rw [bounds.riskActions_of_risk _ _ _ _ _ _ risk, bounds.menu_mem]
  refine ⟨⟨⟨trivial, trivial⟩, trivial⟩, ?_⟩
  simp only [lateResponse, Bool.false_eq_true, ↓reduceIte,
    ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
    WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none,
    disclosureSubmission, EvidenceRequest.normalize_none]

/-- The real second input is a decision information site of the bounded risk
menu, with withholding available as an actual response. -/
theorem late_decision_site (bounds : MessageBounds nativeGraph) (execution : app.Execution)
    (trace : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩)) :
    (nativeModel bounds).IsDecisionInfo owner
      (some (execution.recall owner, execution.observe app owner)) := by
  let history : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History :=
    ⟨some ⟨4, some owner, execution⟩, trace⟩
  refine ⟨⟨history, ?_⟩, ?_, ⟨none⟩, ?_⟩
  · exact (nativeMenu bounds).info (initialLaw setup) horizon scheduler owner trace
  · change ¬ (4 = 0 ∧ (some owner : Option Player) = none)
    simp
  · exact ⟨⟨none⟩, silence_risk bounds owner _ _, rfl⟩

/-- The strictly improving withholding response and the forced silent law
belong to the same actual native input reached by a legal initialized prefix. -/
theorem exists_native_late_wait_regret (bounds : MessageBounds nativeGraph)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (positive : 0 < deposit) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) :
    ∃ (execution : app.Execution) (candidate : Handle nativeGraph),
      Nonempty (((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨4, some owner, execution⟩)) ∧
      (nativeModel bounds).IsDecisionInfo owner
        (some (execution.recall owner, execution.observe app owner)) ∧
      lateResponse candidate false ∈ (nativeMenu bounds).actions owner
        (execution.recall owner) (execution.observe app owner) ∧
      expect (((app.invoke
        (sourceServiceTurnPolicy setup leaks bound turns timing profile) owner execution).bind
        (app.runRounds scheduler (fun _ => app.silentPolicy) 4)).map app.finished)
        (fun final => auditedUtility sample deposit final owner) <
      expect ((app.runRounds scheduler (fun _ => app.silentPolicy) 4
        (execution.respond app owner (lateResponse candidate false))).map app.finished)
        (fun final => auditedUtility sample deposit final owner) := by
  obtain ⟨_before, execution, _prior, _selected, _moved, ⟨trace⟩, position, clock, ready,
      entered, empty⟩ := exists_late_risk_turn bounds
  have rawTrace := (nativeMenu bounds).toRawTrace (initialLaw setup) horizon scheduler trace
  obtain ⟨candidate, _, _, _⟩ := initial_binding_openable _ rawTrace
  refine ⟨execution, candidate, ⟨trace⟩, late_decision_site bounds execution trace,
    late_withhold_available bounds execution trace ready entered clock empty candidate, ?_⟩
  rw [late_prescription_value execution position ready entered clock empty turns timing
    profile sample deposit, late_continuation_value execution candidate rawTrace position ready
    entered clock empty sample authentic deposit false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  linarith

/-- A genuine positive geometric timing mass waits at an owner's first input,
independently of its source decision distribution. -/
theorem geometric_empty_wait_supported (turns : Nat) (later : 0 < turns)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1)
    (profile : BehavioralProfile setup.program) (who : Player) (view : app.PlayerView) :
    (⟨none⟩ : app.Action) ∈ (sourceServiceTurnPolicy setup leaks bound turns
      (geometricTiming setup turns weight positive.le below.le) profile who [] view).support := by
  unfold sourceServiceTurnPolicy
  split
  · exact app.silentPolicy_support [] view
  · rename_i event selected
    split
    · rename_i owned
      rw [ReactiveApplication.policyMixture_policy, PMF.support_bind]
      let slot : Fin (turns + 1) := ⟨turns, by omega⟩
      apply Set.mem_iUnion₂.mpr
      refine ⟨slot, ?_, ?_⟩
      · exact geometricTiming_fullSupport setup turns weight positive.le below.le positive below
          event who owned slot
      · simp [sourceServiceTurnFamily, ReactiveApplication.turnScheduledPolicy,
          sourceServiceTurn, selected, slot, Nat.ne_of_lt later]
    · exact app.silentPolicy_support [] view

/-- Every actual silent prefix before the second owner activation has positive
support under the real geometric turn policy. The only earlier strategic
response is the first owner input, whose recall is empty. -/
theorem silent_prefix_geometric_supported (turns : Nat) (later : 0 < turns)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1)
    (profile : BehavioralProfile setup.program) (count : Nat) (small : count ≤ 5)
    (execution : app.Execution)
    (supported : execution ∈ (app.roundsFrom (initialLaw setup) scheduler
      (fun _ => app.silentPolicy) count).support) :
    execution ∈ (app.roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns
        (geometricTiming setup turns weight positive.le below.le) profile) count).support := by
  let players := sourceServiceTurnPolicy setup leaks bound turns
    (geometricTiming setup turns weight positive.le below.le) profile
  induction count generalizing execution with
  | zero => exact supported
  | succ count ih =>
      rw [app.roundsFrom_succ (initialLaw setup) scheduler (fun _ => app.silentPolicy) count]
        at supported
      obtain ⟨before, prior, stepped⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      rw [app.roundsFrom_succ (initialLaw setup) scheduler players count, PMF.support_bind]
      apply Set.mem_iUnion₂.mpr
      refine ⟨before, ih (by omega) before prior, ?_⟩
      obtain ⟨command, selected, dispatched⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ stepped)
      obtain ⟨middle, moved, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      rw [ReactiveApplication.round, PMF.support_bind]
      apply Set.mem_iUnion₂.mpr
      refine ⟨command, selected, ?_⟩
      rw [ReactiveApplication.dispatch, PMF.support_bind]
      apply Set.mem_iUnion₂.mpr
      refine ⟨middle, moved, ?_⟩
      cases actor : command.actor? app with
      | none =>
          change execution ∈ (app.resume (fun _ => app.silentPolicy)
            (command.actor? app) middle).support at resumed
          simpa only [ReactiveApplication.resume, actor] using resumed
      | some who =>
          change execution ∈ (app.resume (fun _ => app.silentPolicy)
            (command.actor? app) middle).support at resumed
          rw [actor] at resumed
          obtain ⟨response, chosen, executionEq⟩ := PMF.support_map .. ▸ resumed
          have responseEq := app.silentPolicy_cases _ _ response chosen
          have own : who = owner := Subsingleton.elim _ _
          subst who
          obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
            (fun _ => app.silentPolicy) count (by dsimp [horizon]; omega) before prior
          have beforePhase := phase_history trace
          have position : before.environmentRecall.length = count := by
            have budget := beforePhase.budget
            change (10 - count) + before.environmentRecall.length = 10 at budget
            omega
          obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
            (9 - count) before middle command
            (by convert trace using 1; dsimp [horizon]; congr 2; omega) selected moved
          have phase := phase_history middleTrace
          have middlePosition : middle.environmentRecall.length = count + 1 := by
            rw [environmentStep_recall_append before middle command moved,
              List.length_append, List.length_singleton, position]
          have middleSmall : middle.environmentRecall.length ≤ 5 := by
            rw [middlePosition]
            exact small
          have activation : middle.environmentRecall.length = 3 := by
            rcases phase.activation (by rw [actor]; rfl) with first | second
            · exact first
            · change middle.environmentRecall.length = 6 at second
              omega
          have emptyRecall : middle.recall owner = [] := by
            apply List.eq_nil_of_length_eq_zero
            have length := phase.recallCount
            rw [activation, actor] at length
            change (middle.recall owner).length = 0 at length
            exact length
          change execution ∈ ((players owner (middle.recall owner)
            (middle.observe app owner)).map (middle.respond app owner)).support
          rw [PMF.support_map]
          refine ⟨⟨none⟩, ?_, ?_⟩
          · rw [emptyRecall]
            exact geometric_empty_wait_supported turns later weight positive below profile owner _
          · rw [← executionEq, responseEq]

/-- The same legal late native decision is supported by the actual initialized
geometric physical law, for every strictly positive deferral weight. This
asserts actual policy reach, independently of any native Bayes completion. -/
theorem exists_geometric_late_native_site (bounds : MessageBounds nativeGraph)
    (turns : Nat) (later : 0 < turns) (weight : ℝ) (positive : 0 < weight)
    (below : weight < 1) (profile : BehavioralProfile setup.program) :
    ∃ execution : app.Execution,
      Nonempty (((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨4, some owner, execution⟩)) ∧
      (nativeModel bounds).IsDecisionInfo owner
        (some (execution.recall owner, execution.observe app owner)) ∧
      app.RoundSupported (initialLaw setup) horizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns
          (geometricTiming setup turns weight positive.le below.le) profile)
        (some ⟨4, some owner, execution⟩) ∧
      execution.environmentRecall.length = 6 ∧ execution.application.clock = 1 ∧
      execution.application.config.cut.Ready resolution ∧
      execution.application.activatedAt resolution = some 0 ∧ execution.network = .empty := by
  obtain ⟨before, execution, prior, selected, moved, ⟨trace⟩, position, clock, ready,
      entered, empty⟩ := exists_late_risk_turn bounds
  refine ⟨execution, ⟨trace⟩, late_decision_site bounds execution trace, ?_,
    position, clock, ready, entered, empty⟩
  change execution.environmentRecall.length + 4 = 10 ∧ ∃ count prior command,
    execution.environmentRecall.length = count + 1 ∧
    prior ∈ (app.roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns
        (geometricTiming setup turns weight positive.le below.le) profile) count).support ∧
    command ∈ (scheduler prior.environmentRecall (prior.observeEnvironment app)).support ∧
    command.actor? app = some owner ∧
    execution ∈ (prior.environmentStep app command).support
  refine ⟨by omega, 5, before, .activate owner, position, ?_, selected, rfl, moved⟩
  exact silent_prefix_geometric_supported turns later weight positive below profile 5 (by rfl)
    before prior

end Vegas.LateResolutionService
