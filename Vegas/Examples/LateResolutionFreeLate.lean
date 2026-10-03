/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionNativePerturbation

/-! # Every late raw response has a failure-valued terminal source result

The concrete service includes only withholding on this turn. Other packet
constructors remain pending until expiry. This is an actual operational law,
including rejected packets and arbitrary private evidence.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory GameTheory.Math.Probability

theorem latestWithhold_cases (view : app.EnvironmentView) :
    latestWithhold view = .wait ∨ ∃ message : Message Player (WitnessedPacket nativeGraph),
      message ∈ view.network.pending ∧ message.sender = owner ∧
      message.payload.call = .withhold resolution ∧ latestWithhold view = .include message.id := by
  classical
  unfold latestWithhold
  cases found : view.network.pending.reverse.find? (fun message =>
      decide (message.sender = owner ∧ message.payload.call = .withhold resolution ∧
        view.Unpublished app message.id)) with
  | none => exact Or.inl rfl
  | some message =>
      have selectedBool := (List.find?_eq_some_iff_append.mp found).1
      have selected := of_decide_eq_true selectedBool
      exact Or.inr ⟨message, List.mem_reverse.mp (List.mem_of_find?_eq_some found),
        selected.1, selected.2.1, rfl⟩

theorem late_selection_application (execution : app.Execution)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, none, execution⟩))
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (next : app.Execution)
    (moved : next ∈ (execution.environmentStep app
      (latestWithhold (execution.observeEnvironment app))).support) :
    next.application = execution.application ∨ next.application = failureState execution ready := by
  rcases latestWithhold_cases (execution.observeEnvironment app) with waited |
      ⟨message, pending, sender, call, included⟩
  · rw [waited, wait_environment] at moved
    cases (PMF.mem_support_pure_iff _ _).mp moved
    exact Or.inl rfl
  · rw [included, include_environment] at moved
    cases (PMF.mem_support_pure_iff _ _).mp moved
    have facts := legalFacts setup leaks horizon scheduler ⟨4, none, execution⟩ trace
    have audit := (app.submissionAudit_history ReactivePlayerView.publicView (fun _ _ => rfl)
      (initialLaw setup) horizon scheduler trace).1
    have looked := audit.lookup_of_mem app ReactivePlayerView.publicView execution message pending
    have timely : execution.application.WithinDeadline (runtime setup) resolution := by
      simp only [EventGraphRuntime.State.WithinDeadline, entered, clock]
      decide
    have handled := handle_withhold_unremembered_eq (runtime setup) execution.application
      message.id resolution owner .bool initialBinding [] resolution_output resolution_code
      resolution_node ready timely sender (congrFun facts.remembered resolution)
    change handle (runtime setup) execution.application ⟨message.id, .withhold resolution⟩ =
      some (failureState execution ready) at handled
    by_cases tokened : message.payload.tokenValid = true
    · have physical : app.handle execution.application message =
          some (failureState execution ready) := by
        rw [(runtime setup).reactiveApplication_handle_of_tokenValid leaks _ _ tokened, call]
        exact handled
      right
      simp only [includeExecution, ReactiveApplication.Execution.includePending,
        MessageNetwork.includePending, looked, physical, Option.getD_some]
    · have rejected : app.handle execution.application message = none := by
        rw [(runtime setup).reactiveApplication_handle leaks]
        simp [tokened]
      left
      simp only [includeExecution, ReactiveApplication.Execution.includePending,
        MessageNetwork.includePending, looked, rejected, Option.getD_none]

theorem late_raw_response_failed (execution : app.Execution)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (position : execution.environmentRecall.length = 6)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (response : app.Action) (last : app.Execution)
    (supported : last ∈ (app.runRounds scheduler (fun _ => app.silentPolicy) 4
      (execution.respond app owner response)).support) :
    last.application.config.store (.inr resolution) = some .failure := by
  let submitted := execution.respond app owner response
  have unchanged := (runtime setup).reactive_respond_application leaks execution owner response
  have readyNow : submitted.application.config.cut.Ready resolution := by
    change (execution.respond app owner response).application.config.cut.Ready resolution
    rw [unchanged.1]
    exact ready
  have enteredNow : submitted.application.activatedAt resolution = some 0 := by
    have same := congrArg (fun view : PublicView nativeGraph => view.activatedAt resolution)
      unchanged.2
    exact same.trans entered
  have clockNow : submitted.application.clock = 1 :=
    (congrArg PublicView.clock unchanged.2).trans clock
  obtain ⟨submittedTrace⟩ := app.raw_trace_respond (initialLaw setup) horizon scheduler 4 execution
    owner response trace
  have postPosition : submitted.environmentRecall.length = 6 := position
  have first : app.round scheduler (fun _ => app.silentPolicy) submitted =
      submitted.environmentStep app (latestWithhold (submitted.observeEnvironment app)) := by
    simp only [ReactiveApplication.round, scheduler, postPosition, stageCommand, PMF.pure_bind,
      ReactiveApplication.dispatch, latestWithhold_actor_none]
    exact PMF.bind_pure _
  change last ∈ (app.runRounds scheduler (fun _ => app.silentPolicy) 4 submitted).support
    at supported
  rw [ReactiveApplication.runRounds, first, PMF.support_bind] at supported
  obtain ⟨next, moved, finished⟩ := Set.mem_iUnion₂.mp supported
  have nextPosition : next.environmentRecall.length = 7 := by
    rw [environmentStep_recall_append submitted next _ moved, List.length_append,
      List.length_singleton, postPosition]
  rw [ticks_before_expiry next nextPosition] at finished
  rcases late_selection_application submitted submittedTrace readyNow enteredNow clockNow next
      moved with unchanged | withheld
  · have readyNext : next.application.config.cut.Ready resolution := unchanged ▸ readyNow
    have enteredNext : next.application.activatedAt resolution = some 0 := unchanged ▸ enteredNow
    have clockNext : next.application.clock = 1 := unchanged ▸ clockNow
    rw [expiry_environment_ready (tickExecution (tickExecution next)) readyNext enteredNext (by
      change next.application.clock + 1 + 1 = 3
      rw [clockNext])] at finished
    cases (PMF.mem_support_pure_iff _ _).mp finished
    exact next.application.config.complete_output_same resolution readyNext false .failure
  · have completed : resolution ∈ next.application.config.cut.completed := by
      rw [withheld]
      change resolution ∈ (submitted.application.config.cut.complete resolution readyNow).completed
      simp only [EventOrder.Cut.completed_complete, Finset.mem_insert_self]
    rw [expiry_environment_completed (tickExecution (tickExecution next)) completed] at finished
    cases (PMF.mem_support_pure_iff _ _).mp finished
    change next.application.config.store (.inr resolution) = some .failure
    rw [withheld]
    exact submitted.application.config.complete_output_same resolution readyNow false .failure

theorem late_raw_response_value_le_zero (execution : app.Execution)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (position : execution.environmentRecall.length = 6)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (response : app.Action)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) :
    expect ((app.runRounds scheduler (fun _ => app.silentPolicy) 4
      (execution.respond app owner response)).map app.finished)
      (fun state => auditedUtility sample deposit state owner) ≤ 0 := by
  apply expect_le_const _ _ (auditedUtility_integrable _ sample deposit nonnegative owner) 0
  intro state supported
  obtain ⟨last, reached, rfl⟩ := PMF.support_map .. ▸ supported
  have failed := late_raw_response_failed execution trace position ready entered clock response last
    reached
  have zero := baseUtility_failure ⟨0, none, last⟩ failed
  change baseUtility setup leaks sourceUtility (app.finished last) owner = 0 at zero
  have charge := GameTheory.Enforcement.TerminalAudit.charge_mem_Icc
    ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
      (app.finished last) owner
  unfold auditedUtility GameTheory.Enforcement.TerminalAudit.utility
  rw [zero]
  exact sub_nonpos.mpr (mul_nonneg charge.1 nonnegative)

/-- Every whole native continuation at this actual information fiber has
audited value at most zero. The legal explicit-FALSE response attains zero. -/
theorem late_context_value_le_zero (bounds : MessageBounds nativeGraph) (witness : app.Execution)
    (trace : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, witness⟩))
    (ready : witness.application.config.cut.Ready resolution)
    (entered : witness.application.activatedAt resolution = some 0)
    (clock : witness.application.clock = 1) (empty : witness.network = .empty)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (assessment : (nativeModel bounds).BehavioralAssessment)
    (alternative : (nativeModel bounds).BehavioralPolicy owner) :
    (assessment.truncatedContinuationContext (lateSite bounds witness trace)
      (fun final => auditedUtility sample deposit final.state owner) 21).value alternative ≤ 0 := by
  rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    expect_bind_of_finite]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) 0
  intro history _
  obtain ⟨execution, current, position, actualClock, actualReady, actualEntered, actualEmpty⟩ :=
    late_information_resources bounds witness trace ready entered clock empty history
  rw [late_native_choice_value bounds _ history.1 execution current position sample deposit
    nonnegative]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) 0
  intro choice _
  exact late_raw_response_value_le_zero execution
    ((nativeMenu bounds).toRawTrace (initialLaw setup) horizon scheduler
      (current ▸ history.1.trace)) position actualReady actualEntered actualClock _ sample deposit
        nonnegative

theorem late_false_locally_optimal (bounds : MessageBounds nativeGraph) (witness : app.Execution)
    (trace : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, witness⟩))
    (ready : witness.application.config.cut.Ready resolution)
    (entered : witness.application.activatedAt resolution = some 0)
    (clock : witness.application.clock = 1) (empty : witness.network = .empty)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (assessment : (nativeModel bounds).BehavioralAssessment) (candidate : Handle nativeGraph)
    (chooses : (assessment.strategy owner (lateSite bounds witness trace).1).map Subtype.val =
      PMF.pure (some (lateResponse candidate false))) :
    (assessment.truncatedContinuationContext (lateSite bounds witness trace)
      (fun final => auditedUtility sample deposit final.state owner) 21).IsLocallyOptimal
        Set.univ (assessment.strategy owner) := by
  have value := late_context_false_value bounds witness trace ready entered clock empty sample
    deposit assessment candidate authentic (assessment.strategy owner) chooses
  refine (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
    (fun _ _ => payoffIntegrable_of_finite _ _)).mpr fun alternative _ => ?_
  rw [value]
  exact late_context_value_le_zero bounds witness trace ready entered clock empty sample deposit
    nonnegative assessment alternative

end Vegas.LateResolutionService
