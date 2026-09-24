/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationPrefix

/-! # Legal histories of the concrete native disclosure prefix -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def nativeSetupTrace (bit : Bool) :
    nativeArena.Trace (some ⟨56, none, nativeInitialExecution bit⟩) :=
  .extend .start (fun _ => none)
    ⟨by change ¬ False; simp, fun who => by change ¬ (none : Option Bool) = some who; simp⟩
    (by
      change (some ⟨56, none, nativeInitialExecution bit⟩ : nativeApp.ProtocolState) ∈
        (nativeInitialLaw.map _).support
      rw [FinDist.support_map]
      refine ⟨nativeStart bit, ?_, rfl⟩
      rw [nativeInitialLaw, FinDist.support_map]
      exact ⟨bit, FinDist.mem_support_uniformOfFintype bit, rfl⟩)

def nativeEnvironmentTrace (remaining : Nat) (execution next : nativeApp.Execution)
    (trace : nativeArena.Trace (some ⟨remaining + 1, none, execution⟩))
    (command : nativeApp.Command)
    (scheduled : nativeScheduler execution.environmentRecall
      (execution.observeEnvironment nativeApp) = FinDist.pure command)
    (law : execution.environmentStep nativeApp command = FinDist.pure next) :
    nativeArena.Trace (some ⟨remaining, command.actor? nativeApp, next⟩) :=
  .extend trace (fun _ => none)
    ⟨by change ¬ (remaining + 1 = 0 ∧ _); omega,
      fun who => by change ¬ (none : Option Bool) = some who; simp⟩
    (by
      change _ ∈ (nativeApp.transition nativeInitialLaw 56 nativeScheduler
        (some ⟨remaining + 1, none, execution⟩) (fun _ => none)).support
      simp only [ReactiveApplication.transition, scheduled, FinDist.pure_bind, law,
        FinDist.map_pure]
      exact FinDist.mem_support_pure.mpr rfl)

def nativeResponseTrace (remaining : Nat) (execution : nativeApp.Execution) (who : Bool)
    (trace : nativeArena.Trace (some ⟨remaining, some who, execution⟩))
    (action : nativeApp.Action)
    (available : action ∈ nativeMenu.actions who (execution.recall who)
      (execution.observe nativeApp who)) :
    nativeArena.Trace (some ⟨remaining, none, execution.respond nativeApp who action⟩) :=
  .extend trace (fun observer => if observer = who then some action else none)
    ⟨by change ¬ (remaining = 0 ∧ some who = none); simp,
      fun observer => by
        by_cases same : observer = who
        · subst observer
          simp only
          exact ⟨rfl, available⟩
        · simp only [ite_eq_right same]
          change ¬ some who = some observer
          simpa only [Option.some.injEq] using Ne.symm same⟩
    (by
      change _ ∈ (FinDist.pure (some (⟨remaining, none,
        execution.respond nativeApp who ((if who = who then some action else none).getD
          ⟨none⟩)⟩ : nativeApp.Control))).support
      simp)

theorem native_select_singleton (execution : nativeApp.Execution)
    (event : nativeGraph.EventId) (who : Bool)
    (message : Message Bool (WitnessedPacket nativeGraph))
    (pending : execution.network.pending = [message])
    (addressed : eventProposal event who message = true)
    (authorized : nativeApp.SubmissionPermitted dependencyCondition
      execution.environmentRecall message)
    (fresh : (execution.observeEnvironment nativeApp).Unpublished nativeApp message.id) :
    nativeApp.uniformInstruction dependencyCondition execution.environmentRecall
      (execution.observeEnvironment nativeApp) (.select (eventProposal event who)) =
        FinDist.pure (.include message.id) := by
  classical
  have absent : (execution.network.ledger.any fun prior => prior.id = message.id) = false := by
    apply Bool.eq_false_iff.mpr
    intro seen
    obtain ⟨prior, member, same⟩ := List.any_eq_true.mp seen
    exact fresh (List.mem_map.mpr ⟨prior, member, of_decide_eq_true same⟩)
  change (MessageNetwork.uniformPending _ execution.network.pending).map _ = _
  rw [pending, MessageNetwork.uniformPending_singleton]
  · exact FinDist.map_pure _ _
  · simp only [ReactiveApplication.authorizedEligibility, addressed, authorized, decide_true,
      ReactiveApplication.Execution.observeEnvironment, MessageNetwork.publicView, absent,
      Bool.not_false, Bool.and_self]

theorem native_packet_available (who : Bool) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) (packet : Payload nativeGraph)
    (bounded : nativeBounds.AllowsPacket packet) :
    (⟨some (.submit ⟨⟨packet, none⟩, .none⟩)⟩ : nativeApp.Action) ∈
      nativeMenu.actions who past view :=
      by
  rw [MessageBounds.menu_mem]
  refine ⟨⟨⟨bounded, trivial⟩, trivial⟩, ?_⟩
  change (⟨some (.submit
    ⟨(⟨packet, none⟩ : Submission nativeGraph).normalizeReactive who view.application,
      .none⟩)⟩ : nativeApp.Action) = _
  rw [Submission.normalizeReactive_none]

theorem native_opening_available (who : Bool) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) (event : nativeGraph.EventId) (candidate : Handle nativeGraph)
    (bit : Bool) (bounded : nativeBounds.AllowsHandle candidate) :
    (⟨some (.submit ⟨⟨.opening event candidate ⟨.bool, bit⟩, none⟩, .none⟩)⟩ : nativeApp.Action) ∈
      nativeMenu.actions who past view := by
  apply native_packet_available
  refine ⟨bounded, ?_⟩
  classical
  cases bit <;> simp [nativeBounds]

theorem native_withhold_available (who : Bool) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) (event : nativeGraph.EventId) :
    (⟨some (.submit ⟨⟨.withhold event, none⟩, .none⟩)⟩ : nativeApp.Action) ∈
      nativeMenu.actions who past view :=
  native_packet_available who past view _ trivial

theorem native_schedule (execution : nativeApp.Execution)
    (instruction : nativeApp.UniformInstruction)
    (atPosition : nativeCalendar execution.environmentRecall.length = instruction) :
    nativeScheduler execution.environmentRecall (execution.observeEnvironment nativeApp) =
      nativeApp.uniformInstruction dependencyCondition execution.environmentRecall
        (execution.observeEnvironment nativeApp) instruction := by
  change nativeApp.uniformInstruction _ _ _ (nativeCalendar _) = _
  rw [atPosition]

def nativeWindowTrace (remaining : Nat) (execution : nativeApp.Execution)
    (event : nativeGraph.EventId) (who : Bool) (submission : Submission nativeGraph)
    (trace : nativeArena.Trace (some ⟨remaining + 3, none, execution⟩))
    (grant : nativeCalendar execution.environmentRecall.length = .application (.grant event))
    (activate : nativeCalendar (execution.environmentRecall.length + 1) = .activate who)
    (select : nativeCalendar (execution.environmentRecall.length + 2) =
      .select (eventProposal event who))
    (empty : execution.network.pending = [])
    (address : submission.packet.event? nativeGraph = some event)
    (ready : execution.application.config.cut.Ready event)
    (available : (⟨some (.submit ⟨submission, .none⟩)⟩ : nativeApp.Action) ∈ nativeMenu.actions who
      ((nativeActivate (nativeGrant execution event) who).recall who)
      ((nativeActivate (nativeGrant execution event) who).observe nativeApp who)) :
    nativeArena.Trace (some ⟨remaining, none, nativeWindow execution event who submission⟩) := by
  let granted := nativeGrant execution event
  let activated := nativeActivate granted who
  let responded := activated.respond nativeApp who ⟨some (.submit ⟨submission, .none⟩)⟩
  have grantTrace : nativeArena.Trace (some ⟨remaining + 2, none, granted⟩) :=
    nativeEnvironmentTrace _ _ _ trace (.application (.grant event))
      (native_schedule execution _ grant) (native_grant_law execution event)
  have activePosition : nativeCalendar granted.environmentRecall.length = .activate who := by
    simpa only [granted, nativeGrant, nativeRecord, List.length_append,
      List.length_singleton] using activate
  have activeTrace : nativeArena.Trace (some ⟨remaining + 1, some who, activated⟩) :=
    nativeEnvironmentTrace _ _ _ grantTrace (.activate who)
      (native_schedule granted _ activePosition) (native_activate_law granted who)
  have responseTrace := nativeResponseTrace _ _ who activeTrace _ available
  have selectedPosition : nativeCalendar responded.environmentRecall.length =
      .select (eventProposal event who) := by
    simpa only [responded, nativeApp.respond_environmentRecall, activated, granted,
      nativeActivate, nativeGrant, nativeRecord, List.length_append, List.length_singleton,
      Nat.add_assoc] using select
  have pending : responded.network.pending =
      [⟨(who, execution.network.nextSerial who), ⟨submission.packet, none⟩⟩] := by
    change execution.network.pending ++ [_] = _
    rw [empty, List.nil_append]
    rfl
  have permitted : nativeApp.SubmissionPermitted dependencyCondition
      responded.environmentRecall
        ⟨(who, execution.network.nextSerial who), ⟨submission.packet, none⟩⟩ :=
      by
    rw [show responded.environmentRecall = activated.environmentRecall from rfl]
    apply (nativeApp.submissionPermitted_fresh_history ReactivePlayerView.publicView
      (fun _ _ => rfl) dependencyCondition nativeInitialLaw 56 nativeScheduler _
      (nativeMenu.toRawTrace nativeInitialLaw 56 nativeScheduler activeTrace) who rfl _).mpr
    intro target same predecessor member
    have identified : event = target := Option.some.inj (address.symm.trans same)
    subst target
    exact ((State.publicView_eventReady execution.application event).mpr ready).2 predecessor member
  have fresh : (responded.observeEnvironment nativeApp).Unpublished nativeApp
      (who, execution.network.nextSerial who) :=
    (nativeApp.serialsBeforeNext_history nativeScheduler nativeInitialLaw 56
      (nativeMenu.toRawTrace nativeInitialLaw 56 nativeScheduler trace)).next_unpublished who
  have selected := native_select_singleton responded event who _ pending
    (by simp only [eventProposal, Message.sender, address, and_self, decide_true]) permitted fresh
  exact nativeEnvironmentTrace _ _ _ responseTrace
    (.include (who, execution.network.nextSerial who))
    ((native_schedule responded _ selectedPosition).trans selected) (native_include_law _ _)

def nativeFirstTrace (bit : Bool) : nativeArena.Trace (some ⟨53, none, nativeFirst bit⟩) := by
  classical
  apply nativeWindowTrace 53 _ _ _ _ (nativeSetupTrace bit) rfl rfl rfl rfl rfl
    (native_registered_ready bit)
  rw [MessageBounds.menu_mem]
  refine ⟨⟨⟨by change 0 < 56; decide, ?_⟩, trivial⟩, ?_⟩
  · change (⟨.bool, false⟩ : Raw simpleExpr) ∈ nativeBounds.values
    simp [nativeBounds]
  change (⟨some (.submit ⟨dummySubmission.normalizeReactive false _, .none⟩)⟩ :
    nativeApp.Action) = _
  rw [Submission.normalizeReactive_effective]
  exact ⟨rfl, rfl⟩

theorem native_first_position (bit : Bool) : (nativeFirst bit).environmentRecall.length = 3 :=
  native_window_length _ _ _ _

def nativeSecondTrace (bit : Bool) : nativeArena.Trace (some ⟨50, none, nativeSecond bit⟩) := by
  apply nativeWindowTrace 50 _ _ _ _ (nativeFirstTrace bit)
    (by rw [native_first_position]; rfl) (by rw [native_first_position]; rfl)
    (by rw [native_first_position]; rfl) (native_first_pending bit) rfl
  · rw [native_first_application]
    exact native_bound_ready bit
  · exact native_opening_available _ _ _ _ _ false (by change 0 < 56; decide)

theorem native_second_position (bit : Bool) : (nativeSecond bit).environmentRecall.length = 6 := by
  rw [nativeSecond, native_window_length, native_first_position]

def nativeThirdTrace (bit : Bool) : nativeArena.Trace (some ⟨47, none, nativeThird bit⟩) := by
  apply nativeWindowTrace 47 _ _ _ _ (nativeSecondTrace bit)
    (by rw [native_second_position]; rfl) (by rw [native_second_position]; rfl)
    (by rw [native_second_position]; rfl) (native_second_pending bit) rfl
  · rw [native_second_application]
    exact native_dummy_ready bit
  · exact native_opening_available _ _ _ _ _ bit trivial

theorem native_third_position (bit : Bool) : (nativeThird bit).environmentRecall.length = 9 := by
  rw [nativeThird, native_window_length, native_second_position]

def nativeBobTrace (bit : Bool) :
    nativeArena.Trace (some ⟨45, some true, nativeBobExecution bit⟩) := by
  have granted : nativeArena.Trace (some ⟨46, none, nativeGrant (nativeThird bit) guessEvent⟩) :=
    nativeEnvironmentTrace _ _ _ (nativeThirdTrace bit) (.application (.grant guessEvent))
      (native_schedule (nativeThird bit) (.application (.grant guessEvent))
        (by rw [native_third_position]; rfl)) (native_grant_law _ _)
  exact nativeEnvironmentTrace 45 _ _ granted (.activate true)
    (native_schedule (nativeGrant (nativeThird bit) guessEvent) (.activate true) (by
      change nativeCalendar ((nativeThird bit).environmentRecall ++ [_]).length = _
      rw [List.length_append, List.length_singleton, native_third_position]
      rfl)) (native_activate_law _ _)

def nativeBobHistory (bit : Bool) : nativeArena.History := ⟨_, nativeBobTrace bit⟩

def nativeBobSite (bit : Bool) : nativeModel.InformationSite true :=
  nativeModel.informationSite true (nativeBobHistory bit)
    ⟨some (.submit ⟨⟨.withhold guessEvent, none⟩, .none⟩)⟩
    (by change ¬ (45 = 0 ∧ _); omega) (by
      change some _ ∈ (nativeMenu.information nativeInitialLaw 56 nativeScheduler).menu true
        ((nativeMenu.signals nativeInitialLaw 56 nativeScheduler).infoOf true
          (nativeBobHistory bit).trace)
      rw [ReactiveApplication.ResponseMenu.info]
      change ∃ action ∈ nativeMenu.actions true _ _, _ = some action
      exact ⟨_, native_withhold_available _ _ _ _, rfl⟩)

end VegasTests.SequentialValidation
