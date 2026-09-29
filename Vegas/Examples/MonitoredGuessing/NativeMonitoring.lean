/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeResponses
import Vegas.Pending.ReactiveServiceEvaluation

/-! # Ordinary passive observation detects every ambient submission

The selected packet is replayed by a player using only their leaked view. The
fixed wire step checks the resulting public rebroadcast, and the actual handler
rejects the premature call. No privately sampled identifier is supplied to the
scheduler. The debit is determined by the resulting persistent public receipt.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def reportCommand (execution : nativeApp.Execution) : nativeApp.Command :=
  nativeApp.atMostOnceCommand (execution.observeEnvironment nativeApp) <|
    match execution.network.inputs.getLast? with
    | none => .wait
    | some input =>
        if input.broadcaster = watcher ∧ input.envelope.sender = alice then
          .include input.envelope.id
        else .wait

def reported (execution : nativeApp.Execution) : nativeApp.Execution :=
  let command := reportCommand execution
  let next := match command with
    | .include id => execution.includePending nativeApp id
    | _ => execution
  { next with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment nativeApp, command⟩] }

theorem report_command_law (execution : nativeApp.Execution) :
    nativeRuntime.interactionInstruction nativeLeaks nativeNetwork execution.environmentRecall
      (execution.observeEnvironment nativeApp) .wire = PMF.pure (reportCommand execution) := by
  simp only [EventGraphRuntime.interactionInstruction, nativeNetwork, PMF.pure_map]
  unfold reportCommand
  change PMF.pure (nativeApp.atMostOnceCommand _
    (NetworkChoice.command _ _ (match execution.network.inputs.getLast? with
      | none => .wait
      | some input => if input.broadcaster = watcher ∧ input.envelope.sender = alice then
          .include input.envelope.id else .wait))) = _
  cases execution.network.inputs.getLast? with
  | none => rfl
  | some input => dsimp only; split_ifs <;> rfl

def monitoredPrefix (bit : Bool) (action : nativeApp.Action)
    (selected : Finset (MessageId Player)) : nativeApp.Execution :=
  let observed := watcherActivated bit action selected
  reported (observed.respond nativeApp watcher
    (nativeWatcherResponse (observed.observe nativeApp watcher)))

def monitoredPrefixLaw (bit : Bool) (action : nativeApp.Action) : PMF nativeApp.Execution :=
  (nativeLeaks watcher (ambientRespond bit action).network.pending).map
    (monitoredPrefix bit action)

def submissionAction (submission : WitnessedSubmission nativeGraph) : nativeApp.Action :=
  ⟨some (.submit submission)⟩

theorem ambient_submission_pending (bit : Bool) (submission : WitnessedSubmission nativeGraph) :
    (ambientRespond bit (submissionAction submission)).network.pending =
      [⟨(alice, 0), nativeApp.packet
        (nativeApp.submit (nativeInitial bit) alice submission) alice [] submission⟩] := rfl

theorem sampled_submission_report (bit : Bool) (submission : WitnessedSubmission nativeGraph) :
    (monitoredPrefix bit (submissionAction submission) {(alice, 0)}).receipts =
      [((alice, 0), false)] := by
  let before := watcherRespond bit (submissionAction submission) {(alice, 0)}
    ⟨some (.replay (alice, 0))⟩
  have received : nativeWatcherResponse
      ((watcherActivated bit (submissionAction submission) {(alice, 0)}).observe
        nativeApp watcher) = ⟨some (.replay (alice, 0))⟩ := rfl
  have command : reportCommand before = .include (alice, 0) := by
    rfl
  unfold monitoredPrefix
  dsimp only
  rw [received]
  change (reported before).receipts = _
  unfold reported
  rw [command]
  change (before.includePending nativeApp (alice, 0)).receipts = _
  let message : Message Player (WitnessedPacket nativeGraph) :=
    ⟨(alice, 0), nativeApp.packet
      (nativeApp.submit (nativeInitial bit) alice submission) alice [] submission⟩
  have found : before.network.lookup (alice, 0) = some message := rfl
  have rejected : nativeApp.handle before.application message = none :=
    prelude_rejects bit before.application
      (watcher_config bit (submissionAction submission) {(alice, 0)} _)
      ⟨message.id, message.payload.call⟩ (by change alice ≠ bob; decide)
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [found]
  change before.receipts ++ [((alice, 0), (nativeApp.handle before.application message).isSome)] = _
  rw [rejected]
  rfl

theorem unsampled_submission_no_report (bit : Bool)
    (submission : WitnessedSubmission nativeGraph) :
    (monitoredPrefix bit (submissionAction submission) ∅).receipts = [] := by
  simp only [monitoredPrefix, watcherActivated, MessageNetwork.learn_empty]
  rfl

theorem submission_monitoring_law (bit : Bool) (submission : WitnessedSubmission nativeGraph) :
    (monitoredPrefixLaw bit (submissionAction submission)).map
      (fun execution => rejectedAlice execution.receipts) =
        mix (1 / 2) (by norm_num) (by norm_num)
          (PMF.pure true) (PMF.pure false) := by
  unfold monitoredPrefixLaw nativeLeaks
  simp only [↓reduceIte, mix_map, PMF.pure_map]
  have identifiers : pendingIds (ambientRespond bit (submissionAction submission)).network.pending =
      {(alice, 0)} := by
    rw [ambient_submission_pending]
    rfl
  rw [identifiers]
  simp [sampled_submission_report, unsampled_submission_no_report, rejectedAlice]

theorem submission_detection_probability (bit : Bool)
    (submission : WitnessedSubmission nativeGraph) :
    (((monitoredPrefixLaw bit (submissionAction submission)).map
      (fun execution => rejectedAlice execution.receipts)) true).toReal = 1 / 2 := by
  rw [submission_monitoring_law]
  simp [mix_apply_toReal, toReal_pure_apply]

theorem report_step (players : Player → nativeApp.Policy) (execution : nativeApp.Execution) :
    nativeRuntime.interactionStep nativeLeaks players nativeNetwork .wire execution =
      PMF.pure (reported execution) := by
  rw [interactionStep, report_command_law, PMF.pure_bind]
  unfold reported reportCommand
  cases found : execution.network.inputs.getLast? with
  | none =>
      simp only [ReactiveApplication.atMostOnceCommand, ReactiveApplication.dispatch,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
  | some input =>
      dsimp only
      split
      · simp only [ReactiveApplication.atMostOnceCommand]
        split <;>
          simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
            ReactiveApplication.resume, ReactiveApplication.Execution.environmentStep,
            PMF.pure_map, PMF.pure_bind]
      · simp only [ReactiveApplication.atMostOnceCommand, ReactiveApplication.dispatch,
          ReactiveApplication.Command.actor?, ReactiveApplication.resume,
          ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]

theorem watcher_step (players : Player → nativeApp.Policy)
    (reports : players watcher = nativeWatcherPolicy) (bit : Bool) (action : nativeApp.Action) :
    nativeRuntime.interactionStep nativeLeaks players nativeNetwork (.player watcher)
      (ambientRespond bit action) =
      (nativeLeaks watcher (ambientRespond bit action).network.pending).map (fun selected =>
        let observed := watcherActivated bit action selected
        observed.respond nativeApp watcher
          (nativeWatcherResponse (observed.observe nativeApp watcher))) := by
  simp only [interactionStep, interactionInstruction, PMF.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
    ReactiveApplication.Execution.environmentStep, PMF.bind_map,
    ReactiveApplication.resume, ReactiveApplication.invoke, reports, nativeWatcherPolicy,
    PMF.pure_map]
  rw [← ← PMF.bind_pure_comp, Function.comp_def]
  rfl

/-- This is the actual player-activation and wire suffix, with every later
player policy left arbitrary. -/
theorem monitoring_plan (players : Player → nativeApp.Policy)
    (reports : players watcher = nativeWatcherPolicy) (bit : Bool) (action : nativeApp.Action) :
    nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork [.player watcher, .wire]
      (ambientRespond bit action) = monitoredPrefixLaw bit action := by
  simp only [runInteractionPlan, PMF.bind_pure]
  rw [watcher_step players reports, PMF.bind_map]
  simp only [report_step]
  rw [← ← PMF.bind_pure_comp, Function.comp_def]
  rfl

theorem initial_response_cases (bit : Bool) (action : nativeApp.Action)
    (available : action ∈ nativeMenu.actions alice ((aliceActivated bit).recall alice)
      ((aliceActivated bit).observe nativeApp alice)) :
    action = nativeSilent ∨ ∃ submission, action = submissionAction submission := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact Or.inl rfl
  | some transmission =>
      cases transmission with
      | submit submission => exact Or.inr ⟨submission, rfl⟩
      | replay id =>
          change (⟨some (.replay id)⟩ : nativeApp.Action) ∈
            (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions alice _ _ at available
          rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
            at available
          obtain ⟨message, member, _⟩ := available
          change message ∈ ([] : List (Message Player (WitnessedPacket nativeGraph))) at member
          cases member

theorem silent_monitoring_law (bit : Bool) :
    monitoredPrefixLaw bit nativeSilent = PMF.pure (monitoredPrefix bit nativeSilent ∅) := by
  unfold monitoredPrefixLaw nativeLeaks
  simp only [↓reduceIte]
  change (mix (1 / 2) _ _ (PMF.pure ∅) (PMF.pure ∅)).map _ = _
  rw [mix_self, PMF.pure_map]

theorem silent_monitoring_no_report (bit : Bool) :
    (monitoredPrefix bit nativeSilent ∅).receipts = [] := rfl

end Vegas.Examples.MonitoredGuessing
