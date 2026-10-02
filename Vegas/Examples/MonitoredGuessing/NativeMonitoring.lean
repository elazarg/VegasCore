/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeResponses
import Vegas.Examples.MonitoredGuessing.NativeLiability
import Vegas.Pending.ReactiveServiceEvaluation
import GameTheoryExtensions.Math.Probability.Support

/-! # Ordinary passive observation detects every ambient submission

Watcher samples actual pending packets and retains them privately. Its response
and the wire slot are silent. The resulting evidence mark is not a collection
decision; terminal settlement verifies the signed evidence against the record.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def reportCommand (_execution : nativeApp.Execution) : nativeApp.Command := .wait

def reported (execution : nativeApp.Execution) : nativeApp.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment nativeApp, .wait⟩] }

theorem report_command_law (execution : nativeApp.Execution) :
    nativeRuntime.interactionInstruction nativeLeaks nativeNetwork execution.environmentRecall
      (execution.observeEnvironment nativeApp) .wire = PMF.pure (reportCommand execution) := by
  simp only [interactionInstruction, nativeNetwork, PMF.pure_map]
  rfl

def monitoredPrefix (bit : Bool) (action : nativeApp.Action)
    (selected : Finset (MessageId Player)) : nativeApp.Execution :=
  let observed := watcherActivated bit action selected
  reported (observed.respond nativeApp watcher
    (nativeWatcherResponse (observed.observe nativeApp watcher)))

def monitoredPrefixLaw (bit : Bool) (action : nativeApp.Action) : PMF nativeApp.Execution :=
  (nativeLeaks watcher (ambientRespond bit action).network.pending).map
    (monitoredPrefix bit action)

def submissionAction (submission : WitnessedSubmission nativeGraph) : nativeApp.Action :=
  ⟨some submission⟩

theorem ambient_submission_pending (bit : Bool) (submission : WitnessedSubmission nativeGraph) :
    (ambientRespond bit (submissionAction submission)).network.pending =
      [⟨(alice, 0), nativeApp.packet
        (nativeApp.submit (nativeInitial bit) alice submission) alice [] submission⟩] := rfl

theorem ambient_submission_premature (bit : Bool) (submission : WitnessedSubmission nativeGraph) :
    let packet := nativeApp.packet (nativeApp.submit (nativeInitial bit) alice submission)
      alice [] submission
    prematureAlicePacket packet = true := by
  cases submission with
  | mk call evidence =>
      cases call with
      | mk packet opening =>
          cases packet with
          | opening event candidate raw | withhold event =>
              fin_cases event <;> cases evidence <;> cases bit <;> rfl
          | commitment event candidate | malformed raw => cases evidence <;> rfl

theorem sampled_submission_liability (bit : Bool)
    (submission : WitnessedSubmission nativeGraph) :
    aliceLiability (monitoredPrefix bit (submissionAction submission) {(alice, 0)}) = true := by
  change (false || ([(⟨(alice, 0), nativeApp.packet
    (nativeApp.submit (nativeInitial bit) alice submission) alice [] submission⟩ :
      Message Player (WitnessedPacket nativeGraph))].any
        fun message => message.sender == alice && prematureAlicePacket message.payload)) = true
  simp only [List.any_cons, List.any_nil, Message.sender, beq_self_eq_true, Bool.true_and,
    ambient_submission_premature, Bool.true_or, Bool.false_or]

theorem unsampled_submission_no_liability (bit : Bool)
    (submission : WitnessedSubmission nativeGraph) :
    aliceLiability (monitoredPrefix bit (submissionAction submission) ∅) = false := by
  simp only [monitoredPrefix, watcherActivated, MessageNetwork.learn_empty]
  rfl

theorem submission_monitoring_law (bit : Bool) (submission : WitnessedSubmission nativeGraph) :
    (monitoredPrefixLaw bit (submissionAction submission)).map
      (fun execution => aliceLiability execution) =
        mix (1 / 2) (by norm_num) (by norm_num)
          (PMF.pure true) (PMF.pure false) := by
  unfold monitoredPrefixLaw nativeLeaks
  simp only [↓reduceIte, mix_map, PMF.pure_map]
  have identifiers : pendingIds (ambientRespond bit (submissionAction submission)).network.pending =
      {(alice, 0)} := by
    rw [ambient_submission_pending]
    rfl
  rw [identifiers]
  simp [sampled_submission_liability, unsampled_submission_no_liability]

theorem submission_detection_probability (bit : Bool)
    (submission : WitnessedSubmission nativeGraph) :
    (((monitoredPrefixLaw bit (submissionAction submission)).map
      (fun execution => aliceLiability execution)) true).toReal = 1 / 2 := by
  rw [submission_monitoring_law]
  simp

theorem report_step (players : Player → nativeApp.Policy) (execution : nativeApp.Execution) :
    nativeRuntime.interactionStep nativeLeaks players nativeNetwork .wire execution =
      PMF.pure (reported execution) := by
  rw [interactionStep, report_command_law, PMF.pure_bind]
  simp only [reportCommand, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume, ReactiveApplication.Execution.environmentStep, PMF.pure_map,
    PMF.pure_bind]
  rfl

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
    PMF.pure_map, Function.comp_def]
  rw [← PMF.bind_pure_comp, Function.comp_def]
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
  rfl

theorem initial_response_cases (bit : Bool) (action : nativeApp.Action)
    (available : action ∈ nativeMenu.actions alice ((aliceActivated bit).recall alice)
      ((aliceActivated bit).observe nativeApp alice)) :
    action = nativeSilent ∨ ∃ submission, action = submissionAction submission := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact Or.inl rfl
  | some submission => exact Or.inr ⟨submission, rfl⟩

theorem silent_monitoring_law (bit : Bool) :
    monitoredPrefixLaw bit nativeSilent = PMF.pure (monitoredPrefix bit nativeSilent ∅) := by
  unfold monitoredPrefixLaw nativeLeaks
  simp only [↓reduceIte]
  change (mix (1 / 2) _ _ (PMF.pure ∅) (PMF.pure ∅)).map _ = _
  rw [mix_self, PMF.pure_map]

theorem silent_monitoring_no_liability (bit : Bool) :
    aliceLiability (monitoredPrefix bit nativeSilent ∅) = false := rfl

end Vegas.Examples.MonitoredGuessing
