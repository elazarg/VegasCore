/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalLostBindingSuffix
import Vegas.Pending.PhaseProposalLostBindingInclusion
import Vegas.Pending.PhaseAttemptCheckpoint
import Interaction.ReactiveTrafficIdentity

/-! # Actual lost-value replay up to the original closing primitive

Every source-side replay obligation is derived fromStart the one genuine closing
omission and the remembered original submitted packet. Counterfactual earlier
processing of that packet is not assumed to reject.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

omit [Fintype Player] in
private theorem initial_ordered : ∀ state ∈ (initial).support, state.Ordered := by
  intro state member
  obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ member
  exact PhaseRuntimeState.initial_ordered plan draw

/-- A retained intermediate namespace is the same when both endpoints agree.
This uses actual namespace progress and allows arbitrary inherited exclusions. -/
theorem phase_attempt_eq_between
    (scheduler : (app).Scheduler) (first middle last : (app).Control)
    (startTrace : ((menu).protocol initial horizon scheduler).Trace (some first))
    (prior : ((menu).protocol initial horizon scheduler).Trace (some middle))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some last))
    (fromStart : TracePrefix startTrace prior) (kept : TracePrefix prior trace)
    (same : first.execution.application.attempt = last.execution.application.attempt) :
    middle.execution.application.attempt = last.execution.application.attempt := by
  have firstOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    (initial_ordered plan inputs) ((menu).toRawTrace initial horizon scheduler startTrace)
  have middleOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    (initial_ordered plan inputs) ((menu).toRawTrace initial horizon scheduler prior)
  have lower := phase_attempt_progress_of_prefix runtime leaks menu initial
    (initial_ordered plan inputs) horizon scheduler first middle
      startTrace prior fromStart firstOrdered
  have upper := phase_attempt_progress_of_prefix runtime leaks menu initial
    (initial_ordered plan inputs) horizon scheduler middle last
      prior trace kept middleOrdered
  have generation := congrArg CommitAttemptId.generation same
  have phase := congrArg CommitAttemptId.phase same
  cases mid : middle.execution.application.attempt with
  | mk middlePhase middleGeneration =>
      cases final : last.execution.application.attempt with
      | mk lastPhase lastGeneration =>
          simp only [mid, final] at lower upper generation phase ⊢
          congr 1 <;> omega

/-- The entire original counted suffix before closure has an actual counted
counterpart with the lost candidate's private value changed. Original Nature,
all other players' raw aliases, and their full input histories remain literal. -/
theorem phase_lost_binding_replay_before_close
    (scheduler : (app).Scheduler) (ordered : graph.RevealRelaxedOrdered)
    (start closing : (app).Control)
    (startTrace : ((menu).protocol initial horizon scheduler).Trace (some start))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some closing))
    (retained : TracePrefix startTrace trace)
    (same : start.execution.application.attempt = closing.execution.application.attempt)
    (after : (app).Execution) (current : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks closing.execution after current)
    (phase : RuntimePhase graph)
    (installed : closing.execution.application.phases.head? = some phase)
    (kind : phase.kind = .commitment)
    (owner : Player) (omitted : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout omitted = .binding owner payload)
    (inside : omitted ∈ phase.events)
    (unaccepted : (phase.drain current).native.accepted (.inr omitted) = none)
    (entry : (app).PlayerEntry) (recorded : entry ∈ start.execution.recall owner)
    (material : WitnessedSubmission graph)
    (transmitted : entry.action.transmission = some material)
    (serial : Nat) (named : material.call.packet = .commitment omitted (owner, .prepared serial))
    (sameEntry : entry.beforeView.application.2.attempt = start.execution.application.attempt)
    (first second : Raw L) (image : (app).Execution)
    (imagePrefix : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨start.remaining, start.actor, image⟩))
    (paired : image.eraseRecall app owner =
      ((HiddenSwap.preparationOnly (owner, .prepared serial) first second).phaseExecution
        start.execution).eraseRecall app owner) :
    ∃ (target : (app).Execution)
      (imageTrace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨closing.remaining, closing.actor, target⟩)),
      TracePrefix imagePrefix imageTrace ∧
      target.eraseRecall app owner =
        ((HiddenSwap.preparationOnly (owner, .prepared serial) first second).phaseExecution
          closing.execution).eraseRecall app owner := by
  have remembered (control : (app).Control)
      (prior : ((menu).protocol initial horizon scheduler).Trace (some control))
      (fromStart : TracePrefix startTrace prior) : entry ∈ control.execution.recall owner := by
    exact ((app).reaches_recall_prefix initial horizon scheduler
      ((menu).reaches_raw initial horizon scheduler fromStart.reachesWithin)
        start control rfl rfl owner).subset recorded
  have original (control : (app).Control)
      (prior : ((menu).protocol initial horizon scheduler).Trace (some control))
      (fromStart : TracePrefix startTrace prior) : ∃ message ∈ control.execution.network.inputs,
        message.payload.packet.call = .commitment omitted (owner, .prepared serial) := by
    let raw := (menu).toRawTrace initial horizon scheduler prior
    obtain ⟨message, emitted, _sender, call⟩ := PhaseCount.recalled_submission_emitted runtime leaks
      initial horizon scheduler raw owner entry (remembered control prior fromStart) material
        transmitted
    have output : message ∈ (app).outputs (control.execution.recall owner) :=
      List.mem_filterMap.mpr ⟨entry, remembered control prior fromStart, emitted⟩
    rw [← (app).history_inputRecall initial horizon scheduler raw owner] at output
    exact ⟨message, (List.mem_filter.mp output).1, call.trans named⟩
  apply phase_lost_binding_suffix_replay runtime leaks bounds initial horizon scheduler owner
    (.prepared serial) first second start closing startTrace trace retained image imagePrefix paired
  · intro remaining execution prior fromStart kept
    have currentSame := phase_attempt_eq_between runtime leaks bounds plan inputs horizon scheduler
      start ⟨remaining, some owner, execution⟩ closing startTrace prior trace fromStart kept same
    exact phase_lost_binding_callback_silent runtime leaks bounds plan inputs horizon scheduler
      ordered remaining owner execution prior closing trace kept currentSame after current effect
        phase installed kind omitted payload binding inside unaccepted entry
          (remembered _ prior fromStart) material transmitted (owner, .prepared serial) named
            ((sameEntry.trans same).trans currentSame.symm)
  · intro control prior fromStart kept
    have currentSame := phase_attempt_eq_between runtime leaks bounds plan inputs horizon scheduler
      start control closing startTrace prior trace fromStart kept same
    have nativeOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler
      (initial_ordered plan inputs) ((menu).toRawTrace initial horizon scheduler prior)
    have absent := effect.unaccepted_before_of_drain runtime leaks phase (.inr omitted) unaccepted
    have missing : control.execution.application.current.native.accepted (.inr omitted) = none := by
      cases selected : control.execution.application.current.native.accepted (.inr omitted) with
      | none => rfl
      | some candidate =>
          have present := phase_prefix_accepted runtime leaks menu initial horizon scheduler control
            closing prior trace kept nativeOrdered currentSame (.inr omitted) candidate selected
          rw [absent] at present
          cases present
    obtain ⟨message, member, call⟩ := original control prior fromStart
    exact PhaseCount.submitted_handle_unused_of_unaccepted runtime leaks bounds plan inputs horizon
      scheduler control prior owner serial message member omitted call missing
  · intro remaining execution prior fromStart command next _selected moved nextTrace extended kept
      id message _event chosen found call
    subst command
    have nextEq : next = { execution.includePending app id with
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment app, .include id⟩] } := by
      have pureMoved : next ∈ (PMF.pure
          ({ execution.includePending app id with
            environmentRecall := execution.environmentRecall ++
              [⟨execution.observeEnvironment app, .include id⟩] } : (app).Execution)).support := by
        simpa only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] using moved
      exact (PMF.mem_support_pure_iff _ _).mp pureMoved
    subst next
    let control : (app).Control := ⟨remaining + 1, none, execution⟩
    let raw := (menu).toRawTrace initial horizon scheduler prior
    obtain ⟨sent, sentInput, sentCall⟩ := original control prior fromStart
    have recallValid := (app).history_inputRecall initial horizon scheduler raw
    have origins := (app).history_provenance initial horizon scheduler raw
    have input := ((app).retained_envelopes_mem_inputs execution origins recallValid).lookup
      id message found
    have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
      initial
      horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) prior
    have unique := (app).uniqueIds_history scheduler initial horizon control raw
    have identified := PhaseCount.commitment_eq_of_handle execution.network.inputs sent message
      ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 sent sentInput))
      ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)) sentInput input
      (fun left leftInput right rightInput sameId =>
        (unique.inputs right rightInput).inputs left leftInput sameId) sentCall call
    have omittedCall : message.payload.packet.call =
        .commitment omitted (owner, .prepared serial) := by rw [← identified]; exact sentCall
    have sameBefore := phase_attempt_eq_between runtime leaks bounds plan inputs horizon scheduler
      start control closing startTrace prior trace fromStart (extended.trans kept) same
    have sameIncluded := phase_attempt_eq_between runtime leaks bounds plan inputs horizon scheduler
      start _ closing startTrace nextTrace trace (fromStart.trans extended) kept same
    exact phase_lost_binding_include_rejected runtime leaks bounds plan inputs horizon scheduler
      remaining execution prior id message found omitted (owner, .prepared serial) omittedCall
        closing trace nextTrace kept sameBefore sameIncluded after current effect phase unaccepted

end Vegas.EventGraphRuntime
