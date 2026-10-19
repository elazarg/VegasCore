/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalLostBindingClosingReplay

/-! # A whole genuine suffix for one original lost ordinary preparation

The original closing certificate supplies the actual primitive result before
restore. The same suffix is reconstructed before closure, across that command,
and through every later retry and phase. No target trace or rejection is
postulated beyond the genuine changed initial response prefix.
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

/-- Replay all actual later callbacks and service operations after replacing
one never-admitted binding value. The hypothesis about the drained result is
the original finished-attempt certificate, not the restored live table.
Every other player's complete raw responses remain literal. -/
theorem phase_lost_binding_replay
    (scheduler : (app).Scheduler) (ordered : graph.RevealRelaxedOrdered)
    (start : (app).Control)
    (startTrace : ((menu).protocol initial horizon scheduler).Trace (some start))
    (remaining : Nat) (before after : (app).Execution)
    (beforeTrace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, before⟩))
    (toClose : TracePrefix startTrace beforeTrace)
    (same : start.execution.application.attempt = before.application.attempt)
    (command : (app).Command)
    (selected : command ∈ (scheduler before.environmentRecall
      (before.observeEnvironment app)).support)
    (moved : after ∈ (before.environmentStep app command).support)
    (closingJoint : Player → Option (app).Action)
    (closingLegal : ((menu).protocol initial horizon scheduler).Legal
      (some ⟨remaining + 1, none, before⟩) closingJoint)
    (closingRealized : some (⟨remaining, command.actor? app, after⟩ : (app).Control) ∈
      (((menu).protocol initial horizon scheduler).step
        (some ⟨remaining + 1, none, before⟩) ⟨closingJoint, closingLegal⟩).support)
    (afterTrace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, command.actor? app, after⟩))
    (closingStep : afterTrace = beforeTrace.extend closingJoint closingLegal closingRealized)
    (finish : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some finish))
    (fromClose : TracePrefix afterTrace trace)
    (current : RecoveryState graph) (effect : PhaseClosingEffect runtime leaks before after current)
    (phase : RuntimePhase graph) (installed : before.application.phases.head? = some phase)
    (kind : phase.kind = .commitment)
    (finished : phase.Finished (phase.drain current))
    (coverage : (phase.drain current).FailureCoverage)
    (excludedEq : (phase.drain current).excluded = after.application.current.excluded)
    (owner : Player) (omitted : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout omitted = .binding owner payload)
    (inside : omitted ∈ phase.events)
    (unaccepted : (phase.drain current).native.accepted (.inr omitted) = none)
    (entry : (app).PlayerEntry) (recorded : entry ∈ start.execution.recall owner)
    (material : WitnessedSubmission graph)
    (transmitted : entry.action.transmission = some material)
    (serial : Nat) (named : material.call.packet = .commitment omitted (owner, .prepared serial))
    (sameEntry : entry.beforeView.application.2.attempt = start.execution.application.attempt)
    (saved : start.execution.application.entry.native.HandleUnused (owner, .prepared serial))
    (first second : Raw L) (image : (app).Execution)
    (imagePrefix : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨start.remaining, start.actor, image⟩))
    (paired : image.eraseRecall app owner =
      ((HiddenSwap.preparationOnly (owner, .prepared serial) first second).phaseExecution
        start.execution).eraseRecall app owner) :
    TracePrefix startTrace trace ∧ ∃ (target : (app).Execution)
      (imageTrace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨finish.remaining, finish.actor, target⟩)),
      TracePrefix imagePrefix imageTrace ∧
      target.eraseRecall app owner =
        ((HiddenSwap.preparationOnly (owner, .prepared serial) first second).phaseExecution
          finish.execution).eraseRecall app owner ∧
        imageTrace.transitionMass * startTrace.transitionMass =
          trace.transitionMass * imagePrefix.transitionMass ∧
      (∀ policy : ((menu).information initial horizon scheduler).BehavioralPolicy owner,
        ((menu).information initial horizon scheduler).ownPlayReachProbability policy
            (((menu).information initial horizon scheduler).ownPlay owner imageTrace) =
          ((menu).information initial horizon scheduler).ownPlayReachProbability policy
            (((menu).information initial horizon scheduler).ownPlay owner imagePrefix)) ∧
      ∀ policy : ((menu).information initial horizon scheduler).BehavioralPolicy owner,
        ((menu).information initial horizon scheduler).ownPlayReachProbability policy
            (((menu).information initial horizon scheduler).ownPlay owner trace) =
          ((menu).information initial horizon scheduler).ownPlayReachProbability policy
            (((menu).information initial horizon scheduler).ownPlay owner startTrace) := by
  classical
  have closingKept : TracePrefix beforeTrace afterTrace := by
    rw [closingStep]
    exact TracePrefix.extend (prefixTrace := beforeTrace) TracePrefix.refl closingJoint
      closingLegal closingRealized
  refine ⟨toClose.trans (closingKept.trans fromClose), ?_⟩
  obtain ⟨closingImage, closingImageTrace, imageClosingKept, closingPaired, closingMass,
      closingTail, closingSourceTail⟩ :=
    phase_lost_binding_replay_before_close runtime leaks bounds plan inputs horizon scheduler
      ordered start ⟨remaining + 1, none, before⟩ startTrace beforeTrace toClose same after current
        effect phase installed kind owner omitted payload binding inside unaccepted entry recorded
          material transmitted serial named sameEntry first second image imagePrefix paired
  have recalledPrefix := (app).reaches_recall_prefix initial horizon scheduler
    ((menu).reaches_raw initial horizon scheduler toClose.reachesWithin) start
      ⟨remaining + 1, none, before⟩ rfl rfl owner
  have remembered := recalledPrefix.subset recorded
  let raw := (menu).toRawTrace initial horizon scheduler beforeTrace
  obtain ⟨sent, emitted, _sender, sentCall⟩ := PhaseCount.recalled_submission_emitted runtime leaks
    initial horizon scheduler raw owner entry remembered material transmitted
  have inputRecall := (app).history_inputRecall initial horizon scheduler raw
  have sentInput : sent ∈ before.network.inputs := by
    have output : sent ∈ (app).outputs (before.recall owner) :=
      List.mem_filterMap.mpr ⟨entry, remembered, emitted⟩
    rw [← inputRecall owner] at output
    exact (List.mem_filter.mp output).1
  have sentNamed : sent.payload.packet.call =
      .commitment omitted (owner, .prepared serial) := sentCall.trans named
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) beforeTrace
  have unique := (app).uniqueIds_history scheduler initial horizon
    ⟨remaining + 1, none, before⟩ raw
  have singleEvent (message : Message Player (CommitAttemptPacket graph))
      (input : message ∈ before.network.inputs) (event : graph.EventId)
      (call : message.payload.packet.call = .commitment event (owner, .prepared serial)) :
      message.payload.packet.call = .commitment omitted (owner, .prepared serial) := by
    have identified := PhaseCount.commitment_eq_of_handle before.network.inputs sent message
      ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 sent sentInput))
      ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)) sentInput input
      (fun left leftInput right rightInput sameId =>
        (unique.inputs right rightInput).inputs left leftInput sameId) sentNamed call
    rw [← identified]
    exact sentNamed
  have absent := effect.unaccepted_before_of_drain runtime leaks phase (.inr omitted) unaccepted
  have activeBefore := PhaseCount.submitted_handle_unused_of_unaccepted runtime leaks bounds plan
    inputs horizon scheduler ⟨remaining + 1, none, before⟩ beforeTrace owner serial sent sentInput
      omitted sentNamed absent
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _drawn, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have startOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized ((menu).toRawTrace initial horizon scheduler startTrace)
  have entryEq := (phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
    scheduler start ⟨remaining + 1, none, before⟩ startTrace beforeTrace toClose
      startOrdered).2.2 same
  have savedBefore : before.application.entry.native.HandleUnused (owner, .prepared serial) := by
    rw [← entryEq]
    exact saved
  have origins := (app).history_provenance initial horizon scheduler raw
  have originalRejected : ∀ id message event, command = .include id →
      before.network.lookup id = some message →
      message.payload.packet.call = .commitment event (owner, .prepared serial) →
        before.application.handle runtime message = none := by
    intro id message event chosen found call
    subst command
    have input := ((app).retained_envelopes_mem_inputs before origins inputRecall).lookup
      id message found
    exact phase_lost_binding_closing_include_rejected runtime leaks before after current effect
      phase
      omitted (owner, .prepared serial) unaccepted id message found
        (singleEvent message input event call) moved
  obtain ⟨nextImage, nextMoved, nextPaired⟩ :=
    HiddenSwap.preparationOnly_environment_erased owner (.prepared serial) first second before
      closingImage closingPaired command after moved activeBefore originalRejected
  have service : closingImage.environmentRecall = before.environmentRecall := by
    have retained := congrArg (fun execution : (app).Execution => execution.environmentRecall)
      closingPaired
    exact retained
  have observed : closingImage.observeEnvironment app = before.observeEnvironment app :=
    (congrArg (fun execution : (app).Execution => execution.observeEnvironment app)
      closingPaired).trans
        (HiddenSwap.observeEnvironment_phaseExecution
          (HiddenSwap.preparationOnly (owner, .prepared serial) first second) before)
  have selectedImage : command ∈ (scheduler closingImage.environmentRecall
      (closingImage.observeEnvironment app)).support := by
    rw [service, observed]
    exact selected
  obtain ⟨nextImageTrace, nextKept, nextMass, nextWord⟩ :=
    HiddenSwap.phase_environment_trace_prefix bounds
    initial horizon scheduler remaining
    closingImage nextImage command closingImageTrace selectedImage nextMoved
  have intrinsic := HiddenSwap.preparationOnly_environment_atom owner (.prepared serial) first
    second before closingImage closingPaired command after nextImage moved nextMoved nextPaired
      activeBefore originalRejected
  have closingCross : nextImageTrace.transitionMass * beforeTrace.transitionMass =
      afterTrace.transitionMass * closingImageTrace.transitionMass := by
    rw [nextMass, service, observed, intrinsic, closingStep, Trace.transitionMass_extend]
    change (_ * _ : ℝ) * beforeTrace.transitionMass =
      (beforeTrace.transitionMass * ((app).transition initial horizon scheduler
        (some ⟨remaining + 1, none, before⟩) closingJoint
          (some ⟨remaining, command.actor? app, after⟩)).toReal) * _
    rw [(app).transition_environment_apply initial horizon scheduler remaining before after
      command moved]
    ring
  obtain ⟨savedAfter, activeAfter⟩ := phase_environment_unused_preparation runtime leaks
    before after
    command (owner, .prepared serial) savedBefore activeBefore originalRejected moved
  have excluded : owner ∈ after.application.current.excluded := by
    rw [← excludedEq]
    exact RecoveryState.excluded_of_finished_unaccepted_binding (phase.drain current) phase
      finished coverage omitted inside owner payload binding unaccepted
  obtain ⟨target, targetTrace, suffixKept, finalPaired, suffixMass,
      suffixTail, suffixSourceTail⟩ :=
    phase_lost_binding_replay_after_close
    runtime leaks bounds plan inputs horizon scheduler
    owner (.prepared serial) first second ⟨remaining, command.actor? app, after⟩ finish
      afterTrace trace
      fromClose excluded savedAfter activeAfter nextImage nextImageTrace nextPaired
  refine ⟨target, targetTrace,
    imageClosingKept.trans (nextKept.trans suffixKept), finalPaired, ?_, ?_, ?_⟩
  · apply (mul_right_cancel₀ (ne_of_gt afterTrace.transitionMass_pos))
    calc
      targetTrace.transitionMass * startTrace.transitionMass * afterTrace.transitionMass =
          trace.transitionMass * nextImageTrace.transitionMass * startTrace.transitionMass := by
        calc
          _ = (targetTrace.transitionMass * afterTrace.transitionMass) *
              startTrace.transitionMass := by ring
          _ = _ := by rw [suffixMass]
      _ = trace.transitionMass * imagePrefix.transitionMass * afterTrace.transitionMass := by
        apply (mul_right_cancel₀ (ne_of_gt beforeTrace.transitionMass_pos))
        calc
          _ = trace.transitionMass *
              (nextImageTrace.transitionMass * beforeTrace.transitionMass) *
                startTrace.transitionMass := by ring
          _ = trace.transitionMass * afterTrace.transitionMass *
              (closingImageTrace.transitionMass * startTrace.transitionMass) := by
            rw [closingCross]; ring
          _ = _ := by rw [closingMass]; ring
  · intro policy
    rw [suffixTail policy, nextWord owner]
    exact closingTail policy
  · intro policy
    rw [suffixSourceTail policy]
    have closingWord : ((menu).information initial horizon scheduler).ownPlay owner afterTrace =
        ((menu).information initial horizon scheduler).ownPlay owner beforeTrace := by
      rw [HiddenSwap.phase_trace_ownPlay bounds initial horizon scheduler _ afterTrace owner,
        HiddenSwap.phase_trace_ownPlay bounds initial horizon scheduler _ beforeTrace owner,
        ← (app).environmentStep_recall before after command moved]
    rw [closingWord]
    exact closingSourceTail policy


end Vegas.EventGraphRuntime
