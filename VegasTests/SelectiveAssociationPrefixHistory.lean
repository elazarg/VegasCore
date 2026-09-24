/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.ReactiveAssociationEvidence
import VegasTests.SelectiveAssociationOpeningSelection

/-! # The selective-association prefix is an actual raw native history

The prefix keeps Bob's earlier response unrestricted. Its explicit environment
laws produce a legal history of the existing native scheduler, ending at
Carol's activation before she chooses her guess.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability GameTheory.Protocol
open ReactiveAssociationEvidence


abbrev nativeRawArena := nativeApp.protocol (FinDist.pure nativeInitial)
  nativeHorizon nativeScheduler

private theorem trace_response (remaining : Nat) (execution : nativeApp.Execution)
    (who : Player) (response : nativeApp.Action)
    (prior : Nonempty (nativeRawArena.Trace (some ⟨remaining, some who, execution⟩))) :
    Nonempty (nativeRawArena.Trace
      (some ⟨remaining, none, execution.respond nativeApp who response⟩)) := by
  obtain ⟨trace⟩ := prior
  refine ⟨trace.extend (fun actor => if actor = who then some response else none) ?_ ?_⟩
  · constructor
    · simp [nativeRawArena, ReactiveApplication.protocol, ReactiveApplication.terminal]
    · intro actor
      by_cases same : actor = who
      · subst actor
        simp [IsLegalJoint, nativeRawArena, ReactiveApplication.protocol, ReactiveApplication.actor]
      · simp [IsLegalJoint, same, Ne.symm same, nativeRawArena,
          ReactiveApplication.protocol, ReactiveApplication.actor]
  · change _ ∈ (FinDist.pure _).support
    simp only [↓reduceIte, Option.getD_some, FinDist.mem_support_pure]

private theorem trace_environment (remaining : Nat) (execution next : nativeApp.Execution)
    (command : nativeApp.Command)
    (prior : Nonempty (nativeRawArena.Trace (some ⟨remaining + 1, none, execution⟩)))
    (selected : command ∈ (nativeScheduler execution.environmentRecall
      (execution.observeEnvironment nativeApp)).support)
    (moved : next ∈ (execution.environmentStep nativeApp command).support) :
    Nonempty (nativeRawArena.Trace (some ⟨remaining, command.actor? nativeApp, next⟩)) := by
  obtain ⟨trace⟩ := prior
  refine ⟨trace.extend (fun _ => none) ?_ ?_⟩
  · constructor
    · simp [nativeRawArena, ReactiveApplication.protocol, ReactiveApplication.terminal]
    · intro who
      simp [nativeRawArena, ReactiveApplication.protocol, ReactiveApplication.actor]
  · change _ ∈ ((nativeScheduler execution.environmentRecall
      (execution.observeEnvironment nativeApp)).bind _).support
    rw [FinDist.support_bind]
    apply Set.mem_iUnion₂.mpr
    refine ⟨command, selected, ?_⟩
    rw [FinDist.support_map]
    exact ⟨next, moved, rfl⟩

private theorem initial_trace :
    Nonempty (nativeRawArena.Trace (some ⟨89, none, initial⟩)) := by
  refine ⟨.extend .start (fun _ => none) ?_ ?_⟩
  · constructor
    · change ¬False
      trivial
    · intro who
      simp [nativeRawArena, ReactiveApplication.protocol, ReactiveApplication.actor]
  · change _ ∈ ((FinDist.pure nativeInitial).map _).support
    rw [FinDist.map_pure, FinDist.mem_support_pure]
    rfl

private theorem environment_cursor (execution next : nativeApp.Execution)
    (command : nativeApp.Command)
    (moved : next ∈ (execution.environmentStep nativeApp command).support) :
    next.environmentRecall.length = execution.environmentRecall.length + 1 := by
  obtain ⟨updated, _, rfl⟩ := FinDist.support_map .. ▸ moved
  simp only [List.length_append, List.length_singleton]

private theorem first_trace (bit : Bool) :
    Nonempty (nativeRawArena.Trace (some ⟨88, none, first bit⟩)) := by
  apply trace_response 88 activatedInitial alice _
  apply trace_environment 88 initial activatedInitial (.activate alice) initial_trace
  · change _ ∈ (FinDist.pure (.activate alice : nativeApp.Command)).support
    exact FinDist.mem_support_pure.mpr rfl
  · rw [initial_activation]
    exact FinDist.mem_support_pure.mpr rfl

private theorem reacted_trace (bit : Bool) (response : nativeApp.Action) :
    Nonempty (nativeRawArena.Trace (some ⟨87, none, reacted bit response⟩)) := by
  apply trace_response 87 (observed bit) bob response
  apply trace_environment 87 (first bit) (observed bit) (.activate bob)
    (first_trace bit)
  · change _ ∈ (FinDist.pure (.activate bob : nativeApp.Command)).support
    exact FinDist.mem_support_pure.mpr rfl
  · rw [activation_leaks_to_bob]
    exact FinDist.mem_support_pure.mpr rfl

private theorem reacted_cursor (bit : Bool) (response : nativeApp.Action) :
    (reacted bit response).environmentRecall.length = 2 := by
  rw [reacted, nativeApp.respond_environmentRecall]
  rfl

private theorem offered_trace (bit : Bool) (response : nativeApp.Action) :
    Nonempty (nativeRawArena.Trace (some ⟨85, none, offeredAfter bit response⟩)) := by
  apply trace_response 85 (beforeOffer (reacted bit response)) alice _
  have reached := FinDist.mem_support_pure.mpr
    (rfl : beforeOffer (reacted bit response) = _)
  rw [← beforeOffer_law] at reached
  obtain ⟨granted, grantMem, activateMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have grantedTrace := trace_environment 86 (reacted bit response) granted
    (.application (.grant aliceBinding)) (reacted_trace bit response) (by
      simp only [nativeScheduler, reacted_cursor]
      exact FinDist.mem_support_pure.mpr rfl) grantMem
  apply trace_environment 85 granted _ (.activate alice) grantedTrace _ activateMem
  have cursor := environment_cursor _ _ _ grantMem
  rw [reacted_cursor] at cursor
  simp only [nativeScheduler, cursor]
  exact FinDist.mem_support_pure.mpr rfl

theorem native_included_raw_trace (bit : Bool) (response : nativeApp.Action) :
    Nonempty (nativeRawArena.Trace (some ⟨84, none, includedAfter bit response⟩)) := by
  apply trace_environment 84 (offeredAfter bit response) _ (.include (alice, 1))
    (offered_trace bit response)
  · have cursor : (offeredAfter bit response).environmentRecall.length = 4 := by
      simp only [offeredAfter, nativeApp.respond_environmentRecall, beforeOffer,
        List.length_append, List.length_singleton, reacted_cursor]
    simp only [nativeScheduler, cursor]
    change .include (alice, 1) ∈ (FinDist.pure
      (nativeRuntime.reactiveLatest nativeLeaks aliceBinding alice
        ((offeredAfter bit response).observeEnvironment nativeApp))).support
    exact FinDist.mem_support_pure.mpr (later_envelope_selected bit response).symm
  · rw [inclusion_law]
    exact FinDist.mem_support_pure.mpr rfl

theorem native_carol_raw_trace (bit : Bool) (response : nativeApp.Action) :
    Nonempty (nativeRawArena.Trace (some ⟨80, some carol, carolSite bit response⟩)) := by
  have reached := FinDist.mem_support_pure.mpr (rfl : carolSite bit response = _)
  rw [← carolSite_law] at reached
  obtain ⟨ticked, tickMem, rest⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  obtain ⟨expired, expireMem, rest⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ rest)
  obtain ⟨granted, grantMem, activateMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ rest)
  have includedCursor : (includedAfter bit response).environmentRecall.length = 5 := by
    simp only [includedAfter, offeredAfter, nativeApp.respond_environmentRecall,
      beforeOffer, List.length_append, List.length_singleton, reacted_cursor]
  have tickTrace := trace_environment 83 (includedAfter bit response) ticked
    (.application .advanceClock) (native_included_raw_trace bit response) (by
      simp only [nativeScheduler, includedCursor]
      exact FinDist.mem_support_pure.mpr rfl) tickMem
  have tickCursor : ticked.environmentRecall.length = 6 := by
    rw [environment_cursor _ _ _ tickMem, includedCursor]
  have expireTrace := trace_environment 82 ticked expired (.application (.expire aliceBinding))
    tickTrace (by
      simp only [nativeScheduler, tickCursor]
      exact FinDist.mem_support_pure.mpr rfl)
      expireMem
  have expireCursor : expired.environmentRecall.length = 7 := by
    rw [environment_cursor _ _ _ expireMem, tickCursor]
  have grantTrace := trace_environment 81 expired granted (.application (.grant carolBinding))
    expireTrace (by
      simp only [nativeScheduler, expireCursor]
      exact FinDist.mem_support_pure.mpr rfl)
      grantMem
  have grantCursor : granted.environmentRecall.length = 8 := by
    rw [environment_cursor _ _ _ grantMem, expireCursor]
  exact trace_environment 80 granted _ (.activate carol) grantTrace
    (by
      simp only [nativeScheduler, grantCursor]
      exact FinDist.mem_support_pure.mpr rfl) activateMem

theorem native_transport_raw_history (control : nativeApp.Control)
    (raw : (nativeApp.protocol (FinDist.pure nativeInitial)
      nativeHorizon nativeScheduler).Trace (some control)) (who : Player)
    (active : control.actor = some who) :
    control.execution.Provenance nativeApp ∧ control.execution.InputRecall nativeApp ∧
      control.execution.network.PendingOrPublished ∧ control.execution.network.SerialsBeforeNext ∧
      control.execution.application.remembered = nativeInitial.remembered ∧
      ∀ response, (control.execution.respond nativeApp who response).SubmissionAudit nativeApp
        ReactivePlayerView.publicView := by
  have remembered := (nativeRuntime.reactiveRememberedInvariant nativeLeaks
    (fun table => table = nativeInitial.remembered)).history (FinDist.pure nativeInitial)
      nativeHorizon nativeScheduler (by
        intro state member
        cases FinDist.mem_support_pure.mp member
        rfl) raw
  have audit := nativeApp.submissionAudit_history ReactivePlayerView.publicView
    (fun _ _ => rfl) (FinDist.pure nativeInitial) nativeHorizon nativeScheduler raw
  refine ⟨nativeApp.history_provenance (FinDist.pure nativeInitial)
      nativeHorizon nativeScheduler raw,
    nativeApp.history_inputRecall (FinDist.pure nativeInitial) nativeHorizon nativeScheduler raw,
    nativeApp.pendingOrPublished_history nativeScheduler (FinDist.pure nativeInitial)
      nativeHorizon raw,
    nativeApp.serialsBeforeNext_history nativeScheduler (FinDist.pure nativeInitial)
      nativeHorizon raw, remembered, ?_⟩
  intro response
  exact nativeApp.submissionAudit_respond ReactivePlayerView.publicView (fun _ _ => rfl)
    control.execution who response audit.1
    (nativeApp.submissionOrigin_next_none_history (FinDist.pure nativeInitial) nativeHorizon
      nativeScheduler control raw who) (audit.2 who active)

end VegasTests.SelectiveAssociation
