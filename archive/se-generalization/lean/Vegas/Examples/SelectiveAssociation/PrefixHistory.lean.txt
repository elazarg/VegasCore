/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.ReactiveAssociationEvidence
import Vegas.Examples.SelectiveAssociation.OpeningSelection

/-! # The selective-association prefix is an actual raw native history

The prefix keeps Bob's earlier response unrestricted. Its explicit environment
laws produce a legal history of the existing native scheduler, ending at
Carol's activation before she chooses her guess.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability GameTheory.Protocol
open ReactiveAssociationEvidence


abbrev nativeRawArena := nativeApp.protocol (PMF.pure nativeInitial)
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
  · change _ ∈ (PMF.pure _).support
    simp only [↓reduceIte, Option.getD_some, PMF.mem_support_pure_iff _ _]

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
    rw [PMF.support_bind]
    apply Set.mem_iUnion₂.mpr
    refine ⟨command, selected, ?_⟩
    rw [PMF.support_map]
    exact ⟨next, moved, rfl⟩

private theorem initial_trace :
    Nonempty (nativeRawArena.Trace (some ⟨83, none, initial⟩)) := by
  refine ⟨.extend .start (fun _ => none) ?_ ?_⟩
  · constructor
    · change ¬False
      trivial
    · intro who
      simp [nativeRawArena, ReactiveApplication.protocol, ReactiveApplication.actor]
  · change _ ∈ ((PMF.pure nativeInitial).map _).support
    rw [PMF.pure_map, PMF.mem_support_pure_iff _ _]
    rfl

private theorem environment_cursor (execution next : nativeApp.Execution)
    (command : nativeApp.Command)
    (moved : next ∈ (execution.environmentStep nativeApp command).support) :
    next.environmentRecall.length = execution.environmentRecall.length + 1 := by
  obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ moved
  simp only [List.length_append, List.length_singleton]

private theorem first_trace (bit : Bool) :
    Nonempty (nativeRawArena.Trace (some ⟨82, none, first bit⟩)) := by
  apply trace_response 82 activatedInitial alice _
  apply trace_environment 82 initial activatedInitial (.activate alice) initial_trace
  · change _ ∈ (PMF.pure (.activate alice : nativeApp.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [initial_activation]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

private theorem reacted_trace (bit : Bool) (response : nativeApp.Action) :
    Nonempty (nativeRawArena.Trace (some ⟨81, none, reacted bit response⟩)) := by
  apply trace_response 81 (observed bit) bob response
  apply trace_environment 81 (first bit) (observed bit) (.activate bob)
    (first_trace bit)
  · change _ ∈ (PMF.pure (.activate bob : nativeApp.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [activation_leaks_to_bob]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

private theorem reacted_cursor (bit : Bool) (response : nativeApp.Action) :
    (reacted bit response).environmentRecall.length = 2 := by
  rw [reacted, nativeApp.respond_environmentRecall]
  rfl

private theorem offered_trace (bit : Bool) (response : nativeApp.Action) :
    Nonempty (nativeRawArena.Trace (some ⟨80, none, offeredAfter bit response⟩)) := by
  apply trace_response 80 (beforeOffer (reacted bit response)) alice _
  apply trace_environment 80 (reacted bit response) _ (.activate alice)
    (reacted_trace bit response)
  · simp only [serviceScheduler, reacted_cursor]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [beforeOffer_law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem native_included_raw_trace (bit : Bool) (response : nativeApp.Action) :
    Nonempty (nativeRawArena.Trace (some ⟨79, none, includedAfter bit response⟩)) := by
  apply trace_environment 79 (offeredAfter bit response) _ (.include (alice, 1))
    (offered_trace bit response)
  · have cursor : (offeredAfter bit response).environmentRecall.length = 3 := by
      simp only [offeredAfter, nativeApp.respond_environmentRecall, beforeOffer,
        List.length_append, List.length_singleton, reacted_cursor]
    simp only [serviceScheduler, cursor]
    change .include (alice, 1) ∈ (PMF.pure
      (nativeRuntime.reactiveLatest nativeLeaks aliceBinding alice
        ((offeredAfter bit response).observeEnvironment nativeApp))).support
    exact (PMF.mem_support_pure_iff _ _).mpr (later_envelope_selected bit response).symm
  · rw [inclusion_law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem native_carol_raw_trace (bit : Bool) (response : nativeApp.Action) :
    Nonempty (nativeRawArena.Trace (some ⟨76, some carol, carolSite bit response⟩)) := by
  have reached := (PMF.mem_support_pure_iff _ _).mpr (rfl : carolSite bit response = _)
  rw [← carolSite_law] at reached
  obtain ⟨ticked, tickMem, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨expired, expireMem, activateMem⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ rest)
  have includedCursor : (includedAfter bit response).environmentRecall.length = 4 := by
    simp only [includedAfter, offeredAfter, nativeApp.respond_environmentRecall,
      beforeOffer, List.length_append, List.length_singleton, reacted_cursor]
  have tickTrace := trace_environment 78 (includedAfter bit response) ticked
    (.application .advanceClock) (native_included_raw_trace bit response) (by
      simp only [serviceScheduler, includedCursor]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl) tickMem
  have tickCursor : ticked.environmentRecall.length = 5 := by
    rw [environment_cursor _ _ _ tickMem, includedCursor]
  have expireTrace := trace_environment 77 ticked expired (.application (.expire aliceBinding))
    tickTrace (by
      simp only [serviceScheduler, tickCursor]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
      expireMem
  have expireCursor : expired.environmentRecall.length = 6 := by
    rw [environment_cursor _ _ _ expireMem, tickCursor]
  exact trace_environment 76 expired _ (.activate carol) expireTrace
    (by
      simp only [serviceScheduler, expireCursor]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl) activateMem

theorem native_transport_raw_history (control : nativeApp.Control)
    (raw : (nativeApp.protocol (PMF.pure nativeInitial)
      nativeHorizon nativeScheduler).Trace (some control)) (who : Player)
    (active : control.actor = some who) :
    control.execution.Provenance nativeApp ∧ control.execution.InputRecall nativeApp ∧
      control.execution.network.PendingOrPublished ∧ control.execution.network.SerialsBeforeNext ∧
      control.execution.application.remembered = nativeInitial.remembered ∧
      ∀ response, (control.execution.respond nativeApp who response).SubmissionAudit nativeApp
        ReactivePlayerView.publicView := by
  have remembered := (nativeRuntime.reactiveRememberedInvariant nativeLeaks
    (fun table => table = nativeInitial.remembered)).history (PMF.pure nativeInitial)
      nativeHorizon nativeScheduler (by
        intro state member
        cases (PMF.mem_support_pure_iff _ _).mp member
        rfl) raw
  have audit := nativeApp.submissionAudit_history ReactivePlayerView.publicView
    (fun _ _ => rfl) (PMF.pure nativeInitial) nativeHorizon nativeScheduler raw
  refine ⟨nativeApp.history_provenance (PMF.pure nativeInitial)
      nativeHorizon nativeScheduler raw,
    nativeApp.history_inputRecall (PMF.pure nativeInitial) nativeHorizon nativeScheduler raw,
    nativeApp.pendingOrPublished_history nativeScheduler (PMF.pure nativeInitial)
      nativeHorizon raw,
    nativeApp.serialsBeforeNext_history nativeScheduler (PMF.pure nativeInitial)
      nativeHorizon raw, remembered, ?_⟩
  intro response
  exact nativeApp.submissionAudit_respond ReactivePlayerView.publicView (fun _ _ => rfl)
    control.execution who response audit.1
    (nativeApp.submissionOrigin_next_none_history (PMF.pure nativeInitial) nativeHorizon
      nativeScheduler control raw who) (audit.2 who active)

end Vegas.Examples.SelectiveAssociation
