/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalCallbackPrefix
import Vegas.Pending.PhaseCountProjection
import Interaction.ReactiveRecallInvariant

/-! # The original first-late callback retains exactly its initial own response -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

private theorem response_public (execution : app.Execution) (owner : Player)
    (response : app.Action) :
    (execution.respond app owner response).application.publicView =
      execution.application.publicView := by
  rcases response with ⟨material⟩
  cases material with
  | none => rfl
  | some material => exact PhaseCount.submit_publicView execution.application owner material

theorem initial_record_public (first second third : app.Action) (owner : Player)
    (entry : app.PlayerEntry)
    (recorded : entry ∈ (afterInitialResponses first second third).recall owner) :
    entry.beforeView.application.2 = initialState.publicView := by
  have atAlice : initialAliceCallback.application.publicView = initialState.publicView := rfl
  have atBob : (initialBobCallback first).application.publicView = initialState.publicView :=
    response_public initialAliceCallback alice first
  have atCarol : (initialCarolCallback first second).application.publicView =
      initialState.publicView :=
    (response_public (initialBobCallback first) bob second).trans atBob
  rcases app.respond_entry_origin (initialCarolCallback first second) carol owner third entry
      recorded with before | fresh
  · change entry ∈ ((initialBobCallback first).respond app bob second).recall owner at before
    rcases app.respond_entry_origin (initialBobCallback first) bob owner second entry before with
      prior | fresh
    · change entry ∈ (initialAliceCallback.respond app alice first).recall owner at prior
      rcases app.respond_entry_origin initialAliceCallback alice owner first entry prior with
        absent | fresh
      · exact (List.not_mem_nil absent).elim
      · rw [fresh.2]
        exact atAlice
    · rw [fresh.2]
      exact atBob
  · rw [fresh.2]
    exact atCarol

theorem initial_record_length (first second third : app.Action) (owner : Player) :
    ((afterInitialResponses first second third).recall owner).length = 1 := by
  rw [afterInitialResponses, app.respond_recall_length]
  change (((initialBobCallback first).respond app bob second).recall owner).length +
    (if carol = owner then 1 else 0) = 1
  rw [app.respond_recall_length]
  change ((initialAliceCallback.respond app alice first).recall owner).length +
    (if bob = owner then 1 else 0) + (if carol = owner then 1 else 0) = 1
  rw [app.respond_recall_length]
  change 0 + (if alice = owner then 1 else 0) + (if bob = owner then 1 else 0) +
    (if carol = owner then 1 else 0) = 1
  fin_cases owner <;> rfl

private theorem singleton_of_length_one (entries : List app.PlayerEntry)
    (length : entries.length = 1) : ∃ entry, entries = [entry] := by
  cases entries with
  | nil => simp only [List.length_nil] at length; omega
  | cons entry rest =>
      cases rest with
      | nil => exact ⟨entry, rfl⟩
      | cons other rest => simp only [List.length_cons] at length; omega

/-- The complete original own record is retained, including a possible early
packet and its hidden preparation. No assumption of prescribed past play is used. -/
theorem original_first_late_initial_record (seed : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = []) :
    ∃ entry : app.PlayerEntry, execution.recall owner = [entry] ∧
      entry.beforeView.application.2 = initialState.publicView ∧
      PhaseRuntimeState.requests entry.beforeView.application.2 owner
        (originalCoordinate owner) ∧ entry.beforeView.application.2.native.clock = 0 := by
  obtain ⟨frame, final, owners, started, _distinct, absent, reached, sourceWords, _input⟩ :=
    original_first_late_callback_prefix seed remaining execution owner trace original clock empty
  have ownWord : execution.recall owner = frame.recall owner :=
    (sourceWords owner).symm.trans
      (physicalCallbacks_no_own_response rawMenu.uniformResponses owners owner absent frame final
        reached)
  rw [first_five_rounds] at started
  obtain ⟨first, _first, afterFirst⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ started)
  obtain ⟨second, _second, afterSecond⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterFirst)
  obtain ⟨third, _third, same⟩ := (PMF.mem_support_map_iff _ _ _).mp afterSecond
  have frameWord : frame.recall owner = (afterInitialResponses first second third).recall owner :=
    (congrArg (fun current : app.Execution => current.recall owner) same.symm).trans
      (show (initialClockTwo first second third).recall owner =
        (afterInitialResponses first second third).recall owner from rfl)
  have length : (execution.recall owner).length = 1 := by
    rw [ownWord, frameWord]
    exact initial_record_length first second third owner
  obtain ⟨entry, word⟩ := singleton_of_length_one (execution.recall owner) length
  have member : entry ∈ (afterInitialResponses first second third).recall owner := by
    rw [← frameWord, ← ownWord, word]
    exact List.mem_singleton_self _
  have publicView := initial_record_public first second third owner entry member
  refine ⟨entry, word, publicView, ?_, ?_⟩
  · rw [publicView]
    exact initial_bindings_ready owner
  · rw [publicView]
    exact initialState_clock

/-- Each owner has its initial response and at most one original clock-two
response before this decision. This includes arbitrary earlier packet contents. -/
theorem original_first_late_recall_length (seed : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = [])
    (who : Player) : (execution.recall who).length = 1 ∨ (execution.recall who).length = 2 := by
  classical
  obtain ⟨frame, final, owners, started, distinct, _absent, reached, words, _input⟩ :=
    original_first_late_callback_prefix seed remaining execution owner trace original clock empty
  rw [first_five_rounds] at started
  obtain ⟨first, _first, afterFirst⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ started)
  obtain ⟨second, _second, afterSecond⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterFirst)
  obtain ⟨third, _third, same⟩ := (PMF.mem_support_map_iff _ _ _).mp afterSecond
  have length : (frame.recall who).length = 1 := by
    rw [← same]
    exact initial_record_length first second third who
  by_cases member : who ∈ owners
  · obtain ⟨entry, recorded, _view⟩ := physicalCallbacks_unique_record rawMenu.uniformResponses
      owners distinct who member frame final reached
    right
    rw [← words who, recorded, List.length_append, List.length_singleton, length]
  · left
    rw [← words who, physicalCallbacks_no_own_response rawMenu.uniformResponses owners who
      member frame final reached]
    exact length

end Vegas.Examples.CommitSeedBroadcast
