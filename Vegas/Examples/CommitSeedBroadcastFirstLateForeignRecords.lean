/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastFirstLateRecord

/-! # Literal foreign response records at a first-late information fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Every owner's whole word consists of its literal initial response and
possibly its first-late response. Both full public before-views are identified,
without discarding earlier silent mistakes or changing hidden preparations. -/
theorem original_first_late_foreign_records (seed : Seeds) (remaining : Nat)
    (execution : app.Execution) (focal : Player)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some focal, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = [])
    (owner : Player) :
    ∃ first : app.PlayerEntry,
      first.beforeView.application.2 = initialState.publicView ∧
      PhaseRuntimeState.requests first.beforeView.application.2 owner
        (originalCoordinate owner) ∧ first.beforeView.application.2.native.clock = 0 ∧
      (execution.recall owner = [first] ∨ ∃ second : app.PlayerEntry,
        execution.recall owner = [first, second] ∧
        second.beforeView.application.2 = quietStart.application.publicView ∧
        PhaseRuntimeState.requests second.beforeView.application.2 owner
          (originalCoordinate owner) ∧ second.beforeView.application.2.native.clock = 2) := by
  classical
  obtain ⟨frame, final, owners, started, distinct, _absent, reached, words, _input⟩ :=
    original_first_late_callback_prefix seed remaining execution focal trace original clock empty
  rw [first_five_rounds] at started
  obtain ⟨firstAction, _first, afterFirst⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ started)
  obtain ⟨secondAction, _second, afterSecond⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterFirst)
  obtain ⟨thirdAction, _third, same⟩ := (PMF.mem_support_map_iff _ _ _).mp afterSecond
  have frameWord : frame.recall owner =
      (afterInitialResponses firstAction secondAction thirdAction).recall owner :=
    (congrArg (fun current : app.Execution => current.recall owner) same.symm).trans
      (show (initialClockTwo firstAction secondAction thirdAction).recall owner =
        (afterInitialResponses firstAction secondAction thirdAction).recall owner from rfl)
  have length : (frame.recall owner).length = 1 := by
    rw [frameWord]
    exact initial_record_length firstAction secondAction thirdAction owner
  obtain ⟨first, frameSingleton⟩ : ∃ first, frame.recall owner = [first] := by
    cases recalled : frame.recall owner with
    | nil => simp only [recalled, List.length_nil] at length; omega
    | cons first rest =>
        have restEmpty : rest = [] := List.length_eq_zero_iff.mp (by
          simp only [recalled, List.length_cons] at length
          omega)
        exact ⟨first, by rw [restEmpty]⟩
  have firstMember : first ∈
      (afterInitialResponses firstAction secondAction thirdAction).recall owner := by
    rw [← frameWord, frameSingleton]
    exact List.mem_singleton_self _
  have firstView := initial_record_public firstAction secondAction thirdAction owner first
    firstMember
  refine ⟨first, firstView, ?_, ?_, ?_⟩
  · rw [firstView]
    exact initial_bindings_ready owner
  · rw [firstView]
    exact initialState_clock
  · by_cases polled : owner ∈ owners
    · obtain ⟨second, recorded, secondView⟩ := physicalCallbacks_unique_record
        rawMenu.uniformResponses owners distinct owner polled frame final reached
      have framePublic : frame.application.publicView = quietStart.application.publicView := by
        rw [← same]
        exact initialClockTwo_publicView firstAction secondAction thirdAction
      have viewed := secondView.trans framePublic
      right
      refine ⟨second, ?_, viewed, ?_, ?_⟩
      · rw [← words owner, recorded, frameSingleton]
        rfl
      · rw [viewed]
        exact quietStart_public_requests owner
      · rw [viewed]
        exact quietStart_clock
    · left
      rw [← words owner, physicalCallbacks_no_own_response rawMenu.uniformResponses owners owner
        polled frame final reached]
      exact frameSingleton

end Vegas.Examples.CommitSeedBroadcast
