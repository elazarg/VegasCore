/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalCallbackPrefix
import Vegas.Examples.CommitSeedBroadcastPrefixReconstruction

/-! # A genuine raw first-late history has a heavier all-good native repair -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem first_five_metadata (seed : Seeds) (players : Player → app.Policy)
    (frame : app.Execution)
    (reached : frame ∈ (app.runRounds (family seed) players 5 initialExecution).support) :
    frame.application.publicView = quietStart.application.publicView ∧
      frame.environmentRecall.length = 5 ∧ ∀ owner, (frame.recall owner).length = 1 := by
  rw [first_five_rounds] at reached
  obtain ⟨first, _first, afterFirst⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨second, _second, afterSecond⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterFirst)
  obtain ⟨third, _third, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp afterSecond
  refine ⟨initialClockTwo_publicView first second third,
    initialClockTwo_length first second third, ?_⟩
  intro owner
  change ((afterInitialResponses first second third).recall owner).length = 1
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

private theorem allGood_initialized_metadata (order : Equiv.Perm Player)
    (count : Nat) (bounded : count ≤ 3) (actual : app.Execution)
    (reached : actual ∈ (app.runRounds (family (allGoodSeed order)) rawMenu.uniformResponses
      (5 + count) initialExecution).support) :
    actual.application.publicView = quietStart.application.publicView ∧
      actual.environmentRecall.length = 5 + count := by
  rw [app.runRounds_add, PMF.support_bind] at reached
  obtain ⟨frame, started, later⟩ := Set.mem_iUnion₂.mp reached
  obtain ⟨publicView, position, _ownWords⟩ :=
    first_five_metadata (allGoodSeed order) rawMenu.uniformResponses frame started
  exact allGood_prefix_metadata order rawMenu.uniformResponses count bounded frame actual
    publicView position later

/-- The source and target are histories of the actual bounded RAW protocol.
The original seed atom and all native behavioral factors are compared together. -/
theorem original_first_late_native_repair (seed : Seeds) (players : Player → app.Policy)
    (remaining : Nat) (execution : app.Execution) (focal : Player)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some focal, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = []) :
    ∃ order : Equiv.Perm Player, ∃ count : Nat, ∃ _bound : count < 3, ∃ actual : app.Execution,
      ∃ _targetTrace : (rawMenu.protocol initial horizon (family (allGoodSeed order))).Trace
        (some ⟨horizon - (5 + count) - 1, some focal, completeActivation actual focal⟩),
      ((completeActivation actual focal).recall focal,
        (completeActivation actual focal).observe app focal) =
      (execution.recall focal, execution.observe app focal) ∧
      (∀ owner, (actual.recall owner).length = 1 ∨
        ((actual.recall owner).getLast?).map ReactiveApplication.PlayerEntry.action ≠
          some (⟨none⟩ : app.Action)) ∧
      (∀ owner, execution.recall owner = actual.recall owner ∨
        ∃ entry : app.PlayerEntry, entry.action = (⟨none⟩ : app.Action) ∧
          execution.recall owner = actual.recall owner ++ [entry]) ∧
      (nativeSeedLaw seed).toReal * nativeResponseLikelihood players execution ≤
        (nativeSeedLaw (allGoodSeed order)).toReal * nativeResponseLikelihood players
          (completeActivation actual focal) := by
  classical
  obtain ⟨frame, final, owners, started, distinct, absent, reached, sourceWords, sourceInput⟩ :=
    original_first_late_callback_prefix seed remaining execution focal trace original clock empty
  let kept := Finset.univ.filter (fun owner : Player => owner = focal ∨
    ((final.recall owner).getLast?).map ReactiveApplication.PlayerEntry.action ≠
      some (⟨none⟩ : app.Action))
  have focalKept : focal ∈ kept := by simp [kept]
  have silent (owner : Player) (_member : owner ∈ owners) (removed : owner ∉ kept) :
      ((final.recall owner).getLast?).map ReactiveApplication.PlayerEntry.action =
        some (⟨none⟩ : app.Action) := by
    by_contra different
    exact removed (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr different⟩)
  obtain ⟨order, count, bound, actual, _orderWord, actor, supported, input,
    agreement, untouched, words, weight, _occupied, _genuine⟩ :=
    silent_prefix_allGood_weight seed players rawMenu.uniformResponses frame final owners distinct
      focal absent kept focalKept started reached silent
  obtain ⟨_publicView, _position, frameWords⟩ :=
    first_five_metadata seed rawMenu.uniformResponses frame started
  have regular (owner : Player) : (actual.recall owner).length = 1 ∨
      ((actual.recall owner).getLast?).map ReactiveApplication.PlayerEntry.action ≠
        some (⟨none⟩ : app.Action) := by
    by_cases retained : owner ∈ kept
    · by_cases called : owner ∈ owners
      · right
        have different : owner ≠ focal := fun same => absent (same ▸ called)
        have nonSilent := (Finset.mem_filter.mp retained).2.resolve_left different
        rw [← agreement.ownWord owner retained]
        exact nonSilent
      · left
        rw [← agreement.ownWord owner retained,
          physicalCallbacks_no_own_response rawMenu.uniformResponses owners owner called
            frame final reached]
        exact frameWords owner
    · left
      rw [untouched owner retained]
      exact frameWords owner
  have actualMetadata := allGood_initialized_metadata order count (by omega) actual supported
  have rounds : actual ∈ (app.roundsFrom initial (family (allGoodSeed order))
      rawMenu.uniformResponses (5 + count)).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using supported
  obtain ⟨prior⟩ := rawMenu.trace_roundsFrom initial horizon (family (allGoodSeed order))
    rawMenu.uniformResponses (fun owner past view action chosen =>
      (rawMenu.uniformResponses_support owner past view action).mp chosen)
      (5 + count) (by change 5 + count ≤ 128; omega) actual rounds
  have selected := allGood_prefix_choice order ⟨count, bound⟩ actual actualMetadata.1
    actualMetadata.2
  rw [actor] at selected
  have enough : horizon - (5 + count) = horizon - (5 + count) - 1 + 1 := by
    change 128 - (5 + count) = 128 - (5 + count) - 1 + 1
    omega
  rw [enough] at prior
  obtain ⟨targetTrace⟩ := rawMenu.trace_environment initial horizon (family (allGoodSeed order))
    (horizon - (5 + count) - 1) actual (completeActivation actual focal) (.activate focal) prior
    (by rw [selected]; exact (PMF.mem_support_pure_iff ..).mpr rfl)
    (by rw [completeActivation_law]; exact (PMF.mem_support_pure_iff ..).mpr rfl)
  have likelihood : nativeResponseLikelihood players final =
      nativeResponseLikelihood players execution := by
    unfold nativeResponseLikelihood
    apply Finset.prod_congr rfl
    intro owner _member
    rw [sourceWords owner]
  have activated : nativeResponseLikelihood players (completeActivation actual focal) =
      nativeResponseLikelihood players actual := by
    simp only [nativeResponseLikelihood, completeActivation,
      ReactiveApplication.Execution.sampledActivation]
  refine ⟨order, count, bound, actual, targetTrace, input.trans sourceInput, regular, ?_, ?_⟩
  · intro owner
    simpa only [sourceWords owner] using words owner
  · simpa only [likelihood, activated] using weight

end Vegas.Examples.CommitSeedBroadcast
