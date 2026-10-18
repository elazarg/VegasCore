/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastAllGoodPrefix
import Mathlib.Data.List.Perm.Subperm

/-! # An all-good native target for a retained first-late callback prefix -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def targetCallbackWord (retained : List Player) (focal : Player) : List Player :=
  retained ++ [focal] ++ ([0, 1, 2] : List Player).filter
    (fun owner => decide (owner ∉ retained ∧ owner ≠ focal))

theorem targetCallbackWord_nodup (retained : List Player) (focal : Player)
    (distinct : retained.Nodup) (absent : focal ∉ retained) :
    (targetCallbackWord retained focal).Nodup := by
  have first : (retained ++ [focal]).Nodup :=
    distinct.append (by simp) (List.disjoint_left.mpr fun owner member singleton =>
      absent ((List.mem_singleton.mp singleton) ▸ member))
  apply first.append ((by decide : ([0, 1, 2] : List Player).Nodup).filter _)
  apply List.disjoint_left.mpr
  intro owner before after
  have excluded := of_decide_eq_true (List.mem_filter.mp after).2
  rcases List.mem_append.mp before with member | same
  · exact excluded.1 member
  · exact excluded.2 (List.mem_singleton.mp same)

theorem targetCallbackWord_mem (retained : List Player) (focal owner : Player) :
    owner ∈ targetCallbackWord retained focal := by
  by_cases before : owner ∈ retained
  · exact List.mem_append_left _ (List.mem_append_left _ before)
  · by_cases same : owner = focal
    · subst owner
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    · apply List.mem_append_right
      apply List.mem_filter.mpr
      refine ⟨?_, decide_eq_true ⟨before, same⟩⟩
      fin_cases owner <;> decide

theorem targetCallbackWord_length (retained : List Player) (focal : Player)
    (distinct : retained.Nodup) (absent : focal ∉ retained) :
    (targetCallbackWord retained focal).length = 3 := by
  have complete : (targetCallbackWord retained focal).toFinset = Finset.univ := by
    ext owner
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact targetCallbackWord_mem retained focal owner
  have cardinality := congrArg Finset.card complete
  rw [List.toFinset_card_of_nodup (targetCallbackWord_nodup retained focal distinct absent)]
    at cardinality
  exact cardinality

def targetCallbackPermutation (retained : List Player) (focal : Player)
    (distinct : retained.Nodup) (absent : focal ∉ retained) : Equiv.Perm Player :=
  (finCongr (targetCallbackWord_length retained focal distinct absent)).symm.trans
    (List.Nodup.getEquivOfForallMemList _
      (targetCallbackWord_nodup retained focal distinct absent)
      (targetCallbackWord_mem retained focal))

theorem targetCallbackPermutation_word (retained : List Player) (focal : Player)
    (distinct : retained.Nodup) (absent : focal ∉ retained) :
    List.ofFn (targetCallbackPermutation retained focal distinct absent) =
      targetCallbackWord retained focal := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, targetCallbackWord_length retained focal distinct absent]
  · intro index leftBound rightBound
    rw [List.getElem_ofFn]
    rfl

theorem targetCallbackPermutation_prefix (retained : List Player) (focal : Player)
    (distinct : retained.Nodup) (absent : focal ∉ retained) :
    (List.ofFn (targetCallbackPermutation retained focal distinct absent)).take retained.length =
      retained := by
  rw [targetCallbackPermutation_word]
  simp only [targetCallbackWord, List.append_assoc, List.take_left]

theorem targetCallbackPermutation_focal (retained : List Player) (focal : Player)
    (distinct : retained.Nodup) (absent : focal ∉ retained) :
    ∃ bound : retained.length < 3,
      targetCallbackPermutation retained focal distinct absent
        ⟨retained.length, bound⟩ = focal := by
  have length := targetCallbackWord_length retained focal distinct absent
  simp only [targetCallbackWord, List.length_append, List.length_singleton] at length
  have bound : retained.length < 3 := by omega
  refine ⟨bound, ?_⟩
  have position := congrArg (fun word : List Player => word[retained.length]?)
    (targetCallbackPermutation_word retained focal distinct absent)
  have located : (targetCallbackWord retained focal)[retained.length]? = some focal := by
    simp only [targetCallbackWord, List.append_assoc,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  rw [located] at position
  simpa only [List.getElem?_ofFn, dite_eq_left bound, Option.some.injEq] using position

/-- The repaired prefix is an actual original native execution under an
all-good draw. Its source remains the same initialized raw response experiment. -/
theorem silent_prefix_allGood_native_target (oldSeed : Seeds) (players : Player → app.Policy)
    (frame final : app.Execution) (owners : List Player) (distinct : owners.Nodup)
    (focal : Player) (absent : focal ∉ owners) (kept : Finset Player) (focalKept : focal ∈ kept)
    (started : frame ∈ (app.runRounds (family oldSeed) players 5 initialExecution).support)
    (reached : final ∈ (physicalCallbacks players owners frame).support)
    (silent : ∀ actor ∈ owners, actor ∉ kept →
      ((final.recall actor).getLast?).map ReactiveApplication.PlayerEntry.action =
        some (⟨none⟩ : app.Action)) :
    ∃ order : Equiv.Perm Player, ∃ count : Nat, ∃ bound : count < 3, ∃ actual : app.Execution,
      (List.ofFn order).take count = owners.filter (fun owner => owner ∈ kept) ∧
      order ⟨count, bound⟩ = focal ∧
      actual ∈ (app.runRounds (family (allGoodSeed order)) players (5 + count)
        initialExecution).support ∧
      ((completeActivation actual focal).recall focal,
        (completeActivation actual focal).observe app focal) =
      ((completeActivation final focal).recall focal,
        (completeActivation final focal).observe app focal) ∧
      CallbackAgreement kept final actual ∧
      (∀ owner, owner ∉ kept → actual.recall owner = frame.recall owner) ∧
      some ⟨horizon - (5 + count) - 1, some focal, completeActivation actual focal⟩ ∈
        (app.commandControlLaw (family (allGoodSeed order)) players initial
          (horizon - (5 + count) - 1) (5 + count)).support ∧
      Nonempty ((app.protocol initial horizon (family (allGoodSeed order))).Trace
        (some ⟨horizon - (5 + count) - 1, some focal, completeActivation actual focal⟩)) := by
  have frameFacts : frame.application.publicView = quietStart.application.publicView ∧
      frame.environmentRecall.length = 5 := by
    have initialSupported := started
    rw [first_five_rounds] at initialSupported
    obtain ⟨first, _first, afterFirst⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ initialSupported)
    obtain ⟨second, _second, afterSecond⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterFirst)
    obtain ⟨third, _third, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp afterSecond
    exact ⟨initialClockTwo_publicView first second third,
      initialClockTwo_length first second third⟩
  obtain ⟨publicView, position⟩ := frameFacts
  let retained := owners.filter (fun owner => owner ∈ kept)
  have retainedDistinct : retained.Nodup := distinct.filter _
  have focalAbsent : focal ∉ retained := fun member => absent (List.mem_filter.mp member).1
  let order := targetCallbackPermutation retained focal retainedDistinct focalAbsent
  obtain ⟨bound, focalAt⟩ :=
    targetCallbackPermutation_focal retained focal retainedDistinct focalAbsent
  have ordered : (List.ofFn order).take retained.length = retained :=
    targetCallbackPermutation_prefix retained focal retainedDistinct focalAbsent
  obtain ⟨next, supported, same⟩ := physicalCallbacks_remove_silent players kept owners distinct
    frame frame final (CallbackAgreement.refl kept frame) reached silent
  change next ∈ (physicalCallbacks players retained frame).support at supported
  have filteredSupport := supported
  rw [← ordered] at supported
  obtain ⟨actual, physical, actualReached, occupied, genuine⟩ :=
    allGood_focal_decision oldSeed order players frame next retained.length bound started
      publicView position supported
  have actualNext : CallbackAgreement kept actual (physicalExecution actual) :=
    ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  rw [physical] at actualNext
  have nextActual : CallbackAgreement kept next actual :=
    ⟨actualNext.application.symm, actualNext.network.symm, actualNext.receipts.symm,
      fun owner member => (actualNext.leaked owner member).symm,
      fun owner member => (actualNext.ownWord owner member).symm⟩
  have agreement := same.trans nextActual
  have untouched (owner : Player) (removed : owner ∉ kept) :
      actual.recall owner = frame.recall owner := by
    change (physicalExecution actual).recall owner = frame.recall owner
    rw [physical]
    apply physicalCallbacks_no_own_response players retained owner _ frame next filteredSupport
    intro member
    exact removed (of_decide_eq_true (List.mem_filter.mp member).2)
  have inputs := (agreement.activate focal focalKept).input focal focalKept
  rw [focalAt] at occupied genuine
  exact ⟨order, retained.length, bound, actual, ordered, focalAt, actualReached,
    inputs.symm, agreement, untouched, occupied, genuine⟩

end Vegas.Examples.CommitSeedBroadcast
