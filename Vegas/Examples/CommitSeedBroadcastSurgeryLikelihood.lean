/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPrefixLikelihood
import Vegas.Examples.CommitSeedBroadcastSeedAtoms

/-! # Exact behavioral weight comparison for the repaired native prefix -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

private theorem recalled_likelihood_snoc (players : Player → app.Policy) (owner : Player)
    (past : List app.PlayerEntry) (entry : app.PlayerEntry) :
    (app.information initial horizon scheduler).ownPlayReachProbability (who := owner)
        (app.encodePolicy (players owner)) (app.recallOwnPlay (past ++ [entry])) ≤
      (app.information initial horizon scheduler).ownPlayReachProbability (who := owner)
        (app.encodePolicy (players owner)) (app.recallOwnPlay past) := by
  rw [app.recallOwnPlay_append, InformationModel.ownPlayReachProbability]
  exact mul_le_of_le_one_left
    (InformationModel.ownPlayReachProbability_nonneg ..) (pmf_toReal_apply_le_one ..)

private theorem recalled_likelihood_antitone (players : Player → app.Policy) (owner : Player)
    (earlier later : List app.PlayerEntry) (retained : earlier <+: later) :
    (app.information initial horizon scheduler).ownPlayReachProbability (who := owner)
        (app.encodePolicy (players owner)) (app.recallOwnPlay later) ≤
      (app.information initial horizon scheduler).ownPlayReachProbability (who := owner)
        (app.encodePolicy (players owner)) (app.recallOwnPlay earlier) := by
  obtain ⟨suffix, rfl⟩ := retained
  induction suffix using List.reverseRecOn with
  | nil => simp only [List.append_nil, le_refl]
  | append_singleton suffix entry ih =>
      rw [← List.append_assoc]
      exact (recalled_likelihood_snoc players owner (earlier ++ suffix) entry).trans ih

theorem nativeResponseLikelihood_nonnegative (players : Player → app.Policy)
    (execution : app.Execution) : 0 ≤ nativeResponseLikelihood players execution :=
  Finset.prod_nonneg fun _owner _ => InformationModel.ownPlayReachProbability_nonneg ..

theorem nativeResponseLikelihood_le_of_recall_prefix (players : Player → app.Policy)
    (source target : app.Execution)
    (retained : ∀ owner, target.recall owner <+: source.recall owner) :
    nativeResponseLikelihood players source ≤ nativeResponseLikelihood players target := by
  unfold nativeResponseLikelihood
  apply Finset.prod_le_prod₀
  · intro owner _
    exact InformationModel.ownPlayReachProbability_nonneg ..
  · intro owner _
    exact recalled_likelihood_antitone players owner _ _ (retained owner)

private theorem physicalCallbacks_recall_prefix (players : Player → app.Policy)
    (owners : List Player) (execution final : app.Execution)
    (reached : final ∈ (physicalCallbacks players owners execution).support) (observer : Player) :
    execution.recall observer <+: final.recall observer := by
  induction owners generalizing execution with
  | nil =>
      have same : final = physicalExecution execution := by
        simpa only [physicalCallbacks, commandComposition, List.map_nil, List.foldr_nil,
          PMF.pure_map, physicalExecution_idempotent, PMF.mem_support_pure_iff] using reached
      rw [same]
      exact List.prefix_refl _
  | cons actor owners ih =>
      obtain ⟨action, _chosen, future⟩ :=
        physicalCallbacks_cons_support players actor owners execution final reached
      have current : execution.recall observer <+:
          ((completeActivation (physicalExecution execution) actor).respond app actor
            action).recall observer :=
        app.respond_recall_prefix (completeActivation (physicalExecution execution) actor)
          actor observer action
      exact current.trans (ih _ future)

/-- Retained raw preparations have exactly the same old input and response
factors. Every deleted silent response contributes only a factor at most one. -/
theorem silent_prefix_allGood_weight (oldSeed : Seeds)
    (players witnessPlayers : Player → app.Policy)
    (frame final : app.Execution) (owners : List Player) (distinct : owners.Nodup)
    (focal : Player) (absent : focal ∉ owners) (kept : Finset Player) (focalKept : focal ∈ kept)
    (started : frame ∈ (app.runRounds (family oldSeed) witnessPlayers 5 initialExecution).support)
    (reached : final ∈ (physicalCallbacks witnessPlayers owners frame).support)
    (silent : ∀ actor ∈ owners, actor ∉ kept →
      ((final.recall actor).getLast?).map ReactiveApplication.PlayerEntry.action =
        some (⟨none⟩ : app.Action)) :
    ∃ order : Equiv.Perm Player, ∃ count : Nat, ∃ bound : count < 3, ∃ actual : app.Execution,
      (List.ofFn order).take count = owners.filter (fun owner => owner ∈ kept) ∧
      order ⟨count, bound⟩ = focal ∧
      actual ∈ (app.runRounds (family (allGoodSeed order)) witnessPlayers (5 + count)
        initialExecution).support ∧
      ((completeActivation actual focal).recall focal,
        (completeActivation actual focal).observe app focal) =
      ((completeActivation final focal).recall focal,
        (completeActivation final focal).observe app focal) ∧
      CallbackAgreement kept final actual ∧
      (∀ owner, owner ∉ kept → actual.recall owner = frame.recall owner) ∧
      (∀ owner, final.recall owner = actual.recall owner ∨
        ∃ entry : app.PlayerEntry, entry.action = (⟨none⟩ : app.Action) ∧
          final.recall owner = actual.recall owner ++ [entry]) ∧
      (nativeSeedLaw oldSeed).toReal * nativeResponseLikelihood players final ≤
        (nativeSeedLaw (allGoodSeed order)).toReal * nativeResponseLikelihood players actual ∧
      some ⟨horizon - (5 + count) - 1, some focal, completeActivation actual focal⟩ ∈
        (app.commandControlLaw (family (allGoodSeed order)) witnessPlayers initial
          (horizon - (5 + count) - 1) (5 + count)).support ∧
      Nonempty ((app.protocol initial horizon (family (allGoodSeed order))).Trace
        (some ⟨horizon - (5 + count) - 1, some focal, completeActivation actual focal⟩)) := by
  obtain ⟨order, count, bound, actual, word, actor, supported, input,
    agreement, untouched, occupied, genuine⟩ :=
    silent_prefix_allGood_native_target oldSeed witnessPlayers frame final owners distinct
      focal absent
      kept focalKept started reached silent
  have words (owner : Player) : final.recall owner = actual.recall owner ∨
      ∃ entry : app.PlayerEntry, entry.action = (⟨none⟩ : app.Action) ∧
        final.recall owner = actual.recall owner ++ [entry] := by
    by_cases member : owner ∈ kept
    · exact Or.inl (agreement.ownWord owner member)
    · rw [untouched owner member]
      by_cases acted : owner ∈ owners
      · obtain ⟨entry, wordEq, _view⟩ :=
          physicalCallbacks_unique_record witnessPlayers owners distinct
          owner acted frame final reached
        have last := silent owner acted member
        rw [wordEq, List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_singleton,
          Option.map_some] at last
        exact Or.inr ⟨entry, Option.some.inj last, wordEq⟩
      · exact Or.inl (physicalCallbacks_no_own_response witnessPlayers owners owner acted
          frame final reached)
  have behavioral : nativeResponseLikelihood players final ≤
      nativeResponseLikelihood players actual := by
    apply nativeResponseLikelihood_le_of_recall_prefix
    intro owner
    by_cases member : owner ∈ kept
    · rw [← agreement.ownWord owner member]
    · rw [untouched owner member]
      exact physicalCallbacks_recall_prefix witnessPlayers owners frame final reached owner
  have weight := mul_le_mul (nativeSeedLaw_atom_le_allGood oldSeed order) behavioral
    (nativeResponseLikelihood_nonnegative players final) ENNReal.toReal_nonneg
  exact ⟨order, count, bound, actual, word, actor, supported, input, agreement, untouched,
    words, weight,
    occupied, genuine⟩

end Vegas.Examples.CommitSeedBroadcast
