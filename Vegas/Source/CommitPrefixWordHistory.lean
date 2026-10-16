/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixWord
import Vegas.Source.CommitPrefixAttemptReadout

/-! # Complete owned source words enumerate the exact chronological actions -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

omit [IExpr.ResultTypes L] in
/-- A supported full commitment word contains exactly the original effective
own actions in source order. Foreign slots contribute no owned action, and
accepted failed results contribute their genuine failed commitment action. -/
theorem Attempt.wordAction_history (block : CommitPrefix Γ O Δ P)
    (entry : Config Player L Γ) (who : Player) (final : Config Player L Δ)
    (attempt : block.Attempt entry ∅ final ∅) :
    final.history who = entry.history who ++
      (List.range block.length).filterMap (fun index => block.wordAction who index
        (final.view who)) := by
  induction block with
  | nil =>
      cases attempt
      simp only [length, List.range_zero, List.filterMap_nil, List.append_nil]
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      obtain ⟨result, ⟨later⟩⟩ := attempt.clear_tail
      have tail := ih (commitSuccessor name guard entry result) final later
      have preView := Attempt.entryView_eq rest (commitSuccessor name guard entry result)
        final later who
      rw [length, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
      simp only [Function.comp_def, wordAction]
      by_cases own : owner = who
      · subst who
        have cell : (((rest.entryView owner (final.view owner)).1.cells name
            (.commitment owner payload) .here).getD .failure) = result := by
          rw [preView]
          simp only [Config.view, commitSuccessor, sourceObserve_commitment, ite_true,
            Option.getD_some]
          rfl
        simp only [ite_true, cell]
        simpa only [commitSuccessor, Function.update_self, List.append_assoc,
          List.singleton_append] using tail
      · simp only [ite_eq_right own]
        simpa only [commitSuccessor, Function.update_of_ne (Ne.symm own)] using tail

/-- A supported chronological source word retains the exact original owned
history, with all accepted failed choices preserved. -/
theorem prefixLaw_wordAction_history (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entry : Config Player L Γ) (who : Player) (final : Config Player L Δ)
    (supported : final ∈ (block.prefixLaw suffix profile entry).support) :
    final.history who = entry.history who ++
      (List.range block.length).filterMap (fun index => block.wordAction who index
        (final.view who)) := by
  obtain ⟨attempt⟩ := block.prefixLaw_attempt suffix profile entry final supported
  exact Attempt.wordAction_history block entry who final attempt

end Vegas.SourceProgram.CommitPrefix
