/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixWord

/-! # Complete owned source words enumerate the exact chronological actions -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- A supported full commitment word contains exactly the original effective
own actions in source order. Foreign slots contribute no owned action, and
accepted failed results contribute their genuine failed commitment action. -/
theorem prefixLaw_wordAction_history (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entry : Config Player L Γ) (who : Player) (final : Config Player L Δ)
    (supported : final ∈ (block.prefixLaw suffix profile entry).support) :
    final.history who = entry.history who ++
      (List.range block.length).filterMap (fun index => block.wordAction who index
        (final.view who)) := by
  induction block with
  | nil =>
      cases (PMF.mem_support_pure_iff ..).mp supported
      simp only [length, List.range_zero, List.filterMap_nil, List.append_nil]
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      obtain ⟨result, _chosen, later⟩ := (PMF.mem_support_bind_iff ..).mp supported
      have tail := ih suffix (afterCommit profile) (commitSuccessor name guard entry result)
        final later
      have preView : rest.entryView who (final.view who) =
          (commitSuccessor name guard entry result).view who := by
        have member : rest.entryView who (final.view who) ∈
            (((rest.prefixLaw suffix (afterCommit profile)
              (commitSuccessor name guard entry result)).map (Config.view who)).map
                (rest.entryView who)).support := by
          exact (PMF.mem_support_map_iff ..).mpr
            ⟨final.view who, (PMF.mem_support_map_iff ..).mpr ⟨final, later, rfl⟩, rfl⟩
        rw [rest.prefixLaw_entryView] at member
        exact (PMF.mem_support_pure_iff ..).mp member
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


end Vegas.SourceProgram.CommitPrefix
