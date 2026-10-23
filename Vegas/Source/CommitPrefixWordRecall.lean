/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixInformationLaw

/-! # Owned-word recall determines the supported commitment view

At a fixed commitment position, the entry owned view and chronological owned
actions determine the full current owned view. Hidden foreign choices and
accepted failed choices remain permitted.
-/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

omit [IExpr.ResultTypes L] in
/-- An actually clear commitment has a nonmissing clear typed tail. -/
theorem Attempt.clear_tail
    {name : VarId} {owner : Player} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {rest : CommitPrefix ((name, .commitment owner payload) :: Γ) (insert name O) Δ P}
    {entry : Config Player L Γ} {final : Config Player L Δ}
    (attempt : (CommitPrefix.commit name owner fresh guard rest).Attempt entry ∅ final ∅) :
    ∃ result, Nonempty (rest.Attempt (commitSuccessor name guard entry result) ∅ final ∅) := by
  cases attempt with
  | active _ result missed _ later =>
      cases missed with
      | false => exact ⟨result, ⟨later⟩⟩
      | true =>
          have included := later.excluded_subset
          have member : owner ∈ excludeCommit ∅ owner true := by simp only [excludeCommit,
            ite_true, Finset.mem_insert, true_or]
          exact (Finset.notMem_empty owner (included member)).elim
  | excluded inactive _later => exact (Finset.notMem_empty owner inactive).elim

omit [IExpr.ResultTypes L] in
/-- Through actual clear typed attempts, the entry owned view and final
original own-action word determine the complete final owned view. No source
strategy, support or independence hypothesis is needed. -/
theorem Attempt.view_eq_of_history_eq (block : CommitPrefix Γ O Δ P)
    (first second : Config Player L Γ) (who : Player)
    (entryView : first.view who = second.view who)
    (left right : Config Player L Δ)
    (leftAttempt : block.Attempt first ∅ left ∅)
    (rightAttempt : block.Attempt second ∅ right ∅)
    (history : left.history who = right.history who) : left.view who = right.view who := by
  induction block with
  | nil =>
      cases leftAttempt
      cases rightAttempt
      exact entryView
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      obtain ⟨firstResult, ⟨leftTail⟩⟩ := Attempt.clear_tail leftAttempt
      obtain ⟨secondResult, ⟨rightTail⟩⟩ := Attempt.clear_tail rightAttempt
      have nextView : (commitSuccessor name guard first firstResult).view who =
          (commitSuccessor name guard second secondResult).view who := by
        apply Config.view_commit_congr name guard first second entryView firstResult secondResult
        intro own
        subst who
        have leftPrefix := leftTail.history_prefix owner
        have rightPrefix := rightTail.history_prefix owner
        simp only [commitSuccessor, Function.update_self] at leftPrefix rightPrefix
        obtain ⟨leftWord, leftEqual⟩ := leftPrefix
        obtain ⟨rightWord, rightEqual⟩ := rightPrefix
        have prior : first.history owner = second.history owner := congrArg Prod.snd entryView
        have words : (first.history owner ++ [OwnAction.commit owner name payload firstResult]) ++
            leftWord = (first.history owner ++
              [OwnAction.commit owner name payload secondResult]) ++ rightWord := by
          rw [prior]
          simpa only [prior] using leftEqual.trans (history.trans rightEqual.symm)
        have heads : OwnAction.commit owner name payload firstResult =
            OwnAction.commit owner name payload secondResult := by
          have equal : OwnAction.commit owner name payload firstResult :: leftWord =
              OwnAction.commit owner name payload secondResult :: rightWord := by
            apply List.append_cancel_left (as := first.history owner)
            simpa only [List.append_assoc, List.singleton_append] using words
          exact (List.cons.inj equal).1
        simpa only [OwnAction.commit.injEq, heq_eq_eq, true_and] using heads
      exact ih (commitSuccessor name guard first firstResult)
        (commitSuccessor name guard second secondResult) nextView left right leftTail rightTail
          history

/-- Equal effective owned words reconstruct the same complete owned view in
any two supported executions of one typed commitment prefix. -/
theorem prefixLaw_view_eq_of_history_eq (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (firstProfile secondProfile : BehavioralProfile (block.prepend suffix))
    (first second : Config Player L Γ) (who : Player)
    (entryView : first.view who = second.view who)
    (left right : Config Player L Δ)
    (leftSupported : left ∈ (block.prefixLaw suffix firstProfile first).support)
    (rightSupported : right ∈ (block.prefixLaw suffix secondProfile second).support)
    (history : left.history who = right.history who) : left.view who = right.view who := by
  obtain ⟨leftAttempt⟩ := block.prefixLaw_attempt suffix firstProfile first left leftSupported
  obtain ⟨rightAttempt⟩ := block.prefixLaw_attempt suffix secondProfile second right rightSupported
  exact Attempt.view_eq_of_history_eq block first second who entryView left right leftAttempt
    rightAttempt history

end Vegas.SourceProgram.CommitPrefix
