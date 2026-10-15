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
  induction block with
  | nil =>
      cases (PMF.mem_support_pure_iff ..).mp leftSupported
      cases (PMF.mem_support_pure_iff ..).mp rightSupported
      exact entryView
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      obtain ⟨firstResult, _, leftStep⟩ := (PMF.mem_support_bind_iff ..).mp leftSupported
      obtain ⟨secondResult, _, rightStep⟩ := (PMF.mem_support_bind_iff ..).mp rightSupported
      have nextView : (commitSuccessor name guard first firstResult).view who =
          (commitSuccessor name guard second secondResult).view who := by
        apply Config.view_commit_congr name guard first second entryView firstResult secondResult
        intro own
        subst who
        obtain ⟨leftAttempt⟩ := rest.prefixLaw_attempt suffix (afterCommit firstProfile)
          (commitSuccessor name guard first firstResult) left leftStep
        obtain ⟨rightAttempt⟩ := rest.prefixLaw_attempt suffix (afterCommit secondProfile)
          (commitSuccessor name guard second secondResult) right rightStep
        have leftPrefix := leftAttempt.history_prefix owner
        have rightPrefix := rightAttempt.history_prefix owner
        simp only [commitSuccessor, Function.update_self] at leftPrefix rightPrefix
        obtain ⟨leftTail, leftWord⟩ := leftPrefix
        obtain ⟨rightTail, rightWord⟩ := rightPrefix
        have priorHistory : first.history owner = second.history owner :=
          congrArg Prod.snd entryView
        have words : (first.history owner ++ [OwnAction.commit owner name payload firstResult]) ++
            leftTail = (first.history owner ++
              [OwnAction.commit owner name payload secondResult]) ++ rightTail := by
          rw [priorHistory]
          simpa only [priorHistory] using leftWord.trans (history.trans rightWord.symm)
        have heads : OwnAction.commit owner name payload firstResult =
            OwnAction.commit owner name payload secondResult := by
          have equal : OwnAction.commit owner name payload firstResult :: leftTail =
              OwnAction.commit owner name payload secondResult :: rightTail := by
            apply List.append_cancel_left (as := first.history owner)
            simpa only [List.append_assoc, List.singleton_append] using words
          exact (List.cons.inj equal).1
        simpa only [OwnAction.commit.injEq, heq_eq_eq, true_and] using heads
      exact ih suffix (afterCommit firstProfile) (afterCommit secondProfile)
        (commitSuccessor name guard first firstResult)
        (commitSuccessor name guard second secondResult) nextView left right leftStep rightStep
          history

/-- At a genuine current source view, conditioning the actual prefix law on
the complete owned view is exactly conditioning it on the effective owned
word. This does not discard the original hidden foreign choices. -/
theorem prefixPosterior_eq_history (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entry : Config Player L Γ) (who : Player) (observed : DecisionView who Δ)
    (present : observed ∈ ((block.prefixLaw suffix profile entry).map
      (Config.view who)).support) :
    block.prefixPosterior suffix profile entry who observed =
      fiberPosterior (block.prefixLaw suffix profile entry) (fun final => final.history who)
        observed.2 := by
  obtain ⟨witness, member, equal⟩ := (PMF.mem_support_map_iff ..).mp present
  apply fiberPosterior_eq_of_support_fiber
  intro final supported
  constructor
  · intro same
    exact congrArg Prod.snd same
  · intro same
    have word : final.history who = witness.history who :=
      same.trans (congrArg Prod.snd equal).symm
    exact (block.prefixLaw_view_eq_of_history_eq suffix profile profile entry entry who rfl final
      witness supported member word).trans equal

end Vegas.SourceProgram.CommitPrefix
