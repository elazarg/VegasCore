/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryErasure
import Vegas.Source.SetupProtocolRecall

/-! # Honest source recall reconstructed from live typed observations

Commit values persist in typed cells and every intended disclosure is TRUE.
Consequently the current typed observation reconstructs the original own word,
without selecting a history or assuming equality of remembered actions.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolView

/-- Read the intended own action word from the original immutable typed cells. -/
def intendedWord (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolView who program → List (OwnAction Player L)
  | _, _, .ret _, _ => []
  | _, _, .sample _ _ _ next, view => view.elim (fun _ => []) (intendedWord who next)
  | _, _, .commit (payload := payload) name owner _ _ next, view =>
      view.elim (fun _ => []) fun later =>
        (if owner = who then
          [.commit owner name payload
            (((entryView who next later).1.cells.get .here).getD .failure)] else []) ++
          intendedWord who next later
  | _, _, .reveal _ owner name _ _ _ next, view =>
      view.elim (fun _ => []) fun later =>
        (if owner = who then [.reveal owner name true] else []) ++ intendedWord who next later

@[simp] theorem intendedWord_observe_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    intendedWord who program (ProtocolState.observe who program
      (ProtocolState.entry program config)) = [] := by
  cases program <;> rfl

private theorem intended_none_of_other (who : Player) {Γ : SourceCtx Player L}
    {O : Finset VarId} {program : SourceProgram Player L Γ O}
    {view : ProtocolView who program} {choice : Option (OwnAction Player L)}
    (legal : intendedMenu who program view choice) (other : actor who program view ≠ some who) :
    choice = none := by
  cases choice with
  | none => rfl
  | some action => exact (other legal.1).elim

/-- An actual intended source instruction appends the same raw own action to
both remembered recall and the word reconstructed from immutable typed cells. -/
theorem intended_step_word (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (before after : ProtocolState program)
      (joint : Player → Option (OwnAction Player L)),
      intendedMenu who program (ProtocolState.observe who program before) (joint who) →
      after ∈ (ProtocolState.step program before joint).support →
      intendedWord who program (ProtocolState.observe who program after) =
          intendedWord who program (ProtocolState.observe who program before) ++
            (joint who).toList ∧
        ProtocolState.history program after who =
          ProtocolState.history program before who ++ (joint who).toList
  | _, _, .ret _, before, after, joint, legal, supported => by
      have inactive := intended_none_of_other who legal (by simp [actor])
      have result := (PMF.mem_support_pure_iff _ _).mp supported
      subst after
      simp [intendedWord, ProtocolState.history, inactive]
  | _, _, .sample name fresh law next, before, after, joint, legal, supported => by
      cases before with
      | inl config =>
          have inactive := intended_none_of_other who legal
            (by simp [actor, ProtocolState.observe])
          obtain ⟨value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          simp [intendedWord, ProtocolState.observe, ProtocolState.history,
            sampleSuccessor, inactive]
      | inr rest =>
          obtain ⟨after, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact intended_step_word who next rest after joint legal reached
  | _, _, .commit name owner fresh guard next, before, after, joint, legal, supported => by
      cases before with
      | inl config =>
          have result := (PMF.mem_support_pure_iff _ _).mp supported
          subst after
          by_cases own : owner = who
          · subst who
            cases selected : joint owner with
            | none =>
                rw [selected] at legal
                exact (legal (by rfl)).elim
            | some action =>
                rw [selected] at legal
                obtain ⟨value, _, rfl⟩ := legal.2
                simp [intendedWord, ProtocolState.observe, ProtocolState.history,
                  commitSuccessor, Config.view, sourceObserve]
                simp [Env.get, Env.cons]
          · have inactive := intended_none_of_other who legal
              (by simpa [actor, ProtocolState.observe] using own)
            simp [intendedWord, ProtocolState.observe, ProtocolState.history,
              commitSuccessor, Config.view, own, inactive, Function.update_of_ne (Ne.symm own)]
      | inr rest =>
          obtain ⟨after, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          obtain ⟨words, memories⟩ := intended_step_word who next rest after joint legal reached
          have entry := entryView_step who next rest after joint reached
          simp only [intendedWord, ProtocolState.observe, Sum.elim_inr, entry, words,
            List.append_assoc, ProtocolState.history]
          exact ⟨trivial, memories⟩
  | _, _, .reveal published owner name fresh source unresolved next,
      before, after, joint, legal, supported => by
      cases before with
      | inl config =>
          have result := (PMF.mem_support_pure_iff _ _).mp supported
          subst after
          by_cases own : owner = who
          · subst who
            cases selected : joint owner with
            | none =>
                rw [selected] at legal
                exact (legal (by rfl)).elim
            | some action =>
                rw [selected] at legal
                have chosen : action = .reveal owner name true := legal.2
                subst action
                simp [intendedWord, ProtocolState.observe, ProtocolState.history,
                  revealSuccessor, Config.view, OwnAction.disclosure]
          · have inactive := intended_none_of_other who legal
              (by simpa [actor, ProtocolState.observe] using own)
            simp [intendedWord, ProtocolState.observe, ProtocolState.history,
              revealSuccessor, Config.view, own, inactive, Function.update_of_ne (Ne.symm own)]
      | inr rest =>
          obtain ⟨after, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          obtain ⟨words, memories⟩ := intended_step_word who next rest after joint legal reached
          simp only [intendedWord, ProtocolState.observe, Sum.elim_inr, words,
            List.append_assoc, ProtocolState.history]
          exact ⟨trivial, memories⟩

end ProtocolView

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- Genuine intended histories have exactly the own word reconstructed from
live typed cells, including at off-path intended information states. -/
theorem intended_history_of_typed_view (who : Player) :
    ∀ {state : setup.intendedProtocol.State} (_trace : setup.intendedProtocol.Trace state),
      ∀ point, state = some point →
        ProtocolState.history setup.program point who =
          ProtocolView.intendedWord who setup.program
            (ProtocolState.observe who setup.program point)
 := by
  intro state trace
  induction trace with
  | start => intro point same; cases same
  | @extend before _ prior joint legal supported ih =>
      intro point same
      subst same
      cases before with
      | none =>
          obtain ⟨inputs, _, result⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          cases Option.some.inj result
          simp [initialConfig, ProtocolState.history_entry]
      | some before =>
          obtain ⟨after, reached, result⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          cases Option.some.inj result
          have localLegal : ProtocolView.intendedMenu who setup.program
              (ProtocolState.observe who setup.program before) (joint who) := by
            have permitted := legalOption_of_legal legal who
            revert permitted
            cases joint who <;> exact id
          obtain ⟨word, memory⟩ := ProtocolView.intended_step_word who setup.program
            before point joint localLegal reached
          rw [memory, ih before rfl, ← word]

end Setup
end Vegas.SourceProgram
