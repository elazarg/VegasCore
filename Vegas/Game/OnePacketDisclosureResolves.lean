/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.IntendedForPlayer
import Vegas.Game.OnePacketOpeningUnique

/-! # Disclosures resolve at states forced for the observer

From a point intended for a player at which no reveal of the player has failed,
a step in which the player discloses leaves no failed reveal of the player
(`Vegas.SourceProgram.ProtocolState.not_revealFailed_step`). The source action
decoded from a disclosure discloses
(`Vegas.SourceProgram.decodeEventAction_disclosure_true`).
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The source action decoded from a disclosure discloses. -/
theorem decodeEventAction_disclosure_true {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (bound : count < eventCount program) {payload : L.Ty}
      (outputEq : outputLayout program ⟨count, bound⟩ = .publication payload),
      OwnAction.disclosure (decodeEventAction program ⟨count, bound⟩
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)) = true := by
  induction program with
  | ret _ =>
      intro count bound
      simp [eventCount] at bound
  | sample _ _ _ next ih =>
      intro count bound payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | commit name commitOwner fresh guard next ih =>
      intro count bound payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | reveal published revealOwner name fresh source unresolved next ih =>
      intro count bound payload outputEq
      cases count with
      | zero => rfl
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq

namespace ProtocolState

/-- No reveal has failed at a program's entry. -/
theorem not_revealFailed_entry (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    ¬ RevealFailed who program (entry program config) := by
  cases program <;> exact fun failed => failed

/-- **A disclosing player's reveals stay successful.** From a point intended for
a player at which no reveal of the player has failed, a step in which the
player discloses at its reveals leaves no failed reveal of the player. -/
theorem not_revealFailed_step (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → (target : ProtocolState program) →
    IntendedFor who program state → ¬ RevealFailed who program state →
    OwnAction.disclosure (joint who) = true →
    target ∈ (step program state joint).support → ¬ RevealFailed who program target
  | _, _, .ret _, _, _, _, _, clean, _, reached => by
      rw [step, PMF.mem_support_pure_iff] at reached
      rw [reached]
      exact clean
  | _, _, .sample _ _ _ next, state, joint, target, intended, clean, discloses, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          exact not_revealFailed_entry who next _
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact not_revealFailed_step who next rest joint after intended clean discloses supported
  | _, _, .commit _ _ _ _ next, state, joint, target, intended, clean, discloses, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          exact not_revealFailed_entry who next _
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact not_revealFailed_step who next rest joint after intended clean discloses supported
  | _, _, .reveal published owner name fresh source _ next, state, joint, target, intended,
      clean, discloses, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          rintro (⟨same, failed⟩ | later)
          · subst same
            rw [discloses] at failed
            obtain ⟨_, value, opened⟩ := Config.IntendedFor.reveal_own intended fresh source
            rw [base_entry, opened] at failed
            cases failed
          · exact not_revealFailed_entry who next _ later
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rintro (⟨same, failed⟩ | later)
          · exact clean (Or.inl ⟨same, (base_step next rest joint after supported) ▸ failed⟩)
          · exact not_revealFailed_step who next rest joint after intended
              (fun earlier => clean (Or.inr earlier)) discloses supported later

/-- **A stored failed publication is a failed reveal.** A point decoded past a
reveal of `who` whose stored publication is a failure shows `who`'s reveal
failed. -/
theorem revealFailed_of_decode_failure {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (state : ProtocolState program) (bound : count < eventCount program) (who : Player)
      (payload : L.Ty) (publication : outputLayout program ⟨count, bound⟩ = .publication payload),
      decodeSourcePrefix? program refs registry revelations outputs (count + 1) store history =
          some state →
      eventOwner? program ⟨count, bound⟩ = some who →
      (outputs ⟨count, bound⟩).get? store = some (cast
        (congrArg EventGraph.EventField.Value publication.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload))) →
      RevealFailed who program state := by
  induction program with
  | ret _ =>
      intro count _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro count refs registry revelations outputs store history state bound who payload
        publication decoded owned read
      cases count with
      | zero => cases publication
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) who payload
            publication restDecoded owned read
  | commit name owner fresh guard next ih =>
      intro count refs registry revelations outputs store history state bound who payload
        publication decoded owned read
      cases count with
      | zero => cases publication
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) who payload
            publication restDecoded owned read
  | reveal published owner name fresh source unresolved next ih =>
      intro count refs registry revelations outputs store history state bound who payload
        publication decoded owned read
      cases count with
      | zero =>
          cases Option.some.inj owned
          cases publication
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          obtain ⟨cells, cellsDecoded, rfl⟩ := Option.map_eq_some_iff.mp restDecoded
          refine Or.inl ⟨rfl, ?_⟩
          rw [base_entry]
          unfold decodeState? at cellsDecoded
          erw [read] at cellsDecoded
          obtain ⟨head, headEq, rest⟩ := Option.bind_eq_some_iff.mp cellsDecoded
          obtain ⟨tail, _, cellsEq⟩ := Option.bind_eq_some_iff.mp rest
          cases Option.some.inj headEq
          cases Option.some.inj cellsEq
          rfl
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact Or.inr (ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) who
            payload publication restDecoded owned read)

end ProtocolState

end Vegas.SourceProgram
