/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Semantics
import Vegas.Source.CommitmentInterface

/-! # Source program points and protocol observations

The sum nesting identifies a position in one fixed program. At that position
the state is the existing typed source configuration. Observations retain the
same position and exactly the existing player view. No full configuration is
passed to a strategy, and no new source executor is introduced.
-/

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

abbrev ProtocolState : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Type
  | Γ, _, .ret _ => Config Player L Γ
  | Γ, _, .sample _ _ _ next => Config Player L Γ ⊕ ProtocolState next
  | Γ, _, .commit _ _ _ _ next => Config Player L Γ ⊕ ProtocolState next
  | Γ, _, .reveal _ _ _ _ _ _ next => Config Player L Γ ⊕ ProtocolState next

abbrev ProtocolView (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Type
  | Γ, _, .ret _ => DecisionView who Γ
  | Γ, _, .sample _ _ _ next => DecisionView who Γ ⊕ ProtocolView who next
  | Γ, _, .commit _ _ _ _ next => DecisionView who Γ ⊕ ProtocolView who next
  | Γ, _, .reveal _ _ _ _ _ _ next => DecisionView who Γ ⊕ ProtocolView who next

namespace ProtocolState

def entry : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Config Player L Γ → ProtocolState program
  | _, _, .ret _, config => config
  | _, _, .sample _ _ _ _, config => Sum.inl config
  | _, _, .commit _ _ _ _ _, config => Sum.inl config
  | _, _, .reveal _ _ _ _ _ _ _, config => Sum.inl config

def observe (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → ProtocolView who program
  | _, _, .ret _ => fun config => config.view who
  | _, _, .sample _ _ _ next =>
      Sum.elim (fun config => Sum.inl (config.view who))
        (fun state => Sum.inr (observe who next state))
  | _, _, .commit _ _ _ _ next =>
      Sum.elim (fun config => Sum.inl (config.view who))
        (fun state => Sum.inr (observe who next state))
  | _, _, .reveal _ _ _ _ _ _ next =>
      Sum.elim (fun config => Sum.inl (config.view who))
        (fun state => Sum.inr (observe who next state))

def terminal : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Prop
  | _, _, .ret _ => fun _ => True
  | _, _, .sample _ _ _ next => Sum.elim (fun _ => False) (terminal next)
  | _, _, .commit _ _ _ _ next => Sum.elim (fun _ => False) (terminal next)
  | _, _, .reveal _ _ _ _ _ _ next => Sum.elim (fun _ => False) (terminal next)

end ProtocolState

namespace ProtocolView

def actor (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolView who program → Option Player
  | _, _, .ret _ => fun _ => none
  | _, _, .sample _ _ _ next => Sum.elim (fun _ => none) (actor who next)
  | _, _, .commit _ owner _ _ next => Sum.elim (fun _ => some owner) (actor who next)
  | _, _, .reveal _ owner _ _ _ _ next => Sum.elim (fun _ => some owner) (actor who next)

/-- Available actions depend on the public program point and its admission
interface. In particular they do not depend on another player's hidden value. -/
def available (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → CommitmentInterface program →
    ProtocolView who program → Set (OwnAction Player L)
  | _, _, .ret _ => fun _ _ => ∅
  | _, _, .sample _ _ _ next => fun admission =>
      Sum.elim (fun _ => ∅) (available who next admission)
  | _, _, .commit (payload := payload) name owner _ _ next => fun admission =>
      Sum.elim
        (fun _ => { action | ∃ choice : PublicationResult (L.Val payload),
          (admission none).Admits choice ∧ action = .commit owner name payload choice })
        (available who next (fun site => admission (some site)))
  | _, _, .reveal _ owner name _ _ _ next => fun admission =>
      Sum.elim (fun _ => { action | ∃ disclose, action = .reveal owner name disclose })
        (available who next admission)

def menu (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (view : ProtocolView who program) (choice : Option (OwnAction Player L)) : Prop :=
  match choice with
  | some action =>
      actor who program view = some who ∧ action ∈ available who program admission view
  | none => actor who program view ≠ some who

end ProtocolView

/-- The active player is determined by the program point, independently of
which player's observation is used to read it. -/
theorem ProtocolState.actor_observe : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    (first second : Player) →
    ProtocolView.actor first program (ProtocolState.observe first program state) =
      ProtocolView.actor second program (ProtocolState.observe second program state)
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, state, first, second => by
      cases state with
      | inl _ => rfl
      | inr rest => exact actor_observe next rest first second
  | _, _, .commit _ _ _ _ next, state, first, second => by
      cases state with
      | inl _ => rfl
      | inr rest => exact actor_observe next rest first second
  | _, _, .reveal _ _ _ _ _ _ next, state, first, second => by
      cases state with
      | inl _ => rfl
      | inr rest => exact actor_observe next rest first second

end Vegas.SourceProgram
