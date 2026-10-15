/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPhaseRecovery
import Vegas.Source.ProtocolTermination

/-! # Source frontiers and retained recall through commitment retries -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- The complete private action lists at the current typed program point. -/
def history : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → History Player L
  | _, _, .ret _, config => Config.history config
  | _, _, .sample _ _ _ next, state => state.elim (fun config => Config.history config)
      (history next)
  | _, _, .commit _ _ _ _ next, state => state.elim (fun config => Config.history config)
      (history next)
  | _, _, .reveal _ _ _ _ _ _ next, state =>
      state.elim (fun config => Config.history config)
      (history next)

/-- Replace recall alone, leaving every semantic field and the program point intact. -/
def withHistory : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → History Player L →
      ProtocolState program
  | _, _, .ret _, config, past => { config with history := past }
  | _, _, .sample _ _ _ next, state, past =>
      state.elim (fun config => Sum.inl { config with history := past })
        (fun later => Sum.inr (withHistory next later past))
  | _, _, .commit _ _ _ _ next, state, past =>
      state.elim (fun config => Sum.inl { config with history := past })
        (fun later => Sum.inr (withHistory next later past))
  | _, _, .reveal _ _ _ _ _ _ next, state, past =>
      state.elim (fun config => Sum.inl { config with history := past })
        (fun later => Sum.inr (withHistory next later past))

@[simp] theorem history_withHistory : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program)
    (past : History Player L),
    history program (withHistory program state past) = past
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, state, past => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact history_withHistory next state past
  | _, _, .commit _ _ _ _ next, state, past => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact history_withHistory next state past
  | _, _, .reveal _ _ _ _ _ _ next, state, past => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact history_withHistory next state past

@[simp] theorem withHistory_history : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program),
    withHistory program state (history program state) = state
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, state => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact congrArg Sum.inr (withHistory_history next state)
  | _, _, .commit _ _ _ _ next, state => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact congrArg Sum.inr (withHistory_history next state)
  | _, _, .reveal _ _ _ _ _ _ next, state => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact congrArg Sum.inr (withHistory_history next state)

@[simp] theorem withHistory_withHistory : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program)
    (first second : History Player L),
    withHistory program (withHistory program state first) second = withHistory program state second
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, state, first, second => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact congrArg Sum.inr (withHistory_withHistory next state first second)
  | _, _, .commit _ _ _ _ next, state, first, second => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact congrArg Sum.inr (withHistory_withHistory next state first second)
  | _, _, .reveal _ _ _ _ _ _ next, state, first, second => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact congrArg Sum.inr (withHistory_withHistory next state first second)

@[simp] theorem remaining_withHistory : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program)
    (past : History Player L),
    remaining program (withHistory program state past) = remaining program state
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, state, past => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact remaining_withHistory next state past
  | _, _, .commit _ _ _ _ next, state, past => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact remaining_withHistory next state past
  | _, _, .reveal _ _ _ _ _ _ next, state, past => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact remaining_withHistory next state past

def actor : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Option Player
  | _, _, .ret _, _ => none
  | _, _, .sample _ _ _ next, state => state.elim (fun _ => none) (actor next)
  | _, _, .commit _ owner _ _ next, state => state.elim (fun _ => some owner) (actor next)
  | _, _, .reveal _ owner _ _ _ _ next, state => state.elim (fun _ => some owner) (actor next)

theorem actor_observe_eq : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program) (who : Player),
    ProtocolView.actor who program (observe who program state) = actor program state
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, state, who => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact actor_observe_eq next state who
  | _, _, .commit _ _ _ _ next, state, who => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact actor_observe_eq next state who
  | _, _, .reveal _ _ _ _ _ _ next, state, who => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact actor_observe_eq next state who

def atCommit : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Bool
  | _, _, .ret _, _ => false
  | _, _, .sample _ _ _ next, state => state.elim (fun _ => false) (atCommit next)
  | _, _, .commit _ _ _ _ next, state => state.elim (fun _ => true) (atCommit next)
  | _, _, .reveal _ _ _ _ _ _ next, state => state.elim (fun _ => false) (atCommit next)

/-- Owners of the maximal commitment block beginning at this source point. -/
def commitOwners : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Finset Player
  | _, _, .ret _, _ => ∅
  | _, _, .sample _ _ _ next, state => state.elim (fun _ => ∅) (commitOwners next)
  | _, _, program@(.commit _ _ _ _ next), state =>
      state.elim (fun _ => (commitPhase program).block.owners) (commitOwners next)
  | _, _, .reveal _ _ _ _ _ _ next, state => state.elim (fun _ => ∅) (commitOwners next)

/-- The remaining source rank after the current maximal commitment block. -/
def commitEnd : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Nat
  | _, _, .ret _, _ => 0
  | _, _, program@(.sample _ _ _ next), state =>
      state.elim (fun _ => instructionCount program) (commitEnd next)
  | _, _, program@(.commit _ _ _ _ next), state =>
      state.elim (fun _ => instructionCount (commitPhase program).suffix) (commitEnd next)
  | _, _, program@(.reveal _ _ _ _ _ _ next), state =>
      state.elim (fun _ => instructionCount program) (commitEnd next)

/-- Fill only the current commitment block automatically, stopping before its
next sample or reveal. No owned action is recorded. -/
def automaticCommitBlock : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → ProtocolState program
  | _, _, .ret _, state => state
  | _, _, .sample _ _ _ next, state =>
      state.elim Sum.inl (fun later => Sum.inr (automaticCommitBlock next later))
  | _, _, .commit name owner _ _ next, state =>
      state.elim
        (fun config => Sum.inr (automaticCommitBlock next
          (entry next (automaticCommit name owner _ config))))
        (fun later => Sum.inr (automaticCommitBlock next later))
  | _, _, .reveal _ _ _ _ _ _ next, state =>
      state.elim Sum.inl (fun later => Sum.inr (automaticCommitBlock next later))

@[simp] theorem history_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    history program (entry program config) = Config.history config := by cases program <;> rfl

@[simp] theorem commitEnd_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    commitEnd program (entry program config) = instructionCount (commitPhase program).suffix := by
  cases program <;> rfl

@[simp] theorem commitEnd_withHistory : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program)
    (past : History Player L),
    commitEnd program (withHistory program state past) = commitEnd program state
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, state, past => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact commitEnd_withHistory next state past
  | _, _, .commit _ _ _ _ next, state, past => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact commitEnd_withHistory next state past
  | _, _, .reveal _ _ _ _ _ _ next, state, past => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact commitEnd_withHistory next state past

@[simp] theorem automaticCommitBlock_remaining :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (state : ProtocolState program),
      remaining program (automaticCommitBlock program state) = commitEnd program state
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, state => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact automaticCommitBlock_remaining next state
  | _, _, .commit name owner _ _ next, state => by
      cases state with
      | inl config =>
          simpa only [automaticCommitBlock, Sum.elim_inl, remaining, Sum.elim_inr, commitEnd,
            commitPhase, commitEnd_entry] using automaticCommitBlock_remaining next
              (entry next (automaticCommit name owner _ config))
      | inr state =>
          exact automaticCommitBlock_remaining next state
  | _, _, .reveal _ _ _ _ _ _ next, state => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact automaticCommitBlock_remaining next state

theorem remaining_le_instructionCount : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program),
    remaining program state ≤ instructionCount program
  | _, _, .ret _, _ => le_rfl
  | _, _, .sample _ _ _ next, state => by
      cases state with
      | inl _ =>
          exact le_rfl
      | inr state =>
          exact (remaining_le_instructionCount next state).trans (Nat.le_succ _)
  | _, _, .commit _ _ _ _ next, state => by
      cases state with
      | inl _ =>
          exact le_rfl
      | inr state =>
          exact (remaining_le_instructionCount next state).trans (Nat.le_succ _)
  | _, _, .reveal _ _ _ _ _ _ next, state => by
      cases state with
      | inl _ =>
          exact le_rfl
      | inr state =>
          exact (remaining_le_instructionCount next state).trans (Nat.le_succ _)

@[simp] theorem automaticCommitBlock_history : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program),
    history program (automaticCommitBlock program state) = history program state
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, state => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact automaticCommitBlock_history next state
  | _, _, .commit name owner _ _ next, state => by
      cases state with
      | inl config =>
          simpa only [automaticCommitBlock, Sum.elim_inl, history, Sum.elim_inr, history_entry,
            automaticCommit] using automaticCommitBlock_history next
              (entry next (automaticCommit name owner _ config))
      | inr state =>
          exact automaticCommitBlock_history next state
  | _, _, .reveal _ _ _ _ _ _ next, state => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact automaticCommitBlock_history next state

end ProtocolState
end Vegas.SourceProgram
