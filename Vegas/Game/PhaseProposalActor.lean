/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.SequentialLaw
import Vegas.Compile.EventGraphPolicy
import Vegas.Source.CommitRecoveryPoint

/-! # Actual source cursors select the same compiled event owner -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem source_actor_eventOwner : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (event : Fin (eventCount program)),
    event.val = instructionCount program - ProtocolState.remaining program point →
    ProtocolState.actor program point = eventOwner? program event := by
  intro Γ O program
  induction program with
  | ret payoff => intro point event; exact Fin.elim0 event
  | sample name fresh law next ih =>
      intro point event ranked
      cases point with
      | inl entry =>
          have zero : event.val = 0 := by
            simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl, Nat.sub_self]
              using ranked
          have same : event = ⟨0, by simpa only [eventCount] using Nat.zero_lt_succ _⟩ :=
            Fin.ext zero
          subst event
          rfl
      | inr later =>
          have bounded := ProtocolState.remaining_le_instructionCount next later
          have positive : 0 < event.val := by
            simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at ranked
            omega
          let previous : Fin (eventCount next) := ⟨event.val - 1, by
            have bound := event.isLt
            simp only [eventCount] at bound
            omega⟩
          have same : Fin.succ previous = event := Fin.ext (by dsimp [previous]; omega)
          rw [← same]
          exact ih later previous (by dsimp [previous]; simp only [instructionCount,
            ProtocolState.remaining, Sum.elim_inr] at ranked; omega)
  | commit name owner fresh guard next ih =>
      intro point event ranked
      cases point with
      | inl entry =>
          have zero : event.val = 0 := by
            simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl, Nat.sub_self]
              using ranked
          have same : event = ⟨0, by simpa only [eventCount] using Nat.zero_lt_succ _⟩ :=
            Fin.ext zero
          subst event
          rfl
      | inr later =>
          have bounded := ProtocolState.remaining_le_instructionCount next later
          have positive : 0 < event.val := by
            simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at ranked
            omega
          let previous : Fin (eventCount next) := ⟨event.val - 1, by
            have bound := event.isLt
            simp only [eventCount] at bound
            omega⟩
          have same : Fin.succ previous = event := Fin.ext (by dsimp [previous]; omega)
          rw [← same]
          exact ih later previous (by dsimp [previous]; simp only [instructionCount,
            ProtocolState.remaining, Sum.elim_inr] at ranked; omega)
  | reveal published owner name fresh source unresolved next ih =>
      intro point event ranked
      cases point with
      | inl entry =>
          have zero : event.val = 0 := by
            simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl, Nat.sub_self]
              using ranked
          have same : event = ⟨0, by simpa only [eventCount] using Nat.zero_lt_succ _⟩ :=
            Fin.ext zero
          subst event
          rfl
      | inr later =>
          have bounded := ProtocolState.remaining_le_instructionCount next later
          have positive : 0 < event.val := by
            simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at ranked
            omega
          let previous : Fin (eventCount next) := ⟨event.val - 1, by
            have bound := event.isLt
            simp only [eventCount] at bound
            omega⟩
          have same : Fin.succ previous = event := Fin.ext (by dsimp [previous]; omega)
          rw [← same]
          exact ih later previous (by dsimp [previous]; simp only [instructionCount,
            ProtocolState.remaining, Sum.elim_inr] at ranked; omega)

/-- The logical cursor is a static source rank; observation and physical
interleaving do not select a different compiled owner. -/
theorem source_actor_at_compiled_rank {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (mode : ExecutionMode)
    (point : ProtocolState program)
    (event : ((toEventGraph program).withMode mode).EventId)
    (ranked : event.val = instructionCount program - ProtocolState.remaining program point) :
    ProtocolState.actor program point = ((toEventGraph program).withMode mode).actor? event :=
  (source_actor_eventOwner program point event ranked).trans (eventOwner?_eq_actor program event)

/-- A literal source commitment point has a binding field at its compiled event. -/
theorem source_binding_of_commit_at_rank :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (event : Fin (eventCount program)),
      event.val = instructionCount program - ProtocolState.remaining program point →
      ProtocolState.atCommit program point = true →
      ∃ owner payload, outputLayout program event = .binding owner payload := by
  intro Γ O program
  induction program with
  | ret payoff => intro point event; exact Fin.elim0 event
  | sample name fresh law next ih =>
      intro point event ranked committing
      cases point with
      | inl entry => cases committing
      | inr later =>
          have bounded := ProtocolState.remaining_le_instructionCount next later
          have positive : 0 < event.val := by
            simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at ranked
            omega
          let previous : Fin (eventCount next) := ⟨event.val - 1, by
            have bound := event.isLt
            simp only [eventCount] at bound
            omega⟩
          have same : Fin.succ previous = event := Fin.ext (by dsimp [previous]; omega)
          rw [← same]
          exact ih later previous (by
            dsimp only [previous]
            simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at ranked
            omega) committing
  | commit name owner fresh guard next ih =>
      intro point event ranked committing
      cases point with
      | inl entry =>
          have zero : event.val = 0 := by
            simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl, Nat.sub_self]
              using ranked
          have same : event = ⟨0, by simp only [eventCount]; omega⟩ := Fin.ext zero
          rw [same]
          exact ⟨owner, _, rfl⟩
      | inr later =>
          have bounded := ProtocolState.remaining_le_instructionCount next later
          have positive : 0 < event.val := by
            simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at ranked
            omega
          let previous : Fin (eventCount next) := ⟨event.val - 1, by
            have bound := event.isLt
            simp only [eventCount] at bound
            omega⟩
          have same : Fin.succ previous = event := Fin.ext (by dsimp [previous]; omega)
          rw [← same]
          exact ih later previous (by
            dsimp only [previous]
            simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at ranked
            omega) committing
  | reveal published owner name fresh source unresolved next ih =>
      intro point event ranked committing
      cases point with
      | inl entry => cases committing
      | inr later =>
          have bounded := ProtocolState.remaining_le_instructionCount next later
          have positive : 0 < event.val := by
            simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at ranked
            omega
          let previous : Fin (eventCount next) := ⟨event.val - 1, by
            have bound := event.isLt
            simp only [eventCount] at bound
            omega⟩
          have same : Fin.succ previous = event := Fin.ext (by dsimp [previous]; omega)
          rw [← same]
          exact ih later previous (by
            dsimp only [previous]
            simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at ranked
            omega) committing

end Vegas
