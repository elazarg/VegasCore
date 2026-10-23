/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryControl

/-! # Exact source instruction ranks between actual recovery retries -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

namespace CommitRecoveryState

/-- A close either retries the saved cursor, or preserves the exact consumed
rank. Exhaustion does not add a fictitious instruction or skip a public signal. -/
theorem close_rank (state : CommitRecoveryState program) :
    (state.close.generation = state.generation ∧
      ProtocolState.remaining program state.close.point =
        ProtocolState.remaining program state.point) ∨
    (state.close.generation = state.generation + 1 ∧
      ProtocolState.remaining program state.close.point =
        ProtocolState.remaining program state.saved) := by
  unfold close
  split
  · next finished =>
    split
    · split
      · right
        exact ⟨rfl, ProtocolState.remaining_withHistory _ _ _⟩
      · left
        refine ⟨rfl, ?_⟩
        simp only [exhausted, atPoint, ProtocolState.automaticCommitBlock_remaining, restored]
        rw [ProtocolState.commitEnd_withHistory, finished.2]
    · exact Or.inl ⟨rfl, rfl⟩
  · split <;> exact Or.inl ⟨rfl, rfl⟩

/-- One original supported instruction consumes one source rank, except for
its actual retry jump. Both alternatives retain the original saved cursor. -/
theorem step_rank (state : CommitRecoveryState program)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (running : ¬ ProtocolState.terminal program state.point)
    (supported : next ∈ (state.step joint).support) :
    (next.generation = state.generation ∧
      ProtocolState.remaining program next.point + 1 =
        ProtocolState.remaining program state.point) ∨
    (next.generation = state.generation + 1 ∧
      ProtocolState.remaining program next.point =
        ProtocolState.remaining program state.saved) := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have raw : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun value reached => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint value reached)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  have consumed := ProtocolState.recoveryStep_remaining program state.point state.excluded joint
    result.1 running raw
  rcases (state.install result.1 result.2).close_rank with normal | retry
  · exact Or.inl ⟨normal.1, by rw [normal.2]; exact consumed⟩
  · exact Or.inr retry

/-- Generation cannot decrease at a legal source instruction. -/
theorem step_generation_mono (state : CommitRecoveryState program)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (supported : next ∈ (state.step joint).support) : state.generation ≤ next.generation := by
  obtain ⟨result, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  rcases (state.install result.1 result.2).close_rank with normal | retry
  · exact normal.1.ge
  · exact retry.1 ▸ Nat.le_succ _

end CommitRecoveryState

namespace Setup

/-- A genuine continuation between two states of the same generation has
exactly the source instruction length indicated by its endpoint ranks. -/
theorem commitRecovery_same_generation_length
    (setup : Setup (Player := Player) (L := L)) {fuel : Nat}
    {first last : setup.commitRecoveryProtocol.History}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel first last)
    (before after : CommitRecoveryState setup.program)
    (firstState : first.state = some before) (lastState : last.state = some after)
    (same : before.generation = after.generation) :
    ProtocolState.remaining setup.program after.point + last.trace.length =
      ProtocolState.remaining setup.program before.point + first.trace.length := by
  have forward : ∀ {budget : Nat} {start finish : setup.commitRecoveryProtocol.History},
      setup.commitRecoveryProtocol.ReachesWithin budget start finish →
      ∀ initial final, start.state = some initial → finish.state = some final →
      initial.generation ≤ final.generation := by
    intro budget start finish reached
    induction reached with
    | refl =>
        intro initial final firstState lastState
        cases Option.some.inj (firstState.symm.trans lastState)
        exact le_rfl
    | @step budget start target joint legal next supported rest ih =>
        intro initial final firstState lastState
        rcases start with ⟨state, trace⟩
        change state = some initial at firstState
        subst state
        obtain ⟨middle, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        exact (initial.step_generation_mono joint middle reached).trans
          (ih middle final equal.symm lastState)
  induction path generalizing before after with
  | refl =>
      cases Option.some.inj (firstState.symm.trans lastState)
      rfl
  | @step budget start target joint legal next supported rest ih =>
      rcases start with ⟨state, trace⟩
      change state = some before at firstState
      subst state
      obtain ⟨middle, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      have later := forward rest middle after equal.symm lastState
      have earlier := before.step_generation_mono joint middle reached
      have unchanged : before.generation = middle.generation := by omega
      have middleSame : middle.generation = after.generation := by omega
      have remaining := ih middle after equal.symm lastState middleSame
      have rank := before.step_rank joint middle legal.1 reached
      change ProtocolState.remaining setup.program after.point + target.trace.length =
        ProtocolState.remaining setup.program before.point + trace.length
      change ProtocolState.remaining setup.program after.point + target.trace.length =
        ProtocolState.remaining setup.program middle.point + (trace.length + 1) at remaining
      rcases rank with normal | retry
      · omega
      · omega

end Setup
end Vegas.SourceProgram
