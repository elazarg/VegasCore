/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Protocol
import GameTheory.Protocol.Backward

/-! # Finite source protocol execution

Every transition consumes exactly one source instruction, including chance.
The resulting bounds cover arbitrary legal choices and off-path histories.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def instructionCount : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Nat
  | _, _, .ret _ => 0
  | _, _, .sample _ _ _ next => instructionCount next + 1
  | _, _, .commit _ _ _ _ next => instructionCount next + 1
  | _, _, .reveal _ _ _ _ _ _ next => instructionCount next + 1

namespace ProtocolState

def remaining : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Nat
  | _, _, .ret _ => fun _ => 0
  | _, _, .sample _ _ _ next =>
      Sum.elim (fun _ => instructionCount next + 1) (remaining next)
  | _, _, .commit _ _ _ _ next =>
      Sum.elim (fun _ => instructionCount next + 1) (remaining next)
  | _, _, .reveal _ _ _ _ _ _ next =>
      Sum.elim (fun _ => instructionCount next + 1) (remaining next)

@[simp] theorem remaining_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    remaining program (entry program config) = instructionCount program := by
  cases program <;> rfl

theorem remaining_zero_iff_terminal : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    remaining program state = 0 ↔ terminal program state
  | _, _, .ret _, _ => by simp [remaining, terminal]
  | _, _, .sample _ _ _ next, state => by
      cases state with
      | inl config => simp [remaining, terminal]
      | inr rest => exact remaining_zero_iff_terminal next rest
  | _, _, .commit _ _ _ _ next, state => by
      cases state with
      | inl config => simp [remaining, terminal]
      | inr rest => exact remaining_zero_iff_terminal next rest
  | _, _, .reveal _ _ _ _ _ _ next, state => by
      cases state with
      | inl config => simp [remaining, terminal]
      | inr rest => exact remaining_zero_iff_terminal next rest

theorem remaining_step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (before after : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → ¬ terminal program before →
    after ∈ (step program before joint).support →
    remaining program after + 1 = remaining program before
  | _, _, .ret _, _, _, _, running, _ => (running trivial).elim
  | _, _, .sample _ _ _ next, before, after, joint, running, reached => by
      cases before with
      | inl config =>
          simp only [step, Sum.elim_inl, FinDist.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          simp [remaining]
      | inr rest =>
          simp only [step, Sum.elim_inr, FinDist.support_map, Set.mem_image] at reached
          obtain ⟨target, supported, rfl⟩ := reached
          exact remaining_step next rest target joint running supported
  | _, _, .commit _ _ _ _ next, before, after, joint, running, reached => by
      cases before with
      | inl config =>
          simp only [step, Sum.elim_inl, FinDist.mem_support_pure] at reached
          subst after
          simp [remaining]
      | inr rest =>
          simp only [step, Sum.elim_inr, FinDist.support_map, Set.mem_image] at reached
          obtain ⟨target, supported, rfl⟩ := reached
          exact remaining_step next rest target joint running supported
  | _, _, .reveal _ _ _ _ _ _ next, before, after, joint, running, reached => by
      cases before with
      | inl config =>
          simp only [step, Sum.elim_inl, FinDist.mem_support_pure] at reached
          subst after
          simp [remaining]
      | inr rest =>
          simp only [step, Sum.elim_inr, FinDist.support_map, Set.mem_image] at reached
          obtain ⟨target, supported, rfl⟩ := reached
          exact remaining_step next rest target joint running supported

end ProtocolState

theorem protocol_terminates {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) :
    (executionProtocol program admission initial).WellFoundedPlay := by
  apply wellFoundedPlay_of_rank (ProtocolState.remaining program)
  intro before after step
  obtain ⟨joint, legal, reached⟩ := step
  have consumed := ProtocolState.remaining_step program before after joint legal.1 reached
  omega

theorem protocol_history_length {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) :
    ∀ {state} (trace : (executionProtocol program admission initial).Trace state),
      trace.length + ProtocolState.remaining program state = instructionCount program
  | _, .start => by simp [Trace.length, executionProtocol]
  | _, .extend (source := before) (target := after) prior joint legal reached => by
      have earlier := protocol_history_length program admission initial prior
      have consumed := ProtocolState.remaining_step program before after joint legal.1 reached
      simp only [Trace.length]
      omega

theorem protocol_bounded {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) :
    (executionProtocol program admission initial).BoundedHorizon (instructionCount program) := by
  intro state trace enough
  have count := protocol_history_length program admission initial trace
  exact (ProtocolState.remaining_zero_iff_terminal program state).mp (by omega)

end Vegas.SourceProgram
