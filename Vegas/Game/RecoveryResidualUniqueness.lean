/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoverySurvivingBindingSource
import Vegas.Source.CommitAttemptRanks

/-! # Unique actual source suffixes at a fixed physical phase address -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Two actual traversals of the same linear source syntax with the same
remaining length have the same entire residual carrier and state lift. -/
theorem SourceProgram.ProtocolSuffix.residual_eq_of_instructionCount
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (first : ProtocolSuffix whole program lift) :
    ∀ {Δ : SourceCtx Player L} {P : Finset VarId}
      (tail : SourceProgram Player L Δ P) (otherLift : ProtocolState tail → ProtocolState whole),
      ProtocolSuffix whole tail otherLift → instructionCount program = instructionCount tail →
      (⟨Γ, O, program, lift⟩ : ResidualProgram whole) = ⟨Δ, P, tail, otherLift⟩ := by
  induction first with
  | initial =>
      intro Δ P tail otherLift second same
      cases second with
      | initial => rfl
      | sampleTail otherFresh otherLaw otherNext otherPrevious =>
          have bounded := otherPrevious.instructionCount_le
          simp only [instructionCount] at bounded
          omega
      | commitTail otherFresh otherGuard otherNext otherPrevious =>
          have bounded := otherPrevious.instructionCount_le
          simp only [instructionCount] at bounded
          omega
      | revealTail otherFresh otherSelected otherUnresolved otherNext otherPrevious =>
          have bounded := otherPrevious.instructionCount_le
          simp only [instructionCount] at bounded
          omega
  | sampleTail fresh law next previous ih =>
      intro Δ P tail otherLift second same
      cases second with
      | initial =>
          have bounded := previous.instructionCount_le
          simp only [instructionCount] at bounded
          omega
      | sampleTail otherFresh otherLaw otherNext otherPrevious =>
          have parents := ih _ _ otherPrevious (by simp only [instructionCount]; omega)
          cases parents
          rfl
      | commitTail otherFresh otherGuard otherNext otherPrevious =>
          have parents := ih _ _ otherPrevious (by simp only [instructionCount]; omega)
          cases parents
      | revealTail otherFresh otherSelected otherUnresolved otherNext otherPrevious =>
          have parents := ih _ _ otherPrevious (by simp only [instructionCount]; omega)
          cases parents
  | commitTail fresh guard next previous ih =>
      intro Δ P tail otherLift second same
      cases second with
      | initial =>
          have bounded := previous.instructionCount_le
          simp only [instructionCount] at bounded
          omega
      | sampleTail otherFresh otherLaw otherNext otherPrevious =>
          have parents := ih _ _ otherPrevious (by simp only [instructionCount]; omega)
          cases parents
      | commitTail otherFresh otherGuard otherNext otherPrevious =>
          have parents := ih _ _ otherPrevious (by simp only [instructionCount]; omega)
          cases parents
          rfl
      | revealTail otherFresh otherSelected otherUnresolved otherNext otherPrevious =>
          have parents := ih _ _ otherPrevious (by simp only [instructionCount]; omega)
          cases parents
  | revealTail fresh selected unresolved next previous ih =>
      intro Δ P tail otherLift second same
      cases second with
      | initial =>
          have bounded := previous.instructionCount_le
          simp only [instructionCount] at bounded
          omega
      | sampleTail otherFresh otherLaw otherNext otherPrevious =>
          have parents := ih _ _ otherPrevious (by simp only [instructionCount]; omega)
          cases parents
      | commitTail otherFresh otherGuard otherNext otherPrevious =>
          have parents := ih _ _ otherPrevious (by simp only [instructionCount]; omega)
          cases parents
      | revealTail otherFresh otherSelected otherUnresolved otherNext otherPrevious =>
          have parents := ih _ _ otherPrevious (by simp only [instructionCount]; omega)
          cases parents
          rfl

/-- Chosen checkpoints at the same real attempt address use the same typed
residual syntax and exact whole-source lift, independently of private values. -/
theorem RecoverySourceCheckpoint.residual_eq_of_phase_eq
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {first second : PhaseRuntimeState (serviceGraph setup mode)}
    (left : RecoverySourceCheckpoint setup mode first)
    (right : RecoverySourceCheckpoint setup mode second)
    (same : first.attempt.phase = second.attempt.phase) : left.residual = right.residual := by
  apply left.origin.residual_eq_of_instructionCount right.residual.tail right.residual.lift
    right.origin
  have leftRank := left.saved_position
  have rightRank := right.saved_position
  rw [left.remaining, ProtocolState.remaining_entry] at leftRank
  rw [right.remaining, ProtocolState.remaining_entry] at rightRank
  have leftBound := left.origin.instructionCount_le
  have rightBound := right.origin.instructionCount_le
  omega

private theorem embedding_eq_of_event_eq
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    (first second : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (same : first.event = second.event) : first = second := by
  cases first
  cases second
  cases same
  rfl

private theorem residual_cast_ranked
    {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {first second : ResidualProgram whole}
    (same : first = second)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) first.tail)
    (offset : Nat) (ranked : ∀ index, (embedding.event index).val = offset + index.val) :
    ∀ index, ((cast (congrArg (fun residual : ResidualProgram whole =>
      OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) residual.tail) same)
        embedding).event index).val = offset + index.val := by
  cases same
  exact ranked

/-- After the derived typed residual identification, actual checkpoint output
embeddings agree in full: their event addresses are fixed by the same phase rank. -/
theorem RecoverySourceCheckpoint.embedding_eq_of_phase_eq
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {first second : PhaseRuntimeState (serviceGraph setup mode)}
    (left : RecoverySourceCheckpoint setup mode first)
    (right : RecoverySourceCheckpoint setup mode second)
    (same : first.attempt.phase = second.attempt.phase) :
    cast (congrArg (fun residual : ResidualProgram setup.program =>
      OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) residual.tail)
        (left.residual_eq_of_phase_eq right same)) left.embedding = right.embedding := by
  apply embedding_eq_of_event_eq
  funext index
  apply Fin.ext
  rw [residual_cast_ranked (left.residual_eq_of_phase_eq right same) left.embedding
    first.attempt.phase left.compiled.rankEq, right.compiled.rankEq, same]

end Vegas
