/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRevealTail
import Vegas.Source.ProtocolSuffix
import Vegas.Source.CommitRecoveryPoint
import Vegas.Compile.EventGraphSuffix
import Vegas.Pending.RuntimePhase

/-! # Noncommitment instructions in actual source suffix rank windows -/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem suffix_control_of_remaining
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) :
    ∀ point : ProtocolState whole,
      ProtocolState.remaining whole point ≤ instructionCount program →
      ∃ localPoint : ProtocolState program,
        ProtocolState.remaining program localPoint = ProtocolState.remaining whole point ∧
          ProtocolState.atCommit program localPoint = ProtocolState.atCommit whole point := by
  induction origin with
  | initial => intro point _; exact ⟨point, rfl, rfl⟩
  | sampleTail fresh law next _origin ih =>
      intro point bound
      obtain ⟨localPoint, rank, control⟩ := ih point
        (bound.trans (by change instructionCount next ≤ instructionCount next + 1; omega))
      cases localPoint with
      | inl config =>
          change instructionCount next + 1 = ProtocolState.remaining _ point at rank
          omega
      | inr localPoint => exact ⟨localPoint, rank, control⟩
  | commitTail fresh guard next _origin ih =>
      intro point bound
      obtain ⟨localPoint, rank, control⟩ := ih point
        (bound.trans (by change instructionCount next ≤ instructionCount next + 1; omega))
      cases localPoint with
      | inl config =>
          change instructionCount next + 1 = ProtocolState.remaining _ point at rank
          omega
      | inr localPoint => exact ⟨localPoint, rank, control⟩
  | revealTail fresh selected unresolved next _origin ih =>
      intro point bound
      obtain ⟨localPoint, rank, control⟩ := ih point
        (bound.trans (by change instructionCount next ≤ instructionCount next + 1; omega))
      cases localPoint with
      | inl config =>
          change instructionCount next + 1 = ProtocolState.remaining _ point at rank
          omega
      | inr localPoint => exact ⟨localPoint, rank, control⟩

private theorem reveal_prefix_noncommit (count : Nat) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O),
      RevealPrefix program count → ∀ point : ProtocolState program,
      instructionCount program - count < ProtocolState.remaining program point →
      ProtocolState.atCommit program point = false := by
  induction count with
  | zero =>
      intro Γ O program _ point lower
      have bound := ProtocolState.remaining_le_instructionCount program point
      omega
  | succ count ih =>
      intro Γ O program prefixed point lower
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal published owner name fresh selected unresolved next =>
          cases point with
          | inl config => rfl
          | inr point =>
              apply ih next prefixed point
              change instructionCount next + 1 - (count + 1) <
                ProtocolState.remaining next point at lower
              omega

namespace SourceProgram

/-- Every original source point strictly inside a genuine disclosure suffix
window is noncommitment, regardless of its private state or exclusions. -/
theorem ProtocolSuffix.noncommit_of_reveal_window
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (count : Nat)
    (prefixed : RevealPrefix program count) (point : ProtocolState whole)
    (lower : instructionCount program - count < ProtocolState.remaining whole point)
    (upper : ProtocolState.remaining whole point ≤ instructionCount program) :
    ProtocolState.atCommit whole point = false := by
  obtain ⟨localPoint, rank, control⟩ := suffix_control_of_remaining origin point upper
  rw [← control]
  exact reveal_prefix_noncommit count program prefixed localPoint (rank ▸ lower)

/-- The original rank of a genuine sample suffix names its sampling instruction,
so an intermediate state at that rank cannot trigger commitment recovery. -/
theorem ProtocolSuffix.noncommit_of_sample_rank
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    {lift : ProtocolState (.sample name fresh law next) → ProtocolState whole}
    (origin : ProtocolSuffix whole (.sample name fresh law next) lift)
    (point : ProtocolState whole)
    (rank : ProtocolState.remaining whole point =
      instructionCount (.sample name fresh law next)) :
    ProtocolState.atCommit whole point = false := by
  obtain ⟨localPoint, remaining, control⟩ := suffix_control_of_remaining origin point rank.le
  rw [← control]
  cases localPoint with
  | inl config => rfl
  | inr localPoint =>
      have bound := ProtocolState.remaining_le_instructionCount next localPoint
      change ProtocolState.remaining next localPoint = ProtocolState.remaining whole point
        at remaining
      change ProtocolState.remaining whole point = instructionCount next + 1 at rank
      omega

end SourceProgram

/-- A compiled singleton sampling phase identifies the source instruction at
its actual rank, without assuming the source suffix has sampling syntax. -/
theorem CompiledSuffix.noncommit_of_sample_phase
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO) (mode : EventGraph.ExecutionMode)
    (program : SourceProgram Player L Γ O)
    (refs : ContextRefs (graphLayout whole) Γ) (revelations : Revelations Γ)
    (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (before : ContextRefsBefore refs embedding) (offset : Nat)
    (compiled : CompiledSuffix whole program refs revelations registry embedding before offset)
    (phase : EventGraphRuntime.RuntimePhase ((toEventGraph whole).withMode mode))
    (kind : phase.kind = .sample) (low : phase.low = offset)
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (point : ProtocolState whole)
    (rank : ProtocolState.remaining whole point = instructionCount program) :
    ProtocolState.atCommit whole point = false := by
  have bounded := phase.bounded
  have total := compiled.countEq
  have positive : 0 < eventCount program := by
    change phase.high ≤ eventCount whole at bounded
    have nonempty := phase.nonempty
    omega
  let zero : Fin (eventCount program) := ⟨0, positive⟩
  have ranked : (embedding.event zero).val = phase.low := by
    rw [compiled.rankEq]
    dsimp only [zero]
    omega
  have headSample : EventGraphRuntime.RuntimePhaseKind.sample.Matches
      (outputLayout program zero) := by
    have typed := phase.fields (embedding.event zero) (by omega)
      (by have nonempty := phase.nonempty; omega)
    rw [kind] at typed
    change EventGraphRuntime.RuntimePhaseKind.sample.Matches
      (outputLayout whole (embedding.event zero)) at typed
    rw [embedding.layout_eq] at typed
    exact typed
  cases program with
  | ret payoffs => simp only [eventCount] at positive; omega
  | commit name owner fresh guard next =>
      obtain ⟨payload, impossible⟩ := headSample
      cases impossible
  | reveal published owner name fresh selected unresolved next =>
      obtain ⟨payload, impossible⟩ := headSample
      cases impossible
  | sample name fresh law next =>
      exact SourceProgram.ProtocolSuffix.noncommit_of_sample_rank fresh law next origin point rank

end Vegas
