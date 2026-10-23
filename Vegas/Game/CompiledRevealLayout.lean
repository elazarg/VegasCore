/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRevealTail
import Vegas.Pending.RuntimePhase

/-! # Source reveal prefixes determined by actual compiled phase intervals -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A bounded initial interval of publication outputs consists of source
reveal instructions; this follows from the actual syntax and output layout. -/
theorem RevealPrefix.of_outputLayout : ∀ (count : Nat) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O),
    count ≤ eventCount program →
    (∀ index : Fin (eventCount program), index.val < count →
      (outputLayout program index).IsPublication) → RevealPrefix program count := by
  intro count
  induction count with
  | zero =>
      intro Γ O program _bounded _publications
      cases program <;> exact True.intro
  | succ count ih =>
      intro Γ O program bounded publications
      cases program with
      | ret _ => simp only [eventCount] at bounded; omega
      | sample name fresh law next =>
          have impossible := publications ⟨0, by simp only [eventCount]; omega⟩
            (by change 0 < count + 1; omega)
          exact impossible.elim
      | commit name owner fresh guard next =>
          have impossible := publications ⟨0, by simp only [eventCount]; omega⟩
            (by change 0 < count + 1; omega)
          exact impossible.elim
      | reveal published owner name fresh source unresolved next =>
          apply ih next (by simp only [eventCount] at bounded; omega)
          intro index inside
          exact publications (Fin.succ index) (by simp only [Fin.val_succ]; omega)

/-- The installed compiled publication interval supplies its source reveal
prefix, with no syntactic-phase correspondence hypothesis. -/
theorem CompiledSuffix.revealPrefix_of_phase
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO) (mode : EventGraph.ExecutionMode)
    (program : SourceProgram Player L Γ O)
    (refs : ContextRefs (graphLayout whole) Γ) (revelations : Revelations Γ)
    (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (before : ContextRefsBefore refs embedding) (offset : Nat)
    (compiled : CompiledSuffix whole program refs revelations registry embedding before offset)
    (phase : RuntimePhase ((toEventGraph whole).withMode mode))
    (kind : phase.kind = .reveal) (low : phase.low = offset) (count : Nat)
    (high : phase.high = offset + count) : RevealPrefix program count := by
  have bounded := phase.bounded
  have total := compiled.countEq
  have countBound : count ≤ eventCount program := by
    change phase.high ≤ eventCount whole at bounded
    rw [high] at bounded
    omega
  apply RevealPrefix.of_outputLayout count program countBound
  intro index inside
  have fields := phase.fields (embedding.event index)
    (by rw [compiled.rankEq, low]; omega) (by rw [compiled.rankEq, high]; omega)
  rw [kind] at fields
  obtain ⟨payload, publication⟩ := fields
  change outputLayout whole (embedding.event index) = .publication payload at publication
  rw [embedding.layout_eq] at publication
  rw [publication]
  trivial

end Vegas
