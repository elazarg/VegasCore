/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphSuffix
import Vegas.Pending.RuntimePhase
import Vegas.EventGraph.Sequential
import Vegas.Source.CommitRecoveryPoint

/-! # Source control at an installed compiled commitment interval -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- An installed binding interval starts at a genuine source commitment.
The fact follows from the actual compiler output layout and phase bounds. -/
theorem CompiledSuffix.atCommit_of_bindingPhase
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)
    (program : SourceProgram Player L Γ O) (refs : ContextRefs (graphLayout whole) Γ)
    (revelations : Revelations Γ) (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (before : ContextRefsBefore refs embedding) (offset : Nat)
    (compiled : CompiledSuffix whole program refs revelations registry embedding before offset)
    (phase : RuntimePhase ((toEventGraph whole).withMode mode))
    (kind : phase.kind = .commitment) (low : phase.low = offset)
    (source : SourceProgram.Config Player L Γ) :
    ProtocolState.atCommit program (ProtocolState.entry program source) = true := by
  have total := compiled.countEq
  have phaseBound := phase.bounded
  change phase.high ≤ eventCount whole at phaseBound
  have nonempty := phase.nonempty
  have positive : 0 < eventCount program := by omega
  let first : Fin (eventCount program) := ⟨0, positive⟩
  have fields := phase.fields (embedding.event first)
    (by rw [compiled.rankEq, low]; exact Nat.le_add_right _ _)
    (by rw [compiled.rankEq]; dsimp only [first]; omega)
  rw [kind] at fields
  obtain ⟨owner, payload, binding⟩ := fields
  change outputLayout whole (embedding.event first) = .binding owner payload at binding
  have sourceBinding := (embedding.layout_eq first).symm.trans binding
  cases program with
  | ret => simp only [eventCount] at positive; omega
  | sample =>
      simp only [first, outputLayout, Fin.mk_zero, Fin.cases_zero] at sourceBinding
      cases sourceBinding
  | commit => rfl
  | reveal =>
      simp only [first, outputLayout, Fin.mk_zero, Fin.cases_zero] at sourceBinding
      cases sourceBinding

end Vegas
