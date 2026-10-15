/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPhase
import Vegas.Compile.EventGraphLayout
import Vegas.EventGraph.Information

/-! # Layout of typed source commitment blocks -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- Prepending a commitment telescope adds precisely its executable slots. -/
theorem eventCount_prepend (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) :
    block.length + eventCount (suffix) = eventCount (block.prepend suffix) := by
  induction block with
  | nil => simp only [length, prepend, Nat.zero_add]
  | commit name owner fresh guard rest ih =>
      have counted := ih suffix
      simp only [length, prepend, eventCount]
      omega

/-- Every source slot before the block end is a binding by one of its owners. -/
theorem binding_before_length (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) :
    ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      ∃ owner payload, owner ∈ block.owners ∧
        outputLayout (block.prepend suffix) index = .binding owner payload := by
  induction block with
  | nil => intro index inside; simp only [length] at inside; omega
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro index
      refine Fin.cases ?_ ?_ index
      · intro _inside
        exact ⟨owner, payload, Finset.mem_insert_self _ _, rfl⟩
      · intro later inside
        obtain ⟨other, otherPayload, member, layout⟩ := ih suffix later (by
          change later.val + 1 < rest.length + 1 at inside
          omega)
        exact ⟨other, otherPayload, Finset.mem_insert_of_mem member, layout⟩

/-- Each block owner occurs at an actual binding slot of the compiled prefix. -/
theorem owner_iff_binding (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (who : Player) :
    who ∈ block.owners ↔
      ∃ index : Fin (eventCount (block.prepend suffix)), index.val < block.length ∧
        ∃ payload, outputLayout (block.prepend suffix) index = .binding who payload := by
  constructor
  · induction block with
    | nil => intro member; exact (Finset.notMem_empty _ member).elim
    | @commit Γ O Δ P name owner payload fresh guard rest ih =>
        intro member
        rcases Finset.mem_insert.mp member with same | later
        · subst who
          exact ⟨⟨0, by simp only [prepend, eventCount]; omega⟩,
            by simp only [length]; omega, payload, rfl⟩
        · obtain ⟨index, inside, value, layout⟩ := ih suffix later
          exact ⟨Fin.succ index, by change index.val + 1 < rest.length + 1; omega,
            value, layout⟩
  · rintro ⟨index, inside, payload, layout⟩
    obtain ⟨other, otherPayload, member, actual⟩ := block.binding_before_length suffix index inside
    have same := actual.symm.trans layout
    cases same
    exact member

/-- A maximal commitment telescope is followed only by public source output. -/
theorem public_at_length (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (boundary : IsCommitBoundary suffix) :
    ∀ index : Fin (eventCount (block.prepend suffix)), index.val = block.length →
      (outputLayout (block.prepend suffix) index).IsPublic := by
  induction block with
  | nil =>
      intro index atEnd
      cases suffix with
      | ret payoffs => exact Fin.elim0 index
      | sample name fresh law next =>
          have zero : index = ⟨0, by simp only [prepend, eventCount]; omega⟩ := Fin.ext atEnd
          rw [zero]
          trivial
      | commit name owner fresh guard next => exact boundary.elim
      | reveal published owner name fresh source unresolved next =>
          have zero : index = ⟨0, by simp only [prepend, eventCount]; omega⟩ := Fin.ext atEnd
          rw [zero]
          trivial
  | commit name owner fresh guard rest ih =>
      intro index
      refine Fin.cases ?_ ?_ index
      · intro impossible
        change 0 = rest.length + 1 at impossible
        omega
      · intro later atEnd
        apply ih suffix boundary later
        change later.val + 1 = rest.length + 1 at atEnd
        omega

end Vegas.SourceProgram.CommitPrefix
