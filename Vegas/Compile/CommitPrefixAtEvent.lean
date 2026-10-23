/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.CommitPhaseLayout

/-! # Typed commitment prefixes selected by an actual compiled binding slot -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A consecutive interval of binding layouts before a selected binding is a
real typed source commitment telescope, with the selected instruction at its end. -/
theorem exists_commitPrefix_at_binding :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (selected : Fin (eventCount program))
      (who : Player) (payload : L.Ty),
      (∀ index : Fin (eventCount program), index.val ≤ selected.val →
        ∃ owner value, outputLayout program index = .binding owner value) →
      outputLayout program selected = .binding who payload →
      ∃ (Δ : SourceCtx Player L) (P : Finset VarId) (name : VarId)
        (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ who name payload)
        (next : SourceProgram Player L ((name, .commitment who payload) :: Δ) (insert name P))
        (earlier : SourceProgram.CommitPrefix Γ O Δ P),
        earlier.length = selected.val ∧
          earlier.prepend (.commit name who fresh guard next) = program := by
  intro Γ O program
  induction program with
  | ret => intro selected; exact Fin.elim0 selected
  | sample name fresh law next _ih =>
      intro selected who payload bindings _layout
      obtain ⟨owner, value, impossible⟩ := bindings ⟨0, by simp [eventCount]⟩ (Nat.zero_le _)
      change EventField.publicData _ = EventField.binding owner value at impossible
      cases impossible
  | commit name owner fresh guard next ih =>
      intro selected who payload
      refine Fin.cases ?_ ?_ selected
      · intro _bindings layout
        change EventField.binding owner _ = EventField.binding who payload at layout
        cases layout
        exact ⟨_, _, name, fresh, guard, next, .nil, rfl, rfl⟩
      · intro later bindings layout
        obtain ⟨Δ, P, nextName, nextFresh, nextGuard, after, earlier, size, reconstruct⟩ :=
          ih later who payload (fun index before => bindings (Fin.succ index)
            (Nat.succ_le_succ before)) layout
        refine ⟨Δ, P, nextName, nextFresh, nextGuard, after,
          .commit name owner fresh guard earlier, ?_, ?_⟩
        · change earlier.length + 1 = later.val + 1
          omega
        · exact congrArg (SourceProgram.commit name owner fresh guard) reconstruct
  | reveal published owner name fresh source unresolved next _ih =>
      intro selected who payload bindings _layout
      obtain ⟨actor, value, impossible⟩ := bindings ⟨0, by simp [eventCount]⟩ (Nat.zero_le _)
      change EventField.publication _ = EventField.binding actor value at impossible
      cases impossible

end Vegas
