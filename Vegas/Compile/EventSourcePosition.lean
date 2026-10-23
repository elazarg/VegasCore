/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventSourceView
import Vegas.Source.ObservationRecall

/-! # Static source positions of compiled event views -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The syntax decoder's source position is the original compiled event rank,
independently of hidden values, retained actions, or partial-store holes. -/
theorem decodeEventView?_position {Field : Type} {layout : Field → EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, FieldRef layout (outputLayout program event)) (who : Player)
      (event : Fin (eventCount program)) (store : Store layout) (past : List (OwnAction Player L))
      (view : ProtocolView who program),
      decodeEventView? program refs outputs who event store past = some view →
        ProtocolView.position who program view = event.val := by
  intro Γ O program
  induction program with
  | ret => intro refs outputs who event; exact Fin.elim0 event
  | sample name fresh law next ih =>
      intro refs outputs who event store past view decoded
      refine Fin.cases ?_ ?_ event decoded
      · intro decoded
        obtain ⟨observation, _present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        rfl
      · intro tail decoded
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact congrArg Nat.succ (ih _ _ who tail store past later present)
  | commit name owner fresh guard next ih =>
      intro refs outputs who event store past view decoded
      refine Fin.cases ?_ ?_ event decoded
      · intro decoded
        obtain ⟨observation, _present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        rfl
      · intro tail decoded
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact congrArg Nat.succ (ih _ _ who tail store past later present)
  | reveal published owner name fresh selected unresolved next ih =>
      intro refs outputs who event store past view decoded
      refine Fin.cases ?_ ?_ event decoded
      · intro decoded
        obtain ⟨observation, _present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        rfl
      · intro tail decoded
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact congrArg Nat.succ (ih _ _ who tail store past later present)

end Vegas
