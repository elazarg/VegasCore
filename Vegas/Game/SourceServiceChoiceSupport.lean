/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceStep

/-! # Source choice support for the concrete full-source service

The existing message bounds already cover every fresh binding value. They
therefore supply precisely the finite source alphabets needed to complete
unreachable information values. Initial parameters, public samples and
publication payload types are not required to be finite.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem finiteBindingTypes_of_outputs :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (∀ event owner payload, outputLayout program event = .binding owner payload →
      Finite (L.Val payload)) → program.FiniteBindingTypes
  | _, _, .ret _, _ => trivial
  | _, _, .sample _ _ _ next, finite =>
      finiteBindingTypes_of_outputs next (fun event owner payload kind =>
        finite event.succ owner payload kind)
  | _, _, .commit (payload := payload) _ owner _ _ next, finite =>
      ⟨finite ⟨0, by simp [eventCount]⟩ owner payload rfl,
        finiteBindingTypes_of_outputs next (fun event owner payload kind =>
          finite event.succ owner payload kind)⟩
  | _, _, .reveal _ _ _ _ _ _ next, finite =>
      finiteBindingTypes_of_outputs next (fun event owner payload kind =>
        finite event.succ owner payload kind)

/-- The compiler's existing finite binding-value coverage supplies source
choice finiteness without strengthening the source or native game. -/
theorem sourceService_finiteBindingTypes (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} (bounds : MessageBounds (serviceGraph setup mode))
    (covered : bounds.CoversBindingValues) :
    setup.program.FiniteBindingTypes :=
  finiteBindingTypes_of_outputs setup.program (fun event owner payload kind =>
    bounds.finite_binding_values covered event owner payload kind)

end Vegas
