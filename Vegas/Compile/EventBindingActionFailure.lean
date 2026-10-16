/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventSourceView

/-! # Failure reflection for typed compiled binding actions -/

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- At a binding address the physical typed failure is exactly the failed
source declaration, including its original owner, source name and payload. -/
theorem decodeEventAction_binding_failure_iff :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (event : Fin (eventCount program))
      (owner : Player) (payload : L.Ty)
      (binding : outputLayout program event = .binding owner payload)
      (choice : EventField.Action (outputLayout program event)) (action : OwnAction Player L),
      decodeEventAction program event choice = some action →
        (cast (congrArg EventField.Action binding) choice = .failure ↔ action.IsFailure) := by
  intro Γ O program
  induction program with
  | ret => intro event; exact Fin.elim0 event
  | sample name fresh law next ih =>
      intro event owner payload binding choice action decoded
      refine Fin.cases ?_ ?_ event binding choice decoded
      · intro impossible; cases impossible
      · intro tail binding choice decoded
        exact ih tail owner payload binding choice action decoded
  | commit name actor fresh guard next ih =>
      intro event owner payload binding choice action decoded
      refine Fin.cases ?_ ?_ event binding choice decoded
      · intro binding choice decoded
        change EventField.binding actor _ = .binding owner payload at binding
        cases binding
        cases decoded
        rfl
      · intro tail binding choice decoded
        exact ih tail owner payload binding choice action decoded
  | reveal published actor name fresh selected unresolved next ih =>
      intro event owner payload binding choice action decoded
      refine Fin.cases ?_ ?_ event binding choice decoded
      · intro impossible; cases impossible
      · intro tail binding choice decoded
        exact ih tail owner payload binding choice action decoded

end Vegas
