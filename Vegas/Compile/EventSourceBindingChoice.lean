/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventSourceView

/-! # Every typed binding result at its decoded source address -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The full source interface admits every typed result of the addressed
compiled binding. Its exact source action and original address are retained. -/
theorem decodeEventView?_binding_choice {Field : Type} {layout : Field → EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, FieldRef layout (outputLayout program event)) (who : Player)
      (event : Fin (eventCount program)) (store : Store layout) (past : List (OwnAction Player L))
      (view : ProtocolView who program),
      decodeEventView? program refs outputs who event store past = some view →
      ∀ (owner : Player) (payload : L.Ty)
        (binding : outputLayout program event = .binding owner payload)
        (result : PublicationResult (L.Val payload)),
        ∃ action,
          decodeEventAction program event (cast (congrArg EventField.Action binding.symm) result) =
            some action ∧
          action ∈ ProtocolView.available who program (CommitmentInterface.forfeiture program)
            view := by
  intro Γ O program
  induction program with
  | ret => intro refs outputs who event; exact Fin.elim0 event
  | sample name fresh law next ih =>
      intro refs outputs who event store past view decoded owner payload binding result
      refine Fin.cases ?_ ?_ event decoded binding result
      · intro _decoded impossible
        cases impossible
      · intro tail decoded binding result
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact ih _ _ who tail store past later present owner payload binding result
  | commit name actor fresh guard next ih =>
      intro refs outputs who event store past view decoded owner payload binding result
      refine Fin.cases ?_ ?_ event decoded binding result
      · intro decoded binding result
        obtain ⟨observation, _present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        change EventField.binding actor _ = EventField.binding owner payload at binding
        cases binding
        refine ⟨.commit actor name _ result, rfl, result, ?_, rfl⟩
        cases result <;> trivial
      · intro tail decoded binding result
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact ih _ _ who tail store past later present owner payload binding result
  | reveal published actor name fresh source unresolved next ih =>
      intro refs outputs who event store past view decoded owner payload binding result
      refine Fin.cases ?_ ?_ event decoded binding result
      · intro _decoded impossible
        cases impossible
      · intro tail decoded binding result
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact ih _ _ who tail store past later present owner payload binding result

end Vegas
