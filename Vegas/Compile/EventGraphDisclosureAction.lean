/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphDisclosurePolicy

/-! # Compiled disclosing policies choose the original true publication action -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A disclosing source policy emits TRUE at every owned publication address,
including malformed graph observations where the existing decoder falls back. -/
theorem compilePolicyTable_disclosing_publication_true {Field : Type}
    {layout : Field → EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, FieldRef layout (outputLayout program event)) (who : Player)
      (policy : BehavioralPolicy who program), Disclosing program policy →
      ∀ (event : Fin (eventCount program)) (payload : L.Ty)
        (publication : outputLayout program event = .publication payload),
      eventOwner? program event = some who → ∀ store past,
        (compilePolicyTable program refs outputs who policy event store past).map
            (cast (congrArg EventField.Action publication)) = PMF.pure true := by
  intro Γ O program
  induction program with
  | ret => intro refs outputs who policy disclosing event; exact Fin.elim0 event
  | sample name fresh law next ih =>
      intro refs outputs who policy disclosing event payload
      refine Fin.cases ?_ ?_ event
      · intro publication
        cases publication
      · intro tail publication acting store past
        exact ih _ _ who policy disclosing tail payload publication acting store past
  | commit name owner fresh guard next ih =>
      intro refs outputs who policy disclosing event payload
      refine Fin.cases ?_ ?_ event
      · intro publication
        cases publication
      · intro tail publication acting store past
        exact ih _ _ who policy.2 disclosing tail payload publication acting store past
  | reveal published owner name fresh selected unresolved next ih =>
      intro refs outputs who policy disclosing event payload
      refine Fin.cases ?_ ?_ event
      · intro publication acting store past
        have own : owner = who := Option.some.inj acting
        subst owner
        cases publication
        simp only [compilePolicyTable, Fin.cases_zero, ↓reduceDIte]
        have kernel view := eq_pure_true_of_false_not_mem (disclosing.1 rfl (view, past))
        cases decoded : decodeObservation? who refs store with
        | none => rw [PMF.pure_map]; rfl
        | some view =>
            change (policy.1 rfl (view, past)).map id = PMF.pure true
            rw [PMF.map_id]
            exact kernel view
      · intro tail publication acting store past
        exact ih _ _ who policy.2 disclosing.2 tail payload publication acting store past

/-- The actual assembled graph policy retains the source's original TRUE
action, independently of the full graph observation and completion order. -/
theorem compileEventPolicy_disclosing_publication_true {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (who : Player)
    (policy : BehavioralPolicy who program) (disclosing : Disclosing program policy)
    (event : (toEventGraph program).EventId)
    (actor : (toEventGraph program).actor? event = some who)
    (observation : (toEventGraph program).PlayerObservation who)
    (payload : L.Ty) (publication : outputLayout program event = .publication payload) :
    ((compileEventPolicy program who policy) event actor observation).map
        (cast (congrArg EventField.Action publication)) = PMF.pure true := by
  exact compilePolicyTable_disclosing_publication_true program _ _ who policy disclosing
    event payload publication ((eventOwner?_eq_actor program event).trans actor)
    observation.store (decodeCompletions program observation.ownActions)

end Vegas
