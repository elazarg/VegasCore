/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventSourceView
import Vegas.Source.ProtocolBehavioralPolicy

/-! # The source action law at every decoded compiled event view -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Compiling a source policy and decoding its action preserves the full raw
source law at the decoded view, at every owned event address. -/
theorem compilePolicyTable_source_law {Field : Type} {layout : Field → EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, FieldRef layout (outputLayout program event)) (who : Player)
      (policy : BehavioralPolicy who program) (event : Fin (eventCount program))
      (store : Store layout) (past : List (OwnAction Player L))
      (view : ProtocolView who program),
      decodeEventView? program refs outputs who event store past = some view →
      eventOwner? program event = some who →
      (compilePolicyTable program refs outputs who policy event store past).map
          (decodeEventAction program event) =
        policy.protocolAction program view := by
  intro Γ O program
  induction program with
  | ret => intro refs outputs who policy event; exact Fin.elim0 event
  | sample name fresh law next ih =>
      intro refs outputs who policy event store past view decoded acting
      refine Fin.cases ?_ ?_ event decoded acting
      · intro _decoded impossible
        cases impossible
      · intro tail decoded acting
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact ih _ _ who policy tail store past later present acting
  | commit name owner fresh guard next ih =>
      intro refs outputs who policy event store past view decoded acting
      refine Fin.cases ?_ ?_ event decoded acting
      · intro decoded acting
        have own : owner = who := Option.some.inj acting
        subst owner
        obtain ⟨observation, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        simp only [compilePolicyTable, Fin.cases_zero, present,
          decodeEventAction, BehavioralPolicy.protocolAction, Sum.elim_inl, ↓reduceDIte]
        rfl
      · intro tail decoded acting
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact ih _ _ who policy.2 tail store past later present acting
  | reveal published owner name fresh source unresolved next ih =>
      intro refs outputs who policy event store past view decoded acting
      refine Fin.cases ?_ ?_ event decoded acting
      · intro decoded acting
        have own : owner = who := Option.some.inj acting
        subst owner
        obtain ⟨observation, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        simp only [compilePolicyTable, Fin.cases_zero, present,
          decodeEventAction, BehavioralPolicy.protocolAction, Sum.elim_inl, ↓reduceDIte]
        rfl
      · intro tail decoded acting
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact ih _ _ who policy.2 tail store past later present acting

/-- The assembled graph policy has the original source protocol action law,
with the actual dependent graph own-action history decoded in full. -/
theorem compileEventPolicy_source_law {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (who : Player) (policy : BehavioralPolicy who program)
    (event : (toEventGraph program).EventId)
    (actor : (toEventGraph program).actor? event = some who)
    (observation : (toEventGraph program).PlayerObservation who)
    (view : ProtocolView who program)
    (decoded : decodeEventView? program (ContextRefs.initial Γ (outputLayout program))
      (outputRef program) who event observation.store
        (decodeCompletions program observation.ownActions) = some view) :
    ((compileEventPolicy program who policy) event actor observation).map
        (decodeEventAction program event) = policy.protocolAction program view := by
  exact compilePolicyTable_source_law program _ _ who policy event observation.store
    (decodeCompletions program observation.ownActions) view decoded
      ((eventOwner?_eq_actor program event).trans actor)

end Vegas
