module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphPolicy
public import Vegas.EventGraph.PublicationDecision
public import Vegas.Source.Disclosure

@[expose] public section

/-! # Disclosing source policies compile to opening kernels

At every active own publication, a disclosing source policy compiles to the
point mass that opens. This holds for arbitrary observations, including those
whose partial source-view decoder fails, and is independent of graph dependencies.
-/

noncomputable section

namespace Vegas

open EventGraph SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A law on booleans that never yields `false` is the point mass at `true`. -/
private theorem pmf_bool_eq_pure_true (law : PMF Bool) (never : false ∉ law.support) :
    law = PMF.pure true := by
  have falseZero : law false = 0 := (PMF.apply_eq_zero_iff law false).mpr never
  have total := law.tsum_coe
  rw [tsum_bool, falseZero, zero_add] at total
  ext choice
  cases choice
  · simp [falseZero]
  · simp [total]

/-- A disclosing policy's compiled table opens at every active own publication. -/
theorem compilePolicyTable_publication {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, Vegas.EventGraph.FieldRef layout (outputLayout program event))
      (who : Player) (policy : BehavioralPolicy who program)
      (_disclosing : Disclosing program policy)
      (event : Fin (eventCount program))
      (publication : (outputLayout program event).IsPublication)
      (_owned : eventOwner? program event = some who) (store : Vegas.EventGraph.Store layout)
      (defaults : DefaultHistory Player) (history : List (OwnAction Player L))
      (_active : who ∉ defaults.defaulted),
      compilePolicyTable program refs outputs who policy event store defaults history =
        PMF.pure (EventField.openAction _ publication)
  | _, _, .ret _, _, _, _, _, _, event, _, _, _, _, _, _ => nomatch event
  | _, _, .sample _ _ _ next, refs, outputs, who, policy, disclosing, event, publication, owned,
      store, defaults, history, active => by
      cases event using Fin.cases with
      | zero => exact publication.elim
      | succ tail =>
          exact compilePolicyTable_publication next _ _ who policy disclosing tail publication
            owned store defaults history active
  | _, _, .commit _ _ _ _ next, refs, outputs, who, policy, disclosing, event, publication, owned,
      store, defaults, history, active => by
      cases event using Fin.cases with
      | zero => exact publication.elim
      | succ tail =>
          exact compilePolicyTable_publication next _ _ who policy.2 disclosing tail publication
            owned store defaults history active
  | _, _, .reveal _ owner _ _ _ _ next, refs, outputs, who, policy, disclosing, event,
      publication, owned, store, defaults, history, active => by
      cases event using Fin.cases with
      | zero =>
          have same : owner = who := Option.some.inj owned
          cases decoded : decodeObservation? who refs store with
          | some observation =>
              exact (compilePolicyTable_reveal_of_decode refs outputs policy same store defaults
                active history observation decoded).trans
                  (pmf_bool_eq_pure_true _
                    (disclosing.1 same ⟨observation, defaults, history⟩ active))
          | none =>
              exact compilePolicyTable_reveal_of_decode_none refs outputs policy same store defaults
                active history decoded
      | succ tail =>
          exact compilePolicyTable_publication next _ _ who policy.2 disclosing.2 tail
            publication owned store defaults history active

/-- A disclosing source policy compiles to a kernel that opens, as a point mass,
at every active publication of its owner. -/
theorem compileEventPolicy_publication {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (who : Player)
    (policy : BehavioralPolicy who program) (disclosing : Disclosing program policy)
    (event : (toInformationGraph program).EventId)
    (actor : (toInformationGraph program).actor? event = some who)
    (publication : ((toInformationGraph program).outputLayout event).IsPublication)
    (observation : (toInformationGraph program).PlayerObservation who)
    (active : who ∉ observation.defaulted) :
    compileEventPolicy program who policy event actor observation active =
      PMF.pure (EventField.openAction _ publication) :=
  compilePolicyTable_publication program _ _ who policy disclosing event publication
    ((eventOwner?_eq_actor program event).trans actor) _ _ _ active

/-- Forcing source disclosure leaves every compiled nonpublication kernel unchanged. -/
theorem compilePolicyTable_forceDisclose_of_not_publication {Field : Type}
    {layout : Field → EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, FieldRef layout (outputLayout program event)) (who : Player)
      (policy : BehavioralPolicy who program) (event : Fin (eventCount program))
      (_plain : ¬ (outputLayout program event).IsPublication) (store : Store layout)
      (defaults : DefaultHistory Player) (history : List (OwnAction Player L)),
      compilePolicyTable program refs outputs who (policy.forceDisclose program) event store
        defaults history = compilePolicyTable program refs outputs who policy event store defaults
          history
  | _, _, .ret _, _, _, _, _, event, _, _, _, _ => nomatch event
  | _, _, .sample _ _ _ next, refs, outputs, who, policy, event, plain, store, defaults,
      history => by
      cases event using Fin.cases with
      | zero => rfl
      | succ tail =>
          exact compilePolicyTable_forceDisclose_of_not_publication next _ _ who policy tail plain
            store defaults history
  | _, _, .commit _ _ _ _ next, refs, outputs, who, policy, event, plain, store, defaults,
      history => by
      cases event using Fin.cases with
      | zero => rfl
      | succ tail =>
          exact compilePolicyTable_forceDisclose_of_not_publication next _ _ who policy.2 tail plain
            store defaults history
  | _, _, .reveal _ _ _ _ _ _ next, refs, outputs, who, policy, event, plain, store, defaults,
      history => by
      cases event using Fin.cases with
      | zero => exact (plain trivial).elim
      | succ tail =>
          exact compilePolicyTable_forceDisclose_of_not_publication next _ _ who policy.2 tail plain
            store defaults history

/-- Forcing source disclosure does not change an owned nonpublication callback. -/
theorem compileEventPolicy_forceDisclose_of_not_publication
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (who : Player)
    (policy : BehavioralPolicy who program) (event : (toInformationGraph program).EventId)
    (actor : (toInformationGraph program).actor? event = some who)
    (plain : ¬ ((toInformationGraph program).outputLayout event).IsPublication)
    (observation : (toInformationGraph program).PlayerObservation who)
    (active : who ∉ observation.defaulted) :
    compileEventPolicy program who (policy.forceDisclose program) event actor observation active =
      compileEventPolicy program who policy event actor observation active :=
  compilePolicyTable_forceDisclose_of_not_publication program _ _ who policy event plain _ _ _

end Vegas
