/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphStep
import Vegas.Source.RegistryFailureExtension
import Vegas.Compile.EventGraphState
import Vegas.EventGraph.ConfigRestriction
import Vegas.Source.CommitRecoveryStep
import Vegas.Pending.ExclusionPublicRecord

/-! # Reading completed reveals in source order from actual reachable stores -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
theorem publication_failure_iff_read {graph : Vegas.EventGraph Player L}
    (native : EventGraphRuntime.State graph) (event : graph.EventId)
    {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (value : PublicationResult (L.Val payload))
    (stored : (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
      native.config.store = some value) :
    native.PublicFailure event ↔ value = .failure := by
  have viewed := nodeView_eq_resolve outputEq codeEq
  have missed : native.publicView.missedBinding event = false := by
    simp only [PublicView.missedBinding, outputEq]
  simp only [EventGraphRuntime.State.PublicFailure, missed, Bool.false_eq_true, false_or,
    RecoveryState.publicationFailed, viewed]
  change cast (congrArg Option (congrArg EventField.Value outputEq))
    (native.config.outputs event) = some value at stored
  have castSome : ∀ {α β : Type} (same : α = β) (item : α),
      cast (congrArg Option same) (some item) = some (cast same item) := by
    intro α β same item
    cases same
    rfl
  have castNone : ∀ {α β : Type} (same : α = β),
      cast (congrArg Option same) (none : Option α) = (none : Option β) := by
    intro α β same
    cases same
    rfl
  cases output : native.config.outputs event with
  | none =>
      rw [output, castNone (congrArg EventField.Value outputEq)] at stored
      cases stored
  | some result =>
      rw [output, castSome (congrArg EventField.Value outputEq)] at stored
      have same := Option.some.inj stored
      dsimp only
      rw [same]
      cases value <;> simp

private theorem recorded_reveal_value {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {Γ : SourceCtx Player L}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (refs : ContextRefs layout Γ) (sourceConfig : SourceProgram.Config Player L Γ)
    (registry : Registry Γ) (source : HasVar Γ name (.commitment owner payload))
    (store : Store layout) (agree : refs.Agrees sourceConfig.state store)
    (guards : Registry.FailureExtension sourceConfig.registry registry sourceConfig.state)
    (failures : Revelations.PreservesFailures sourceConfig.revelations sourceConfig.state)
    (unique : (Γ.map Prod.fst).Nodup)
    {kind : EventField Player L} (node : EventCode layout kind)
    (outputEq : kind = .publication payload)
    (codeEq : cast (congrArg (EventCode layout) outputEq) node =
      .resolve owner payload (refs.get source)
        (compileChecks (published := published) refs registry sourceConfig.revelations source))
    (action : kind.Action) (law : PMF kind.Value) (value : kind.Value)
    (evaluated : node.eval? action store = some law) (supported : value ∈ law.support) :
    ∃ disclose : Bool,
      cast (congrArg EventField.Action outputEq) action = disclose ∧
      cast (congrArg (fun field => Option field.Value) outputEq) (some value) =
        some ((revealSuccessor published source sourceConfig disclose).state.get .here) := by
  cases outputEq
  simp only [cast_eq] at codeEq
  subst node
  have actual :
      (EventCode.resolve owner payload (refs.get source)
        (compileChecks (published := published) refs registry
          sourceConfig.revelations source)).eval? action store =
        some (PMF.pure
          ((revealSuccessor published source sourceConfig action).state.get .here)) := by
    rw [compileResolve_eval? refs registry sourceConfig.revelations sourceConfig.state store agree
      source action]
    have checks := guards.completedBy_all_eq sourceConfig.revelations failures unique source
      (published := published) action
    dsimp only at checks
    dsimp only [revealSuccessor, Env.cons_get_here]
    rw [checks]
  have same : law = PMF.pure
      ((revealSuccessor published source sourceConfig action).state.get .here) :=
    Option.some.inj (evaluated.symm.trans actual)
  rw [same, PMF.mem_support_pure_iff] at supported
  exact ⟨action, rfl, congrArg some supported⟩

/-- Actual recorded output semantics supplies a source reveal successor and
its extended typed environment. This uses the final reachable store, so earlier
independent reveals need not have completed in numeric source order. -/
theorem completed_reveal_source_successor {graph : Vegas.EventGraph Player L}
    {Γ : SourceCtx Player L} {published name : VarId} {owner : Player} {payload : L.Ty}
    (config : graph.Config) {inputs : graph.Inputs} (reachable : config.Reachable inputs)
    (event : graph.EventId) (completed : event ∈ config.cut.completed)
    (outputEq : graph.outputLayout event = .publication payload)
    (refs : ContextRefs graph.layout Γ) (sourceConfig : SourceProgram.Config Player L Γ)
    (registry : Registry Γ) (source : HasVar Γ name (.commitment owner payload))
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload (refs.get source)
        (compileChecks (published := published) refs registry sourceConfig.revelations source))
    (agree : refs.Agrees sourceConfig.state config.store)
    (guards : Registry.FailureExtension sourceConfig.registry registry sourceConfig.state)
    (failures : Revelations.PreservesFailures sourceConfig.revelations sourceConfig.state)
    (unique : (Γ.map Prod.fst).Nodup) :
    ∃ disclose : Bool, ∃ action : (graph.outputLayout event).Action,
      ⟨event, action⟩ ∈ config.history ∧
      cast (congrArg EventField.Action outputEq) action = disclose ∧
      let after := revealSuccessor published source sourceConfig disclose
      (refs.cons (name := published) (cell := .publication payload)
        ⟨.inr event, outputEq⟩).Agrees after.state config.store ∧
      Registry.FailureExtension after.registry registry.weaken after.state ∧
      Revelations.PreservesFailures after.revelations after.state := by
  obtain ⟨⟨selected, action⟩, recorded, named⟩ :=
    List.mem_map.mp ((config.history_exact event).mpr completed)
  change selected = event at named
  subst selected
  obtain ⟨law, value, stored, evaluated, supported⟩ :=
    reachable.history_output_semantics ⟨event, action⟩ recorded
  obtain ⟨disclose, disclosure, publication⟩ :=
    recorded_reveal_value refs sourceConfig registry source
    config.store agree guards failures unique (graph.nodes event) outputEq codeEq action law
    value
    evaluated supported
  let after := revealSuccessor published source sourceConfig disclose
  refine ⟨disclose, action, recorded, disclosure, ?_, ?_, ?_⟩
  · apply ContextRefs.Agrees.cons refs sourceConfig.state config.store agree
      (name := published) (cell := .publication payload) ⟨.inr event, outputEq⟩
      (after.state.get .here)
    change cast (congrArg (fun field => Option field.Value) outputEq) (config.outputs event) = _
    rw [stored]
    exact publication
  · exact guards.weaken (name := published) (cell := .publication payload) (after.state.get .here)
  · exact Revelations.PreservesFailures.revealSuccessor sourceConfig failures unique source disclose

/-- A recorded reveal gives the actual recovery successor. An already excluded
owner has no effective source action in its retained history; its physical
publication is required to be failed, as ensured by ordered phase exclusion. -/
theorem completed_reveal_recovery_successor {graph : Vegas.EventGraph Player L}
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (source : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (config : graph.Config) {inputs : graph.Inputs} (reachable : config.Reachable inputs)
    (event : graph.EventId) (completed : event ∈ config.cut.completed)
    (outputEq : graph.outputLayout event = .publication payload)
    (refs : ContextRefs graph.layout Γ) (sourceConfig : SourceProgram.Config Player L Γ)
    (registry : Registry Γ) (excluded : Finset Player)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload (refs.get source)
        (compileChecks (published := published) refs registry sourceConfig.revelations source))
    (agree : refs.Agrees sourceConfig.state config.store)
    (guards : Registry.FailureExtension sourceConfig.registry registry sourceConfig.state)
    (failures : Revelations.PreservesFailures sourceConfig.revelations sourceConfig.state)
    (unique : (Γ.map Prod.fst).Nodup)
    (suppressed : owner ∈ excluded →
      (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
        config.store = some .failure) :
    ∃ disclose : Bool, ∃ action : (graph.outputLayout event).Action,
    ∃ after : SourceProgram.Config Player L ((published, .publication payload) :: Γ),
    ∃ nextExcluded : Finset Player,
      ⟨event, action⟩ ∈ config.history ∧
      cast (congrArg EventField.Action outputEq) action = disclose ∧
      ProtocolState.recoveryStep (.reveal published owner name fresh source unresolved next)
          (.inl sourceConfig) excluded
          (Function.update (fun _ => none) owner
            (some ⟨.reveal owner name disclose, false⟩)) =
        PMF.pure (.inr (ProtocolState.entry next after), nextExcluded) ∧
      (refs.cons (name := published) (cell := .publication payload)
        ⟨.inr event, outputEq⟩).Agrees after.state config.store ∧
      Registry.FailureExtension after.registry registry.weaken after.state ∧
      Revelations.PreservesFailures after.revelations after.state ∧
      (@Config.revelations Player L _ after) =
        (Revelations.reveal (published := published) sourceConfig.revelations source :
          Revelations ((published, .publication payload) :: Γ)) ∧
      after.history = (if owner ∈ excluded then sourceConfig.history else
        Function.update sourceConfig.history owner
          (sourceConfig.history owner ++ [.reveal owner name disclose])) ∧
      nextExcluded = (match after.state.get .here with
        | .failure => insert owner excluded
        | .success _ => excluded) := by
  classical
  obtain ⟨disclose, action, recorded, actual, readback, extended, preserved⟩ :=
    completed_reveal_source_successor config reachable event completed outputEq refs sourceConfig
      registry source codeEq agree guards failures unique
  by_cases inactive : owner ∈ excluded
  · let raw := revealSuccessor published source sourceConfig false
    let after := { raw with history := sourceConfig.history }
    have headFailure : raw.state.get .here = PublicationResult.failure := by
      simp only [raw, revealSuccessor, Env.cons_get_here, Bool.false_eq_true,
        ↓reduceIte, ite_self]
    have afterState : after.state = Env.cons (x := published) (τ := .publication payload)
        PublicationResult.failure sourceConfig.state := by
      change Env.cons (raw.state.get .here) sourceConfig.state = _
      rw [headFailure]
    have afterAgree : (refs.cons (name := published) (cell := .publication payload)
        ⟨.inr event, outputEq⟩).Agrees after.state config.store := by
      rw [afterState]
      exact ContextRefs.Agrees.cons refs sourceConfig.state config.store agree
        (name := published) (cell := .publication payload) ⟨.inr event, outputEq⟩
        PublicationResult.failure (suppressed inactive)
    refine ⟨disclose, action, after, insert owner excluded, recorded, actual, ?_,
      afterAgree, ?_, ?_, rfl, ?_, ?_⟩
    · simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive, ↓reduceIte]
      change PMF.pure ((Sum.inr (ProtocolState.entry next after) :
          ProtocolState (.reveal published owner name fresh source unresolved next)),
        match raw.state.get .here with
        | .failure => insert owner excluded
        | .success _ => excluded) = _
      rw [headFailure]
    · change Registry.FailureExtension sourceConfig.registry.weaken registry.weaken after.state
      rw [afterState]
      exact guards.weaken (name := published) (cell := .publication payload)
        PublicationResult.failure
    · exact Revelations.PreservesFailures.revealSuccessor sourceConfig failures unique source false
    · simp only [inactive, ↓reduceIte, after]
    · change insert owner excluded = (match raw.state.get .here with
        | .failure => insert owner excluded
        | .success _ => excluded)
      rw [headFailure]
  · let after := revealSuccessor published source sourceConfig disclose
    let nextExcluded := match after.state.get .here with
      | .failure => insert owner excluded
      | .success _ => excluded
    refine ⟨disclose, action, after, nextExcluded, recorded, actual, ?_,
      readback, extended, preserved, rfl, ?_, rfl⟩
    · simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive, ↓reduceIte,
        Function.update_self, Option.map_some, OwnAction.disclosure]
      rfl
    · simp only [inactive, ↓reduceIte, after, revealSuccessor]

end Vegas
