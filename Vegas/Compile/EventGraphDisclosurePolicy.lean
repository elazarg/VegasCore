/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphCanonicalContinuation
import Vegas.Source.DisclosureOpening
import Vegas.EventGraph.RevealRelaxedScheduling

/-! # Disclosure policies compiled across graph execution modes

The source disclosure condition makes every publication decision kernel constant,
including incomplete graph observations. The actual transported compiled profile
therefore satisfies ready independence in every existing execution mode.
-/

noncomputable section
namespace Vegas
open SourceProgram EventGraph
variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

theorem compilePolicyTable_disclosing_publication {Field : Type}
    {layout : Field → EventField Player L} :
    {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) →
    (refs : ContextRefs layout Γ) →
    (outputs : ∀ event, FieldRef layout (outputLayout program event)) →
    (who : Player) → (policy : BehavioralPolicy who program) → Disclosing program policy →
    (event : Fin (eventCount program)) → (outputLayout program event).IsPublication →
    ∀ left right leftHistory rightHistory,
      compilePolicyTable program refs outputs who policy event left leftHistory =
      compilePolicyTable program refs outputs who policy event right rightHistory := by
  intro Γ names program
  induction program with
  | ret => intro refs outputs who policy disclosing event; exact nomatch event
  | sample name fresh law next ih =>
      intro refs outputs who policy disclosing event
      refine Fin.cases ?_ (fun tail => ?_) event
      · simp [outputLayout, EventField.IsPublication]
      · exact ih _ _ who policy disclosing tail
  | commit name owner fresh guard next ih =>
      intro refs outputs who policy disclosing event
      refine Fin.cases ?_ (fun tail => ?_) event
      · simp [outputLayout, EventField.IsPublication]
      · exact ih _ _ who policy.2 disclosing tail
  | reveal published owner name fresh selected unresolved next ih =>
      intro refs outputs who policy disclosing event
      refine Fin.cases ?_ (fun tail => ?_) event
      · intro publication left right leftHistory rightHistory
        change (if same : owner = who then
          match decodeObservation? who refs left with
          | some view => policy.1 same (view, leftHistory)
          | none => PMF.pure true
          else PMF.pure false) =
          (if same : owner = who then
          match decodeObservation? who refs right with
          | some view => policy.1 same (view, rightHistory)
          | none => PMF.pure true
          else PMF.pure false)
        by_cases same : owner = who
        · simp only [dite_eq_left same]
          have kernel (view) := eq_pure_true_of_false_not_mem (disclosing.1 same view)
          cases decodeObservation? who refs left <;>
            cases decodeObservation? who refs right <;> simp [kernel]
        · simp only [dite_eq_right same]
      · exact ih _ _ who policy.2 disclosing.2 tail
theorem compileEventProfile_disclosing_oblivious {Γ : SourceCtx Player L}
    {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (profile : BehavioralProfile program) (disclosing : ∀ who, Disclosing program (profile who)) :
    (toEventGraph program).ObliviousAtPublications (compileEventProfile program profile) := by
  intro who event actor publication left right
  exact compilePolicyTable_disclosing_publication program _ _ who (profile who)
    (disclosing who) event publication left.store right.store
      (decodeCompletions program left.ownActions) (decodeCompletions program right.ownActions)

theorem compileEventProfile_mode_disclosing_oblivious {Γ : SourceCtx Player L}
    {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (profile : BehavioralProfile program) (disclosing : ∀ who, Disclosing program (profile who))
    (mode : ExecutionMode) :
    ((toEventGraph program).withMode mode).ObliviousAtPublications
      ((toEventGraph program).toModeProfile mode (compileEventProfile program profile)) := by
  intro who event actor publication left right
  exact compileEventProfile_disclosing_oblivious program profile disclosing
    who event actor publication _ _
theorem compileEventProfile_mode_disclosing_readyIndependent {Γ : SourceCtx Player L}
    {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (profile : BehavioralProfile program) (disclosing : ∀ who, Disclosing program (profile who))
    (mode : ExecutionMode) :
    ((toEventGraph program).withMode mode).ReadyIndependent
      ((toEventGraph program).toModeProfile mode (compileEventProfile program profile)) :=
  ((toEventGraph program).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered program) mode).readyIndependent
      (compileEventProfile_mode_disclosing_oblivious program profile disclosing mode)
/-- Every public scheduling order preserves the complete original source state
for a genuinely disclosing profile, in every existing dependency mode. -/
theorem runPolicies_mode_disclosing_source_decode {Γ : SourceCtx Player L}
    {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (profile : BehavioralProfile program) (disclosing : ∀ who, Disclosing program (profile who))
    (mode : ExecutionMode) (scheduler : ((toEventGraph program).withMode mode).PublicScheduler)
    (initial : State L Γ) :
    (((toEventGraph program).withMode mode).runPolicies scheduler
      (((toEventGraph program).withMode mode).normalizeProfile
        ((toEventGraph program).toModeProfile mode (compileEventProfile program profile)))
          (encodeInputs initial)).map (fun config => decodeState? (terminalRefs program)
            config.store) = (SourceProgram.run program profile initial).map some := by
  have ordered := (toEventGraph program).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered program) mode
  have same := ordered.runPolicies_store_eq_canonical
    ((toEventGraph program).toModeProfile mode (compileEventProfile program profile))
    (compileEventProfile_mode_disclosing_oblivious program profile disclosing mode)
    scheduler (encodeInputs initial)
  have source := canonicalContinuation_mode_source_decode program profile mode initial
  rw [EventGraph.canonicalContinuation_initial, PMF.map_comp] at source
  change (((toEventGraph program).withMode mode).runPolicies _ _ _).map
    ((decodeState? (terminalRefs program)) ∘ Config.store) = _
  rw [← PMF.map_comp, same, PMF.map_comp]
  simpa only [PMF.map_comp, Function.comp_def, EventGraph.semanticKey,
    EventGraph.storeRecall] using source
/-- Initialized ideal execution preserves the original initial draw jointly
with the complete final source state, including private fields. -/
theorem runPolicies_mode_disclosing_joint_source_law
    (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program)
    (disclosing : ∀ who, Disclosing setup.program (profile who))
    (mode : ExecutionMode) (scheduler : (setup.eventGraph.withMode mode).PublicScheduler) :
    setup.initialLaw.bind (fun initial =>
      ((setup.eventGraph.withMode mode).runPolicies scheduler
        ((setup.eventGraph.withMode mode).normalizeProfile
          (setup.eventGraph.toModeProfile mode (compileEventProfile setup.program profile)))
            (setup.eventInputs initial)).map (fun config =>
              (initial, decodeState? (terminalRefs setup.program) config.store))) =
    setup.initialLaw.bind (fun initial =>
      (SourceProgram.run setup.program profile initial).map
        (fun final => (initial, some final))) := by
  apply GameTheory.Math.Probability.bind_congr_on_support _
  intro initial _
  have decoded := runPolicies_mode_disclosing_source_decode setup.program profile
    disclosing mode scheduler initial
  have joint := congrArg (fun law => law.map (fun final => (initial, final))) decoded
  simpa only [PMF.map_comp, Function.comp_def, Setup.eventGraph, Setup.eventInputs] using joint
end Vegas
