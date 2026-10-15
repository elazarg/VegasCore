/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceInformation
import Vegas.Compile.EventGraphObservationEncoding
import Vegas.Pending.PhaseApplication

/-! # Semantic source decision views at physical phased binding sites

At an owned ready binding, all earlier source cells visible to that owner are
present even if foreign hidden bindings remain pending. This decodes semantic
source choices, not the auxiliary recovery game's complete signal transcript.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)

/-- Source-visible prefix cells are available at every genuine nonpublication
ready cut; no total rank-prefix completion or foreign hidden value is needed. -/
theorem exists_decodeObservation_of_ready
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (before : ContextRefsBefore refs embedding) (index : Fin (eventCount program))
    (config : (serviceGraph setup mode).Config) (who : Player)
    (ready : config.cut.Ready (embedding.event index))
    (acting : (serviceGraph setup mode).actor? (embedding.event index) = some who)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (embedding.event index)).IsPublication) :
    ∃ observation, decodeObservation? who refs
      ((serviceGraph setup mode).playerStore who config.store) = some observation := by
  apply exists_decodeObservation_of_available who refs
  intro name cell source visible
  let ref := refs.get source
  have visibleKind := (cellVisibleTo_iff_fieldVisibleTo who cell).mp visible
  rw [ref.get?_playerStore (graph := serviceGraph setup mode) who config.store visibleKind]
  apply ref.get?_isSome
  cases field : ref.field with
  | inl input => simp only [EventGraph.Config.store, Option.isSome_some]
  | inr prior =>
      have lower : prior.val < (embedding.event index).val := by
        have earlier := before source index
        change FieldBefore (embedding.event index) ref.field at earlier
        rw [field] at earlier
        exact earlier
      have priorVisible : ((serviceGraph setup mode).outputLayout prior).VisibleTo who := by
        have kind := ref.layout_eq
        rw [field] at kind
        change ((graphLayout setup.program) (.inr prior)).VisibleTo who
        rw [kind]
        exact visibleKind
      have completed := ((serviceGraph_revealRelaxedOrdered setup mode).ready_visible_iff
        config.cut ready acting priorVisible
        (EventGraph.IndependentReveals.not_of_not_publication_right notPublication)
        (EventGraph.IndependentReveals.not_of_not_publication_left notPublication)).mpr lower
      rw [EventGraph.Config.store_output, config.output_available]
      exact completed

variable (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

/-- Decode the semantic source view and effective own actions of the surviving
store. Physical recall and voided actions remain in the actual input; this map
is not an auxiliary source-recovery information-history projection. -/
def phaseSemanticDecisionView? {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (who : Player)
    (view : (phaseApplication runtime leaks).PlayerView) : Option (DecisionView who Γ) :=
  if same : view.application.1.who = who then
    let observed : (serviceGraph setup mode).PlayerObservation who := same ▸
      view.application.1.observation
    (decodeObservation? who refs observed.store).map fun source =>
      (source, decodeCompletions setup.program
        (observed.ownActions.map (setup.eventGraph.fromModeCompletion mode)))
  else none

/-- The actual observation at a ready owned binding always yields a typed
semantic source view, including private setup values and own effective actions. -/
theorem phaseSemanticDecisionView?_succeeds
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (before : ContextRefsBefore refs embedding) (index : Fin (eventCount program))
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (ready : execution.application.current.native.config.cut.Ready (embedding.event index))
    (acting : (serviceGraph setup mode).actor? (embedding.event index) = some who)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (embedding.event index)).IsPublication) :
    ∃ source, phaseSemanticDecisionView? setup mode runtime leaks refs who
      (execution.observe (phaseApplication runtime leaks) who) = some source := by
  obtain ⟨observation, decoded⟩ := exists_decodeObservation_of_ready setup mode program refs
    embedding before index execution.application.current.native.config who ready acting
      notPublication
  unfold phaseSemanticDecisionView?
  rw [dite_eq_left (show
    (execution.observe (phaseApplication runtime leaks) who).application.1.who = who from rfl)]
  change ∃ source, (decodeObservation? who refs
    ((serviceGraph setup mode).playerStore who
      execution.application.current.native.config.store)).map
      (fun observation => (observation, decodeCompletions setup.program
        (((serviceGraph setup mode).ownCompletions who
          execution.application.current.native.config.history).map
            (setup.eventGraph.fromModeCompletion mode)))) = some source
  rw [decoded]
  exact ⟨_, rfl⟩

end Vegas
