/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitPrefixCompletion
import Vegas.Game.ServiceInformation
import Vegas.Pending.ReactiveEventStability

/-! # Visible source state at a ready commitment with hidden unfinished bindings -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)

/-- Readiness makes every earlier binding owned by the active player available,
regardless of unfinished hidden foreign commitments. -/
theorem commitPrefix_owned_completed_of_ready
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (config : (serviceGraph setup mode).Config) (who : Player)
    (selected : Fin (eventCount (block.prepend suffix))) (atEnd : selected.val = block.length)
    (ready : config.cut.Ready (embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (embedding.event selected) = some who)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (embedding.event selected)).IsPublication) :
    ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      eventOwner? (block.prepend suffix) index = some who →
        embedding.event index ∈ config.cut.completed := by
  intro prior earlier owned
  obtain ⟨owner, payload, _member, layout⟩ := block.binding_before_length suffix prior earlier
  have localActor := EventGraph.actor?_of_outputLayout_binding (toEventGraph
    (block.prepend suffix)) layout
  have ownerEq : owner = who := Option.some.inj (localActor.symm.trans
    ((eventOwner?_eq_actor (block.prepend suffix) prior).symm.trans owned))
  subst owner
  have output : (serviceGraph setup mode).outputLayout (embedding.event prior) =
      .binding who payload := (embedding.layout_eq prior).trans layout
  have visible : ((serviceGraph setup mode).outputLayout (embedding.event prior)).VisibleTo
      who := by
    rw [output]
    rfl
  have completed := ((serviceGraph_revealRelaxedOrdered setup mode).ready_visible_iff
    config.cut ready acting visible
      (EventGraph.IndependentReveals.not_of_not_publication_right notPublication)
      (EventGraph.IndependentReveals.not_of_not_publication_left notPublication)).mpr
    (embedding.strictMono (Fin.mk_lt_mk.mpr (earlier.trans_eq atEnd.symm)))
  exact completed

/-- Readiness makes every earlier binding owned by the active player available,
regardless of unfinished hidden foreign commitments. -/
theorem commitPrefix_owned_fields_of_ready
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (config : (serviceGraph setup mode).Config) (who : Player)
    (selected : Fin (eventCount (block.prepend suffix))) (atEnd : selected.val = block.length)
    (ready : config.cut.Ready (embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (embedding.event selected) = some who)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (embedding.event selected)).IsPublication) :
    ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      eventOwner? (block.prepend suffix) index = some who →
        ((embedding.ref index).get? config.store).isSome = true := by
  intro prior earlier owned
  apply (embedding.ref prior).get?_isSome
  change (config.store (.inr (embedding.event prior))).isSome = true
  rw [EventGraph.Config.store_output, config.output_available]
  exact commitPrefix_owned_completed_of_ready setup mode block suffix embedding config who
    selected atEnd ready acting notPublication prior earlier owned

/-- Complete the earlier commitment slots from the actual partial store. Every
own slot is already present by readiness; unavailable foreign cells are hidden
and can be filled by a legal failed value without changing the decoded view. -/
theorem fillCommitPrefix_observation_of_ready
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (refs : ContextRefs (graphLayout setup.program) Γ)
    (config : (serviceGraph setup mode).Config) (entry : SourceProgram.Config Player L Γ)
    (who : Player)
    (decoded : decodeObservation? who refs config.store = some (sourceObserve who entry.state))
    (selected : Fin (eventCount (block.prepend suffix))) (atEnd : selected.val = block.length)
    (ready : config.cut.Ready (embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (embedding.event selected) = some who)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (embedding.event selected)).IsPublication) :
    decodeObservation? who (commitBlockRefs setup.program block suffix embedding refs)
        config.store =
      some (sourceObserve who
        (fillCommitPrefix setup.program block suffix embedding config.store entry).state) := by
  exact fillCommitPrefix_observation setup.program block suffix embedding refs config.store entry
    who decoded (commitPrefix_owned_fields_of_ready setup mode block suffix embedding config who
      selected atEnd ready acting notPublication)

end Vegas
