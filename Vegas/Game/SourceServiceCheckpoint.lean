/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceStep
import Vegas.Game.RevealServiceState
import Vegas.Source.SetupProtocol

/-! # Dynamic source configuration checkpoints

Typed source cells and source action recall agree with the actual sequential
application configuration. Commitments may extend the accepted-handle table
and candidate catalogue; neither is fixed at initialization. Registry entries
and publication positions remain in the original source configuration.

This relation says nothing about equilibrium or posterior beliefs. Operational
invariants, allocation and observation laws remain obligations of actual service
steps, rather than fields silently assuming strategic correspondence.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The semantic part of a public source boundary, valid for all source
constructors and arbitrary outstanding deferred guards. -/
structure SourceCheckpoint (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} {Γ : SourceCtx Player L} (source : Config Player L Γ)
    (refs : ContextRefs (serviceGraph setup mode).layout Γ) (rank : Nat)
    (native : (serviceGraph setup mode).Config) : Prop where
  agrees : refs.Agrees source.state native.store
  history : decodeHistory setup.program
    (native.history.map (setup.eventGraph.fromModeCompletion mode)) = source.history
  ordered : native.cut.IsPrefix rank

theorem SourceCheckpoint.initial (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} (initial : State L setup.context) : SourceCheckpoint setup
    (setup.initialConfig initial) (ContextRefs.initial setup.context (outputLayout setup.program)) 0
    (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
        (setup.eventInputs initial)).config :=
    ⟨initial_agrees setup initial, initial_history setup initial, EventOrder.Cut.empty_isPrefix _⟩

private theorem complete_source_history (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} (native : EventGraphRuntime.State (serviceGraph setup mode))
    (event : (serviceGraph setup mode).EventId) (ready : native.config.cut.Ready event)
    (action : (serviceGraph setup mode).Action event)
    (value : ((serviceGraph setup mode).outputLayout event).Value) : decodeHistory setup.program
    ((native.complete event ready action value).config.history.map
        (setup.eventGraph.fromModeCompletion mode)) =
      match decodeEventAction setup.program event action with
      | none => decodeHistory setup.program
          (native.config.history.map (setup.eventGraph.fromModeCompletion mode))
      | some sourceAction => Function.update
          (decodeHistory setup.program
            (native.config.history.map (setup.eventGraph.fromModeCompletion mode)))
          (sourceActionOwner sourceAction)
          (decodeHistory setup.program
            (native.config.history.map (setup.eventGraph.fromModeCompletion mode))
              (sourceActionOwner sourceAction) ++ [sourceAction]) := by
  change decodeHistory setup.program
    ((native.config.history ++ [(⟨event, action⟩ : (serviceGraph setup mode).Completion)]).map
      (setup.eventGraph.fromModeCompletion mode)) = _
  rw [List.map_append, List.map_singleton]
  exact decodeHistory_append_completion setup.program _ event action

theorem SourceCheckpoint.sample
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (serviceGraph setup mode).layout Γ} {rank : Nat}
    {native : EventGraphRuntime.State (serviceGraph setup mode)}
    (checkpoint : SourceCheckpoint setup source refs rank native.config)
    {payload : L.Ty} (name : VarId) (event : (serviceGraph setup mode).EventId)
    (eventRank : event.val = rank) (ready : native.config.cut.Ready event)
    (outputEq : (serviceGraph setup mode).outputLayout event = .publicData payload)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) = none)
    (value : L.Val payload) :
    SourceCheckpoint setup (sampleSuccessor name source value)
      (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1)
      (native.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)).config := by
  refine ⟨complete_sample_agrees name source refs native checkpoint.agrees event ready outputEq
    before value, ?_, checkpoint.ordered.complete_at event ready eventRank⟩
  rw [complete_source_history, decoded, checkpoint.history]
  rfl

theorem SourceCheckpoint.commit
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (serviceGraph setup mode).layout Γ} {rank : Nat}
    {native : EventGraphRuntime.State (serviceGraph setup mode)}
    (checkpoint : SourceCheckpoint setup source refs rank native.config)
    {owner : Player} {payload : L.Ty} (name : VarId)
    (guard : SourceGuard L Γ owner name payload)
    (event : (serviceGraph setup mode).EventId) (eventRank : event.val = rank)
    (ready : native.config.cut.Ready event)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (choice : PublicationResult (L.Val payload))
    (decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
        some (.commit owner name payload choice)) :
    SourceCheckpoint setup (commitSuccessor name guard source choice)
      (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1)
      (native.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm) choice)).config := by
  refine ⟨complete_commit_agrees name guard source refs native.config checkpoint.agrees event ready
    outputEq before choice, ?_, checkpoint.ordered.complete_at event ready eventRank⟩
  rw [complete_source_history, decoded, checkpoint.history]
  rfl

theorem SourceCheckpoint.reveal
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (serviceGraph setup mode).layout Γ} {rank : Nat}
    {native : EventGraphRuntime.State (serviceGraph setup mode)}
    (checkpoint : SourceCheckpoint setup source refs rank native.config)
    {name : VarId} {owner : Player} {payload : L.Ty} (published : VarId)
    (binding : HasVar Γ name (.commitment owner payload))
    (event : (serviceGraph setup mode).EventId) (eventRank : event.val = rank)
    (ready : native.config.cut.Ready event)
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (disclose : Bool)
    (decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
        some (.reveal owner name disclose)) :
    SourceCheckpoint setup (revealSuccessor published binding source disclose)
      (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1)
      (native.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (disclosureResult published binding source disclose))).config := by
  refine ⟨complete_guarded_reveal_agrees published binding source refs native checkpoint.agrees
    event ready outputEq before disclose, ?_, checkpoint.ordered.complete_at event ready eventRank⟩
  rw [complete_source_history, decoded, checkpoint.history]
  rfl

end Vegas
