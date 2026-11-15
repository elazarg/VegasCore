module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceStep
public import Vegas.Game.RevealServiceState
public import Vegas.Source.SetupProtocol
public import Vegas.Pending.ExclusionCompletion
public import Vegas.EventGraph.SequentialNormalization

@[expose] public section

/-! # Dynamic source configuration checkpoints

Typed source cells, public default history and source action recall agree with the sequential
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
    {deps : setup.dataflowGraph.Dependencies} {Γ : SourceCtx Player L} (source : Config Player L Γ)
    (refs : ContextRefs (serviceGraph setup deps).layout Γ) (rank : Nat)
    (native : (serviceGraph setup deps).Config) : Prop where
  agrees : refs.Agrees source.state native.store
  history : decodeHistory setup.program
    (native.history) = source.history
  defaults : native.defaults = source.defaults
  ordered : native.cut.IsPrefix rank

theorem SourceCheckpoint.initial (setup : Setup (Player := Player) (L := L))
    {deps : setup.dataflowGraph.Dependencies} (initial : State L setup.context) :
    SourceCheckpoint setup
    (Config.initial initial) (ContextRefs.initial setup.context (outputLayout setup.program)) 0
    (EventGraphRuntime.State.initial (graph := serviceGraph setup deps)
        (setup.eventInputs initial)).config :=
    ⟨initial_agrees setup initial, initial_history setup initial, rfl,
      EventOrder.Cut.empty_isPrefix _⟩

private theorem complete_source_history (setup : Setup (Player := Player) (L := L))
    {deps : setup.dataflowGraph.Dependencies}
    (native : EventGraphRuntime.State (serviceGraph setup deps))
    (event : (serviceGraph setup deps).EventId) (ready : native.config.cut.Ready event)
    (action : (serviceGraph setup deps).Action event)
    (value : ((serviceGraph setup deps).outputLayout event).Value) : decodeHistory setup.program
    ((native.complete event ready action value).config.history) =
      match (native.config.actualDecision event action).bind
          (decodeEventAction setup.program event) with
      | none => decodeHistory setup.program
          (native.config.history)
      | some sourceAction => Function.update
          (decodeHistory setup.program
            (native.config.history))
          (sourceActionOwner sourceAction)
          (decodeHistory setup.program
            (native.config.history)
              (sourceActionOwner sourceAction) ++ [sourceAction]) := by
  change decodeHistory setup.program
    ((native.config.history ++ [EventGraph.completion (serviceGraph setup deps) event
      (native.config.actualDecision event action) value])) = _
  exact decodeHistory_append_completion setup.program _ event
    (native.config.actualDecision event action) _

theorem SourceCheckpoint.sample
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (serviceGraph setup deps).layout Γ} {rank : Nat}
    {native : EventGraphRuntime.State (serviceGraph setup deps)}
    (checkpoint : SourceCheckpoint setup source refs rank native.config)
    {payload : L.Ty} (name : VarId) (event : (serviceGraph setup deps).EventId)
    (eventRank : event.val = rank) (ready : native.config.cut.Ready event)
    (outputEq : (serviceGraph setup deps).outputLayout event = .publicData payload)
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
    before value, ?_, ?_, checkpoint.ordered.complete_at event ready eventRank⟩
  · have actor : ((serviceGraph setup deps).nodes event).actor = none := by
      change (toInformationGraph setup.program).actor? event = none
      have law := (decodeEventAction_owner setup.program event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)).symm
      rw [eventOwner?_eq_actor] at law
      simpa [decoded, EventGraph.actor?] using law
    change (setup.dataflowGraph.nodes event).actor = none at actor
    rw [complete_source_history]
    simp [EventGraph.Config.actualDecision, EventGraph.EventCode.actualDecision,
      actor, checkpoint.history, sampleSuccessor]
  · rw [EventGraphRuntime.State.complete,
      native.config.complete_defaults_of_code event ready outputEq
        (cast (congrArg (EventGraph.EventCode (serviceGraph setup deps).layout) outputEq)
          ((serviceGraph setup deps).nodes event)) rfl]
    cases code : cast
        (congrArg (EventGraph.EventCode (serviceGraph setup deps).layout) outputEq)
        ((serviceGraph setup deps).nodes event) with
    | sample payload law =>
        simp [EventGraph.EventCode.actualDecision, EventGraph.EventCode.actor,
          checkpoint.defaults, sampleSuccessor]

theorem SourceCheckpoint.commit
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (serviceGraph setup deps).layout Γ} {rank : Nat}
    {native : EventGraphRuntime.State (serviceGraph setup deps)}
    (checkpoint : SourceCheckpoint setup source refs rank native.config)
    {owner : Player} {payload : L.Ty} (name : VarId)
    (guard : SourceGuard L Γ owner name payload)
    (event : (serviceGraph setup deps).EventId) (eventRank : event.val = rank)
    (ready : native.config.cut.Ready event)
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (choice : Option (PublicationResult (L.Val payload)))
    (decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
        some (.commit owner name payload choice)) :
    SourceCheckpoint setup (commitSuccessor name guard source choice)
      (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1)
      (native.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          ((commitSuccessor name guard source choice).state.get .here))).config := by
  have actor : ((serviceGraph setup deps).nodes event).actor = some owner := by
    change (toInformationGraph setup.program).actor? event = some owner
    have law := (decodeEventAction_owner setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)).symm
    rw [eventOwner?_eq_actor] at law
    simpa [decoded, sourceActionOwner, EventGraph.actor?] using law
  change (setup.dataflowGraph.nodes event).actor = some owner at actor
  have status : native.config.defaulted = source.defaulted :=
    congrArg DefaultHistory.defaulted checkpoint.defaults
  refine ⟨complete_commit_agrees name guard source refs native.config checkpoint.agrees event ready
    outputEq before choice, ?_, ?_, checkpoint.ordered.complete_at event ready eventRank⟩
  · rw [complete_source_history]
    by_cases inactive : owner ∈ source.defaulted <;>
      simp [EventGraph.Config.actualDecision, EventGraph.EventCode.actualDecision,
        actor, status, inactive, decoded, checkpoint.history, commitSuccessor, sourceActionOwner]
  · rw [EventGraphRuntime.State.complete,
      native.config.complete_defaults_of_code event ready outputEq
        (cast (congrArg (EventGraph.EventCode (serviceGraph setup deps).layout) outputEq)
          ((serviceGraph setup deps).nodes event)) rfl]
    cases code : cast
        (congrArg (EventGraph.EventCode (serviceGraph setup deps).layout) outputEq)
        ((serviceGraph setup deps).nodes event) with
    | bind owner payload =>
        by_cases inactive : owner ∈ source.defaulted <;>
          simp [EventGraph.EventCode.actualDecision, EventGraph.EventCode.actor,
            EventGraph.EventCode.defaultEvent, EventGraph.EventCode.causesDefault,
            status, inactive, checkpoint.defaults, commitSuccessor]

theorem SourceCheckpoint.reveal
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (serviceGraph setup deps).layout Γ} {rank : Nat}
    {native : EventGraphRuntime.State (serviceGraph setup deps)}
    (checkpoint : SourceCheckpoint setup source refs rank native.config)
    {name : VarId} {owner : Player} {payload : L.Ty} (published : VarId)
    (binding : HasVar Γ name (.commitment owner payload))
    (event : (serviceGraph setup deps).EventId) (eventRank : event.val = rank)
    (ready : native.config.cut.Ready event)
    (outputEq : (serviceGraph setup deps).outputLayout event = .publication payload)
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
  have actor : ((serviceGraph setup deps).nodes event).actor = some owner := by
    change (toInformationGraph setup.program).actor? event = some owner
    have law := (decodeEventAction_owner setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)).symm
    rw [eventOwner?_eq_actor] at law
    simpa [decoded, sourceActionOwner, EventGraph.actor?] using law
  change (setup.dataflowGraph.nodes event).actor = some owner at actor
  have status : native.config.defaulted = source.defaulted :=
    congrArg DefaultHistory.defaulted checkpoint.defaults
  refine ⟨complete_guarded_reveal_agrees published binding source refs native checkpoint.agrees
    event ready outputEq before disclose, ?_, ?_,
    checkpoint.ordered.complete_at event ready eventRank⟩
  · rw [complete_source_history]
    by_cases inactive : owner ∈ source.defaulted <;>
      simp [EventGraph.Config.actualDecision, EventGraph.EventCode.actualDecision,
        actor, status, inactive, decoded, checkpoint.history, revealSuccessor, sourceActionOwner]
  · rw [EventGraphRuntime.State.complete,
      native.config.complete_defaults_of_code event ready outputEq
        (cast (congrArg (EventGraph.EventCode (serviceGraph setup deps).layout) outputEq)
          ((serviceGraph setup deps).nodes event)) rfl]
    have codeActor :
        (cast (congrArg (EventGraph.EventCode (serviceGraph setup deps).layout) outputEq)
          ((serviceGraph setup deps).nodes event)).actor = some owner :=
      (EventGraph.EventCode.actor_cast outputEq _).trans actor
    cases code : cast
        (congrArg (EventGraph.EventCode (serviceGraph setup deps).layout) outputEq)
        ((serviceGraph setup deps).nodes event) with
    | resolve actual payload ref checks =>
        rw [code] at codeActor
        have ownerEq : actual = owner := Option.some.inj codeActor
        subst actual
        by_cases inactive : owner ∈ source.defaulted <;>
          simp [EventGraph.EventCode.actualDecision, EventGraph.EventCode.actor,
            EventGraph.EventCode.defaultEvent, EventGraph.EventCode.causesDefault,
            status, inactive, checkpoint.defaults, revealSuccessor, disclosureResult]

/-- Automatic service of a defaulted binding performs its existing typed source successor. -/
theorem SourceCheckpoint.commitAutomatic
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (serviceGraph setup deps).layout Γ} {rank : Nat}
    {native : EventGraphRuntime.State (serviceGraph setup deps)}
    (checkpoint : SourceCheckpoint setup source refs rank native.config)
    {owner : Player} {payload : L.Ty} (name : VarId)
    (guard : SourceGuard L Γ owner name payload)
    (event : (serviceGraph setup deps).EventId) (eventRank : event.val = rank)
    (eligible : native.AutomaticReady event)
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup deps).layout) outputEq)
      ((serviceGraph setup deps).nodes event) = .bind owner payload)
    (decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (none : Option (PublicationResult (L.Val payload)))) =
      some (.commit owner name payload none)) :
    SourceCheckpoint setup (commitSuccessor name guard source none)
      (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1)
      (native.completeAutomatic event eligible).config := by
  have next := checkpoint.commit name guard event eventRank eligible.1 outputEq before none decoded
  have output : (commitSuccessor name guard source none).state.get .here = .failure := by
    simp only [commitSuccessor, Env.get, Env.cons, ite_self, Option.getD_none]
  rw [output] at next
  simpa only [State.completeAutomatic, State.completeFailure, nodeView_eq_bind outputEq codeEq]
    using next

/-- Automatic service of a defaulted publication performs its existing typed source successor. -/
theorem SourceCheckpoint.revealAutomatic
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (serviceGraph setup deps).layout Γ} {rank : Nat}
    {native : EventGraphRuntime.State (serviceGraph setup deps)}
    (checkpoint : SourceCheckpoint setup source refs rank native.config)
    {name : VarId} {owner : Player} {payload : L.Ty} (published : VarId)
    (binding : HasVar Γ name (.commitment owner payload))
    (event : (serviceGraph setup deps).EventId) (eventRank : event.val = rank)
    (eligible : native.AutomaticReady event)
    (outputEq : (serviceGraph setup deps).outputLayout event = .publication payload)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup deps).layout) outputEq)
      ((serviceGraph setup deps).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding))
    (decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) false) =
      some (.reveal owner name false)) :
    SourceCheckpoint setup (revealSuccessor published binding source false)
      (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1)
      (native.completeAutomatic event eligible).config := by
  have next := checkpoint.reveal published binding event eventRank eligible.1 outputEq before
    false decoded
  rw [disclosureResult_false] at next
  simpa only [State.completeAutomatic, State.completeFailure, nodeView_eq_resolve outputEq codeEq]
    using next


/-- A source checkpoint survives a change to any valid compiled dependencies. -/
theorem SourceCheckpoint.fromSequentialConfig
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs setup.informationGraph.layout Γ} {rank : Nat}
    {ghost : setup.informationGraph.Config}
    (checkpoint : SourceCheckpoint (deps := setup.informationDependencies) setup source refs rank
      ghost) :
    SourceCheckpoint (deps := deps) setup source refs rank
      ((serviceGraph setup deps).fromSequentialConfig ghost) := by
  have stores : ((serviceGraph setup deps).fromSequentialConfig ghost).store = ghost.store := by
    funext field
    cases field <;> rfl
  refine ⟨?_, checkpoint.history, checkpoint.defaults, checkpoint.ordered⟩
  rw [stores]
  exact checkpoint.agrees

end Vegas
