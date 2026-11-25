module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphSourceStep
public import Vegas.Compile.EventGraphHistory
public import Vegas.Compile.EventGraphInputs
public import Vegas.EventGraph.SequentialNormalization
public import Vegas.EventGraph.SequentialDistribution
public import Vegas.Source.SetupProtocol

@[expose] public section

/-! # Source configuration agreement at graph prefixes -/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Arbitrarily correlated initialized source states are encoded exactly in
the compiled graph's initial store. -/
theorem initial_agrees (setup : Setup (Player := Player) (L := L))
    {deps : setup.dataflowGraph.Dependencies}
    (initial : State L setup.context) :
    (ContextRefs.initial setup.context (outputLayout setup.program)).Agrees initial
      (EventGraph.Config.initial (graph := setup.dataflowGraph.withDependencies deps)
        (setup.eventInputs initial)).store := by
  apply ContextRefs.initial_agrees
  intro input
  rfl

theorem initial_history (setup : Setup (Player := Player) (L := L))
    {deps : setup.dataflowGraph.Dependencies} (initial : State L setup.context) : decodeHistory
    setup.program
    ((EventGraph.Config.initial (graph := setup.dataflowGraph.withDependencies deps)
        (setup.eventInputs initial)).history) = fun _ => [] := rfl

/-- The semantic part of a public source boundary, valid for all source
constructors and arbitrary outstanding deferred guards. -/
structure SourceCheckpoint (setup : Setup (Player := Player) (L := L))
    {deps : setup.dataflowGraph.Dependencies} {Γ : SourceCtx Player L} (source : Config Player L Γ)
    (refs : ContextRefs (setup.dataflowGraph.withDependencies deps).layout Γ) (rank : Nat)
    (native : (setup.dataflowGraph.withDependencies deps).Config) : Prop where
  agrees : refs.Agrees source.state native.store
  history : decodeHistory setup.program
    (native.history) = source.history
  defaults : native.defaults = source.defaults
  ordered : native.cut.IsPrefix rank

theorem SourceCheckpoint.initial (setup : Setup (Player := Player) (L := L))
    {deps : setup.dataflowGraph.Dependencies} (initial : State L setup.context) :
    SourceCheckpoint setup
    (Config.initial initial) (ContextRefs.initial setup.context (outputLayout setup.program)) 0
    (EventGraph.Config.initial (graph := setup.dataflowGraph.withDependencies deps)
        (setup.eventInputs initial)) :=
    ⟨initial_agrees setup initial, initial_history setup initial, rfl,
      EventOrder.Cut.empty_isPrefix _⟩

private theorem complete_source_history (setup : Setup (Player := Player) (L := L))
    {deps : setup.dataflowGraph.Dependencies}
    (native : (setup.dataflowGraph.withDependencies deps).Config)
    (event : (setup.dataflowGraph.withDependencies deps).EventId) (ready : native.cut.Ready event)
    (action : (setup.dataflowGraph.withDependencies deps).Action event)
    (value : ((setup.dataflowGraph.withDependencies deps).outputLayout event).Value) :
    decodeHistory setup.program
    ((native.complete event ready action value).history) =
      match (native.actualDecision event action).bind
          (decodeEventAction setup.program event) with
      | none => decodeHistory setup.program
          (native.history)
      | some sourceAction => Function.update
          (decodeHistory setup.program
            (native.history))
          (sourceActionOwner sourceAction)
          (decodeHistory setup.program
            (native.history)
              (sourceActionOwner sourceAction) ++ [sourceAction]) := by
  change decodeHistory setup.program
    ((native.history ++ [EventGraph.completion (setup.dataflowGraph.withDependencies deps) event
      (native.actualDecision event action) value])) = _
  exact decodeHistory_append_completion setup.program _ event
    (native.actualDecision event action) _

theorem SourceCheckpoint.sample
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (setup.dataflowGraph.withDependencies deps).layout Γ} {rank : Nat}
    {native : (setup.dataflowGraph.withDependencies deps).Config}
    (checkpoint : SourceCheckpoint setup source refs rank native)
    {payload : L.Ty} (name : VarId) (event : (setup.dataflowGraph.withDependencies deps).EventId)
    (eventRank : event.val = rank) (ready : native.cut.Ready event)
    (outputEq : (setup.dataflowGraph.withDependencies deps).outputLayout event =
      .publicData payload)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) = none)
    (value : L.Val payload) :
    SourceCheckpoint setup (sampleSuccessor name source value)
      (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1)
      (native.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)) := by
  refine ⟨complete_sample_agrees name source refs native checkpoint.agrees event ready outputEq
    before value, ?_, ?_, checkpoint.ordered.complete_at event ready eventRank⟩
  · have actor : ((setup.dataflowGraph.withDependencies deps).nodes event).actor = none := by
      change (toInformationGraph setup.program).actor? event = none
      have law := (decodeEventAction_owner setup.program event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)).symm
      rw [eventOwner?_eq_actor] at law
      simpa [decoded, EventGraph.actor?] using law
    change (setup.dataflowGraph.nodes event).actor = none at actor
    rw [complete_source_history]
    simp [EventGraph.Config.actualDecision, EventGraph.EventCode.actualDecision,
      actor, checkpoint.history, sampleSuccessor]
  · rw [native.complete_defaults_of_code event ready outputEq
        (cast (congrArg (EventGraph.EventCode (setup.dataflowGraph.withDependencies deps).layout)
          outputEq)
          ((setup.dataflowGraph.withDependencies deps).nodes event)) rfl]
    cases code : cast
        (congrArg (EventGraph.EventCode (setup.dataflowGraph.withDependencies deps).layout)
          outputEq)
        ((setup.dataflowGraph.withDependencies deps).nodes event) with
    | sample payload law =>
        simp [EventGraph.EventCode.actualDecision, EventGraph.EventCode.actor,
          checkpoint.defaults, sampleSuccessor]

theorem SourceCheckpoint.commit
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (setup.dataflowGraph.withDependencies deps).layout Γ} {rank : Nat}
    {native : (setup.dataflowGraph.withDependencies deps).Config}
    (checkpoint : SourceCheckpoint setup source refs rank native)
    {owner : Player} {payload : L.Ty} (name : VarId)
    (guard : SourceGuard L Γ owner name payload)
    (event : (setup.dataflowGraph.withDependencies deps).EventId) (eventRank : event.val = rank)
    (ready : native.cut.Ready event)
    (outputEq : (setup.dataflowGraph.withDependencies deps).outputLayout event =
      .binding owner payload)
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
          ((commitSuccessor name guard source choice).state.get .here))) := by
  have actor : ((setup.dataflowGraph.withDependencies deps).nodes event).actor = some owner := by
    change (toInformationGraph setup.program).actor? event = some owner
    have law := (decodeEventAction_owner setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)).symm
    rw [eventOwner?_eq_actor] at law
    simpa [decoded, sourceActionOwner, EventGraph.actor?] using law
  change (setup.dataflowGraph.nodes event).actor = some owner at actor
  have status : native.defaulted = source.defaulted :=
    congrArg DefaultHistory.defaulted checkpoint.defaults
  refine ⟨complete_commit_agrees name guard source refs native checkpoint.agrees event ready
    outputEq before choice, ?_, ?_, checkpoint.ordered.complete_at event ready eventRank⟩
  · rw [complete_source_history]
    by_cases inactive : owner ∈ source.defaulted <;>
      simp [EventGraph.Config.actualDecision, EventGraph.EventCode.actualDecision,
        actor, status, inactive, decoded, checkpoint.history, commitSuccessor, sourceActionOwner]
  · rw [native.complete_defaults_of_code event ready outputEq
        (cast (congrArg (EventGraph.EventCode (setup.dataflowGraph.withDependencies deps).layout)
          outputEq)
          ((setup.dataflowGraph.withDependencies deps).nodes event)) rfl]
    cases code : cast
        (congrArg (EventGraph.EventCode (setup.dataflowGraph.withDependencies deps).layout)
          outputEq)
        ((setup.dataflowGraph.withDependencies deps).nodes event) with
    | bind owner payload =>
        by_cases inactive : owner ∈ source.defaulted <;>
          simp [EventGraph.EventCode.actualDecision, EventGraph.EventCode.actor,
            EventGraph.EventCode.defaultEvent, EventGraph.EventCode.causesDefault,
            status, inactive, checkpoint.defaults, commitSuccessor]

theorem SourceCheckpoint.reveal
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (setup.dataflowGraph.withDependencies deps).layout Γ} {rank : Nat}
    {native : (setup.dataflowGraph.withDependencies deps).Config}
    (checkpoint : SourceCheckpoint setup source refs rank native)
    {name : VarId} {owner : Player} {payload : L.Ty} (published : VarId)
    (binding : HasVar Γ name (.commitment owner payload))
    (event : (setup.dataflowGraph.withDependencies deps).EventId) (eventRank : event.val = rank)
    (ready : native.cut.Ready event)
    (outputEq : (setup.dataflowGraph.withDependencies deps).outputLayout event =
      .publication payload)
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
          (disclosureResult published binding source disclose))) := by
  have actor : ((setup.dataflowGraph.withDependencies deps).nodes event).actor = some owner := by
    change (toInformationGraph setup.program).actor? event = some owner
    have law := (decodeEventAction_owner setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)).symm
    rw [eventOwner?_eq_actor] at law
    simpa [decoded, sourceActionOwner, EventGraph.actor?] using law
  change (setup.dataflowGraph.nodes event).actor = some owner at actor
  have status : native.defaulted = source.defaulted :=
    congrArg DefaultHistory.defaulted checkpoint.defaults
  refine ⟨complete_guarded_reveal_agrees published binding source refs native checkpoint.agrees
    event ready outputEq before disclose, ?_, ?_,
    checkpoint.ordered.complete_at event ready eventRank⟩
  · rw [complete_source_history]
    by_cases inactive : owner ∈ source.defaulted <;>
      simp [EventGraph.Config.actualDecision, EventGraph.EventCode.actualDecision,
        actor, status, inactive, decoded, checkpoint.history, revealSuccessor, sourceActionOwner]
  · rw [native.complete_defaults_of_code event ready outputEq
        (cast (congrArg (EventGraph.EventCode (setup.dataflowGraph.withDependencies deps).layout)
          outputEq)
          ((setup.dataflowGraph.withDependencies deps).nodes event)) rfl]
    have codeActor :
        (cast (congrArg (EventGraph.EventCode (setup.dataflowGraph.withDependencies deps).layout)
          outputEq)
          ((setup.dataflowGraph.withDependencies deps).nodes event)).actor = some owner :=
      (EventGraph.EventCode.actor_cast outputEq _).trans actor
    cases code : cast
        (congrArg (EventGraph.EventCode (setup.dataflowGraph.withDependencies deps).layout)
          outputEq)
        ((setup.dataflowGraph.withDependencies deps).nodes event) with
    | resolve actual payload ref checks =>
        rw [code] at codeActor
        have ownerEq : actual = owner := Option.some.inj codeActor
        subst actual
        by_cases inactive : owner ∈ source.defaulted <;>
          simp [EventGraph.EventCode.actualDecision, EventGraph.EventCode.actor,
            EventGraph.EventCode.defaultEvent, EventGraph.EventCode.causesDefault,
            status, inactive, checkpoint.defaults, revealSuccessor, disclosureResult]

/-- A source checkpoint survives a change to any valid compiled dependencies. -/
theorem SourceCheckpoint.fromSequentialConfig
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs setup.informationGraph.layout Γ} {rank : Nat}
    {ghost : setup.informationGraph.Config}
    (checkpoint : SourceCheckpoint (deps := setup.informationDependencies) setup source refs rank
      ghost) :
    SourceCheckpoint (deps := deps) setup source refs rank
      ((setup.dataflowGraph.withDependencies deps).fromSequentialConfig ghost) := by
  have stores : ((setup.dataflowGraph.withDependencies deps).fromSequentialConfig ghost).store =
      ghost.store := by
    funext field
    cases field <;> rfl
  refine ⟨?_, checkpoint.history, checkpoint.defaults, checkpoint.ordered⟩
  rw [stores]
  exact checkpoint.agrees

end Vegas
