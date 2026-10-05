/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBinding
import Vegas.Game.SourceServiceInitialObservation
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
    {Γ : SourceCtx Player L} (source : Config Player L Γ)
    (refs : ContextRefs (graph setup).layout Γ) (rank : Nat)
    (native : (graph setup).Config) : Prop where
  agrees : refs.Agrees source.state native.store
  history : decodeHistory setup.program
    (native.history.map (setup.eventGraph.fromModeCompletion .sequential)) = source.history
  ordered : native.cut.IsPrefix rank

theorem SourceCheckpoint.initial (setup : Setup (Player := Player) (L := L))
    (initial : State L setup.context) :
    SourceCheckpoint setup (setup.initialConfig initial)
      (ContextRefs.initial setup.context (outputLayout setup.program)) 0
      (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).config :=
  ⟨initial_agrees setup initial, initial_history setup initial,
    EventOrder.Cut.empty_isPrefix _⟩

private theorem complete_source_history (setup : Setup (Player := Player) (L := L))
    (native : EventGraphRuntime.State (graph setup))
    (event : (graph setup).EventId) (ready : native.config.cut.Ready event)
    (action : (graph setup).Action event) (value : ((graph setup).outputLayout event).Value) :
    decodeHistory setup.program
      ((native.complete event ready action value).config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) =
      match decodeEventAction setup.program event action with
      | none => decodeHistory setup.program
          (native.config.history.map (setup.eventGraph.fromModeCompletion .sequential))
      | some sourceAction => Function.update
          (decodeHistory setup.program
            (native.config.history.map (setup.eventGraph.fromModeCompletion .sequential)))
          (sourceActionOwner sourceAction)
          (decodeHistory setup.program
            (native.config.history.map (setup.eventGraph.fromModeCompletion .sequential))
              (sourceActionOwner sourceAction) ++ [sourceAction]) := by
  change decodeHistory setup.program
    ((native.config.history ++ [(⟨event, action⟩ : (graph setup).Completion)]).map
      (setup.eventGraph.fromModeCompletion .sequential)) = _
  rw [List.map_append, List.map_singleton]
  exact decodeHistory_append_completion setup.program _ event action

theorem SourceCheckpoint.sample
    {setup : Setup (Player := Player) (L := L)}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {native : EventGraphRuntime.State (graph setup)}
    (checkpoint : SourceCheckpoint setup source refs rank native.config)
    {payload : L.Ty} (name : VarId) (event : (graph setup).EventId)
    (eventRank : event.val = rank) (ready : native.config.cut.Ready event)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
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
    {setup : Setup (Player := Player) (L := L)}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {native : EventGraphRuntime.State (graph setup)}
    (checkpoint : SourceCheckpoint setup source refs rank native.config)
    {owner : Player} {payload : L.Ty} (name : VarId)
    (guard : SourceGuard L Γ owner name payload)
    (event : (graph setup).EventId) (eventRank : event.val = rank)
    (ready : native.config.cut.Ready event)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
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
    {setup : Setup (Player := Player) (L := L)}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {native : EventGraphRuntime.State (graph setup)}
    (checkpoint : SourceCheckpoint setup source refs rank native.config)
    {name : VarId} {owner : Player} {payload : L.Ty} (published : VarId)
    (binding : HasVar Γ name (.commitment owner payload))
    (event : (graph setup).EventId) (eventRank : event.val = rank)
    (ready : native.config.cut.Ready event)
    (outputEq : (graph setup).outputLayout event = .publication payload)
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

/-- A supported result of the runtime's actual public-sampling transition
is precisely a supported original source sample and its new checkpoint. -/
theorem SourceCheckpoint.sample_environment
    {setup : Setup (Player := Player) (L := L)}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {native : EventGraphRuntime.State (graph setup)}
    (checkpoint : SourceCheckpoint setup source refs rank native.config)
    {payload : L.Ty} (name : VarId) (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (event : (graph setup).EventId) (eventRank : event.val = rank)
    (ready : native.config.cut.Ready event)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload (compilePublicDist refs law))
    (node : nodeView (graph setup) event =
      .sample payload (compilePublicDist refs law) outputEq codeEq)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) = none)
    (after : EventGraphRuntime.State (graph setup))
    (supported : after ∈ (environmentStep (runtime setup) native (.executeSample event)).support) :
    ∃ value ∈ (L.evalDist law (sourcePublicEnv source.state)).support,
      SourceCheckpoint setup (sampleSuccessor name source value)
        (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1) after.config := by
  rw [source_sample_environment (runtime setup) native event ready outputEq refs law codeEq node
    source.state checkpoint.agrees, PMF.support_map] at supported
  obtain ⟨value, member, rfl⟩ := supported
  exact ⟨value, member,
    checkpoint.sample name event eventRank ready outputEq before decoded value⟩

/-- Actual compiler invocation and protected inclusion advance the original
source binding kernel. Private candidate allocation remains in the returned
execution and is not replaced by a source-state encoding. -/
theorem sourceServicePolicy_commit_checkpoint
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (checkpoint : SourceCheckpoint setup source refs offset execution.application.config)
    (serial : Nat)
    (selected : reactiveFreshSlot (execution.observe
      (application setup leaks) owner).application = some serial)
    (candidate : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (unused : execution.application.HandleUnused (owner, .prepared serial))
    (serials : execution.network.SerialsBeforeNext)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event := embedding.event index
    let outputEq : (graph setup).outputLayout event = .binding owner payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    ∀ (ready : execution.application.config.cut.Ready event)
      (timely : execution.application.WithinDeadline (runtime setup) event)
      (vacant : execution.application.accepted (.inr event) = none)
      (after : (application setup leaks).Execution),
      after ∈ ((sourceServicePolicy setup leaks wholeProfile owner (execution.recall owner)
        (execution.observe (application setup leaks) owner)).bind fun response =>
          (runtime setup).interactionStep leaks players network (.includeLatest event owner)
            (execution.respond (application setup leaks) owner response)).support →
      ∃ choice ∈ (commitKernel profile (source.view owner)).support,
        SourceCheckpoint setup (commitSuccessor name guard source choice)
          (refs.cons (name := name) ⟨.inr event, outputEq⟩) (offset + 1)
          after.application.config ∧
        after.receipts = execution.receipts ++
          [((owner, execution.network.nextSerial owner), true)] := by
  intro index event outputEq ready timely vacant after supported
  have law := sourceServicePolicy_commit_service setup leaks fresh guard next wholeProfile profile
    refs source embedding refsBefore offset aligned execution checkpoint.agrees checkpoint.history
    serial selected candidate unused serials players network ready timely vacant
  have mapped : (after.application.config, after.receipts) ∈
      (((sourceServicePolicy setup leaks wholeProfile owner (execution.recall owner)
        (execution.observe (application setup leaks) owner)).bind fun response =>
          (runtime setup).interactionStep leaks players network (.includeLatest event owner)
            (execution.respond (application setup leaks) owner response)).map
              (fun final => (final.application.config, final.receipts))).support := by
    rw [PMF.support_map]
    exact ⟨after, supported, rfl⟩
  rw [law, PMF.support_map] at mapped
  obtain ⟨choice, chosen, same⟩ := mapped
  have stateEq := congrArg Prod.fst same
  have receiptEq := congrArg Prod.snd same
  dsimp only at stateEq receiptEq
  have eventRank : event.val = offset := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
        some (.commit owner name payload choice) := by
    have action := aligned.actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
    simpa [event, index, outputEq, decodeEventAction] using action
  refine ⟨choice, chosen, ?_, receiptEq.symm⟩
  exact stateEq ▸ checkpoint.commit name guard event eventRank ready outputEq
    (fun ref => refsBefore ref index) choice decoded

end Vegas
