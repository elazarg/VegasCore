/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.ResolutionProvenance
import Vegas.Source.DisclosureBehavioral
import Vegas.Game.AsyncDeviationForeign
import Vegas.Game.SourceServiceChanceContinuation
import Vegas.Game.SourceServiceDeviationChoice
import GameTheoryExtensions.Math.Probability.ObservedChoice

/-! # Source successors jointly with native deviation traffic

Public chance and honest foreign decisions pair actual focal traffic with
their source successors. The traffic factors through each successor's full
source view, including public defaults. A native endpoint retains a primary
typed checkpoint followed by automatic completion of variable length.
-/

noncomputable section
namespace Vegas
open SourceProgram EventGraph Interaction GameTheory.Math.Probability EventGraphRuntime
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private def sampledValue {compiled : Vegas.EventGraph Player L}
    (event : compiled.EventId) {payload : L.Ty}
    (outputEq : compiled.outputLayout event = .publicData payload)
    (config : compiled.Config) : L.Val payload :=
  ((config.outputs event).map (cast (congrArg EventField.Value outputEq))).getD
    (L.someValue payload)

private theorem chance_completed_value_law
    {setup : Setup (Player := Player) (L := L)} (timeouts : EventTimeouts (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : (graph setup).BehavioralProfile)
    (scheduler : (application setup timeouts leaks).Scheduler)
    (players : Player → (application setup timeouts leaks).Policy)
    (event : (graph setup).EventId) (ownerless : (graph setup).actor? event = none)
    (count : Nat) (execution : (application setup timeouts leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    {Γ : SourceCtx Player L} {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (refs : ContextRefs (graph setup).layout Γ)
    (distribution : L.DistExpr (SourcePublicCtx L Γ) payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload (compilePublicDist refs distribution))
    (source : State L Γ) (agrees : refs.Agrees source execution.application.config.store)
    (completed : ∀ final ∈ ((application setup timeouts leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count execution).support,
      event ∈ final.application.config.cut.completed) :
    ((application setup timeouts leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count execution).map
        (fun final => sampledValue event outputEq final.application.config) =
      L.evalDist distribution (sourcePublicEnv source) := by
  have raw := chance_completed_output_law timeouts leaks profile scheduler players event ownerless
    count execution ready completed
  rw [((graph setup).nodes event).action_eq_of_actor_none ownerless
    (EventCode.actionOfActorNone ((graph setup).nodes event) ownerless)
    (cast (congrArg EventField.Action outputEq.symm) PUnit.unit),
    sample_step execution.application.config event ready outputEq refs distribution codeEq
      source agrees, PMF.map_comp] at raw
  have projected := congrArg (PMF.map
    (fun value : Option ((graph setup).outputLayout event).Value =>
    (value.map (cast (congrArg EventField.Value outputEq))).getD (L.someValue payload))) raw
  simp only [PMF.map_comp, Function.comp_def] at projected
  change
    ((application setup timeouts leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count execution).map
        (fun final => sampledValue event outputEq final.application.config) =
    (L.evalDist distribution (sourcePublicEnv source)).map (fun value : L.Val payload =>
      sampledValue event outputEq (execution.application.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventField.Value outputEq.symm) value))) at projected
  have reads : (fun value : L.Val payload =>
      sampledValue event outputEq (execution.application.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventField.Value outputEq.symm) value))) = id := by
    funext value
    simp only [sampledValue, EventGraph.Config.complete, Function.update_self,
      Option.map_some, cast_cast, cast_eq, Option.getD_some, id_eq]
  rw [reads] at projected
  exact projected.trans (PMF.map_id _)

private def sampledTrafficValue
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {duration : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (event : (serviceGraph setup mode).EventId) {payload : L.Ty}
    (outputEq : (serviceGraph setup mode).outputLayout event = .publicData payload)
    (traffic : MessageNetwork Player (serviceApplication setup mode duration leaks).Payload ×
      List (MessageId Player × Bool) ×
      List (serviceApplication setup mode duration leaks).EnvironmentEntry ×
      List (serviceApplication setup mode duration leaks).PlayerEntry ×
      PlayerView (serviceGraph setup mode) × PublicView (serviceGraph setup mode)) :
    L.Val payload :=
  ((traffic.2.2.2.2.2.observation.store (.inr event)).map
    (cast (congrArg EventField.Value outputEq))).getD (L.someValue payload)

private theorem sampledTrafficValue_eq
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {duration : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (focal : Player) (event : (serviceGraph setup mode).EventId) {payload : L.Ty}
    (outputEq : (serviceGraph setup mode).outputLayout event = .publicData payload)
    (execution : (serviceApplication setup mode duration leaks).Execution) :
    sampledTrafficValue setup leaks event outputEq
      ((bindingTraffic (serviceTimeouts setup mode duration)) leaks focal execution) =
      sampledValue event outputEq execution.application.config := by
  have publicField : (serviceGraph setup mode).fieldPublic (.inr event) := by
    change ((serviceGraph setup mode).outputLayout event).IsPublic
    rw [outputEq]
    trivial
  dsimp only [sampledTrafficValue, bindingTraffic, State.publicView, EventGraph.publicObserve]
  rw [EventGraph.publicStore_of_public _ _ _ publicField]
  rfl

private theorem primary_sample_joint_of_marginal
    {Seed : Type} {Γ : SourceCtx Player L} {payload : L.Ty}
    (name : VarId) (distribution : L.DistExpr (SourcePublicCtx L Γ) payload)
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {duration : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (scheduler : (serviceApplication setup mode duration leaks).Scheduler)
    (focal : Player) (deviation : (serviceApplication setup mode duration leaks).Policy)
    (event : (serviceGraph setup mode).EventId)
    (ownerless : (serviceGraph setup mode).actor? event = none)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (horizon : Nat) (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (serviceApplication setup mode duration leaks).Execution)
    (pick : MessageNetwork Player (serviceApplication setup mode duration leaks).Payload ×
      List (MessageId Player × Bool) ×
      List (serviceApplication setup mode duration leaks).EnvironmentEntry ×
      List (serviceApplication setup mode duration leaks).PlayerEntry ×
      PlayerView (serviceGraph setup mode) × PublicView (serviceGraph setup mode) → L.Val payload)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
      (bindingTraffic (serviceTimeouts setup mode duration)) leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun traffic => (config, traffic))
    (ready : ∀ seed ∈ prior.support, event ∉ (execution seed).application.config.cut.completed →
      (execution seed).application.config.cut.Ready event)
    (sampled : ∀ seed ∈ prior.support,
      (((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
        (focalPlayers setup leaks focal deviation)
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).map fun final =>
          pick ((bindingTraffic (serviceTimeouts setup mode duration)) leaks focal final)) =
      L.evalDist distribution (sourcePublicEnv (source seed).state)) :
    ∃ nextNoise : DecisionView focal ((name, .publicData payload) :: Γ) → PMF _,
      (prior.bind fun seed =>
        ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
          (focalPlayers setup leaks focal deviation)
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            (sampleSuccessor name (source seed)
              (pick ((bindingTraffic (serviceTimeouts setup mode duration)) leaks focal final)),
              (bindingTraffic (serviceTimeouts setup mode duration)) leaks focal final)) =
      ((prior.map source).bind fun config =>
        (L.evalDist distribution (sourcePublicEnv config.state)).map
          (sampleSuccessor name config)).bind fun config =>
          (nextNoise (config.view focal)).map fun traffic => (config, traffic) := by
  let app := serviceApplication setup mode duration leaks
  let read := fun seed => (bindingTraffic (serviceTimeouts setup mode duration)) leaks focal
    (execution seed)
  let phase := fun seed => (app.runUntilHorizon scheduler (focalPlayers setup leaks focal deviation)
    (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)).map
      ((bindingTraffic (serviceTimeouts setup mode duration)) leaks focal)
  obtain ⟨channel, channelLaw⟩ := exists_updated_observation_kernel_of_readout prior source read
    (fun config => config.view focal) noise factor
    (fun _ => PMF.pure ()) (fun config _ => config) (fun config => config.view focal)
    (fun seed _ => phase seed)
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left leftSupport _ _ right rightSupport _ _ _ same => by
      have recalled := congrArg (fun traffic => traffic.2.2.1) same
      change (execution left).environmentRecall = (execution right).environmentRecall at recalled
      simp only [phase, ReactiveApplication.runUntilHorizon, recalled]
      exact focalPhase_traffic_congr scheduler focal deviation (Or.inl ownerless) alone
        (horizon - (execution right).environmentRecall.length)
        (execution left) (execution right) (ready left leftSupport) (ready right rightSupport) same)
  have joint : (prior.bind fun seed => (phase seed).map fun traffic => (source seed, traffic)) =
      (prior.map source).bind fun config =>
        (channel (config.view focal)).map fun traffic => (config, traffic) := by
    simpa only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure] using channelLaw
  let choice := fun view => (channel view).map pick
  let nextNoise := fun view : DecisionView focal ((name, .publicData payload) :: Γ) =>
    fiberPosterior (channel (view.back false)) pick (view.observation.cells.get .here)
  have factored :
      (prior.bind fun seed => (phase seed).map fun traffic =>
        (sampleSuccessor name (source seed) (pick traffic), traffic)) =
      ((prior.map source).bind fun config =>
        (choice (config.view focal)).map (sampleSuccessor name config)).bind fun config =>
          (nextNoise (config.view focal)).map fun traffic => (config, traffic) := by
    calc
      _ = (prior.bind fun seed => (phase seed).map fun traffic => (source seed, traffic)).map
          (fun pair => (sampleSuccessor name pair.1 (pick pair.2), pair.2)) := by
        simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      _ = ((prior.map source).bind fun config =>
          (channel (config.view focal)).map fun traffic => (config, traffic)).map
            (fun pair => (sampleSuccessor name pair.1 (pick pair.2), pair.2)) := by rw [joint]
      _ = _ := by
        simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_bind, PMF.bind_map]
        apply bind_congr_on_support _
        intro seed _supported
        rw [map_readout_choice (channel ((source seed).view focal)) pick
          (fun value traffic => (sampleSuccessor name (source seed) value, traffic))]
        apply bind_congr_on_support _
        intro value _chosen
        have backed := back_sample_view focal name (source seed) value
        dsimp only [nextNoise]
        rw [backed]
        rfl
  have projected := congrArg (PMF.map Prod.fst) factored
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_fun_const,
    PMF.bind_pure] at projected
  have marginal : (prior.bind fun seed => (phase seed).map
      (fun traffic => sampleSuccessor name (source seed) (pick traffic))) =
      (prior.map source).bind fun config =>
        (L.evalDist distribution (sourcePublicEnv config.state)).map
          (sampleSuccessor name config) := by
    rw [PMF.bind_map]
    apply bind_congr_on_support _
    intro seed supported
    have actual := congrArg (PMF.map (sampleSuccessor name (source seed))) (sampled seed supported)
    simpa only [phase, PMF.map_comp, Function.comp_def] using actual
  refine ⟨nextNoise, ?_⟩
  rw [← projected, marginal] at factored
  simpa only [phase, PMF.map_bind, PMF.map_comp, Function.comp_def] using factored


private theorem path_store_value {compiled : Vegas.EventGraph Player L}
    {before after : compiled.Config} (path : Relation.ReflTransGen Config.Step before after)
    (field : compiled.Field) (value : (compiled.layout field).Value)
    (stored : before.store field = some value) : after.store field = some value := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact stored
  | @head first middle moved _ ih =>
      obtain ⟨event, ready, action, supported⟩ := moved
      exact ih (first.step_store_of_some middle event ready action supported field value stored)

/-- Public chance has its source successor law jointly with the focal native
traffic. Each stopped endpoint is a typed primary checkpoint followed by drain. -/
theorem sourceService_chance_law
    {setup : Setup (Player := Player) (L := L)}
    (timeouts : EventTimeouts (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}
    (complete : CompletesPlay timeouts leaks (initialLaw setup) horizon scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    (focal : Player) (deviation : (application setup timeouts leaks).Policy)
    {Seed : Type} {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (distribution : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) openNames)
    (profile : BehavioralProfile (.sample name fresh distribution next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.sample name fresh distribution next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup timeouts leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.sample name fresh distribution next) profile refs (source seed).revelations
      (source seed).registry embedding refsBefore rank)
    (checkpoint : ∀ seed, SourceCheckpoint setup (source seed) refs rank
      (execution seed).application.config)
    (boundary : ∀ seed ∈ prior.support, CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup .sequential timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) rank (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => (source seed, (bindingTraffic timeouts) leaks focal
      (execution seed))) = (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun traffic => (config, traffic)) :
    let index : Fin (eventCount (.sample name fresh distribution next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let outputEq : (graph setup).outputLayout event = .publicData payload :=
      by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    let sampleRef : FieldRef (graphLayout setup.program) (.publicData payload) :=
      ⟨.inr event, outputEq⟩
    let players := Function.update
      (serviceTurnPolicy setup .sequential timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation
    let readChoice := fun final : (application setup timeouts leaks).Execution =>
      ((final.application.config.outputs event).map
        (cast (congrArg EventField.Value outputEq))).getD (L.someValue payload)
    ∃ nextNoise : DecisionView focal ((name, .publicData payload) :: Γ) → PMF _,
      ((prior.bind fun seed =>
        ((application setup timeouts leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            (sampleSuccessor name (source seed) (readChoice final),
              (bindingTraffic timeouts) leaks focal final)) =
        ((prior.map source).bind fun config =>
          (L.evalDist distribution (sourcePublicEnv config.state)).map
            (sampleSuccessor name config)).bind fun config =>
              (nextNoise (config.view focal)).map (fun traffic => (config, traffic))) ∧
      ∀ seed ∈ prior.support, ∀ final ∈
          ((application setup timeouts leaks).runUntilHorizon scheduler players
            (fun current => event ∈ current.application.config.cut.completed) horizon
            (execution seed)).support,
        ∃ (value : L.Val payload) (native : EventGraphRuntime.State (graph setup)),
          SourceCheckpoint setup (sampleSuccessor name (source seed) value)
            (refs.cons (name := name) sampleRef) (rank + 1) native.config ∧
          final.application.config = native.drain.config ∧ readChoice final = value := by
  intro index event outputEq sampleRef players readChoice
  let app := application setup timeouts leaks
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have ownerless : (graph setup).actor? event = none := by
    change (toEventGraph setup.program).actor? event = none
    simpa [event, index, eventOwner?, eventCount] using
      (aligned prior.support_nonempty.choose).actorEq index
  have codeEq (seed : Seed) :
      cast (congrArg (EventCode (graph setup).layout) outputEq) ((graph setup).nodes event) =
        .sample payload (compilePublicDist refs distribution) := by
    change cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using (aligned seed).graphSuffix.nodeEq index
  have decodedAction : decodeEventAction setup.program event
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit) = none := by
    have lookup := (aligned prior.support_nonempty.choose).actionEq index
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
    simpa [event, index, outputEq, decodeEventAction] using lookup
  have readyAt (seed : Seed) (supported : seed ∈ prior.support) :
      (execution seed).application.config.cut.Ready event := by
    have ordered := (boundary seed supported).ordered
    rw [← eventRank] at ordered
    exact ordered.ready event.isLt
  have alone : ∀ (cut : (graph setup).order.Cut) other,
      cut.Ready event → cut.Ready other → other = event := by
    intro cut other ready otherReady
    exact setup.eventGraph.sequentialize_ready_unique cut otherReady ready
  have phaseEq (seed : Seed) (supported : seed ∈ prior.support) :
      app.runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed) =
      app.runUntilHorizon scheduler (focalPlayers setup leaks focal deviation)
        (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed) :=
    runUntil_deviation_focal scheduler bound turns wholeProfile focal deviation event
      (Or.inl ownerless) alone _ (execution seed) (fun _ => readyAt seed supported)
  have completed (seed : Seed) (supported : seed ∈ prior.support)
      (final : app.Execution)
      (reached : final ∈ (app.runUntilHorizon scheduler players
        (fun current => event ∈ current.application.config.cut.completed) horizon
        (execution seed)).support) : event ∈ final.application.config.cut.completed := by
    obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players _
      (bounded seed supported) _ (boundary seed supported).supported
    let remaining := horizon - (execution seed).environmentRecall.length
    change final ∈ (app.runUntil scheduler players
      (fun current => event ∈ current.application.config.cut.completed) remaining
      (execution seed)).support at reached
    rcases app.runUntil_stopped scheduler players _ remaining (execution seed) final reached
        with done | spent
    · exact done
    · obtain ⟨used, enough, rounds, _lengthEq⟩ := app.runUntil_runRounds scheduler players _
        remaining (execution seed) final reached
      obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler players
        (remaining - used) used (execution seed) final
        (by simpa only [Nat.sub_add_cancel enough] using trace) rounds
      have terminal := complete _ finalTrace (by
        change remaining - used = 0 ∧ _
        exact ⟨by dsimp only [remaining] at *; omega, rfl⟩)
      change final.application.config.cut.completed = Finset.univ at terminal
      rw [terminal]
      exact Finset.mem_univ _
  have sampled (seed : Seed) (supported : seed ∈ prior.support) :
      (app.runUntilHorizon scheduler (focalPlayers setup leaks focal deviation)
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).map (fun final => sampledTrafficValue setup leaks event outputEq
          ((bindingTraffic timeouts) leaks focal final)) =
      L.evalDist distribution (sourcePublicEnv (source seed).state) := by
    rw [← phaseEq seed supported]
    have pointwise (final : app.Execution) :
        sampledTrafficValue setup leaks event outputEq ((bindingTraffic timeouts) leaks focal
          final) =
          sampledValue event outputEq final.application.config :=
      sampledTrafficValue_eq setup (mode := .sequential) (duration := timeouts.duration)
        leaks focal event outputEq final
    simp_rw [pointwise]
    exact chance_completed_value_law timeouts leaks (compileEventProfile setup.program wholeProfile)
      scheduler players event ownerless _ (execution seed) (readyAt seed supported) outputEq refs
      distribution (codeEq seed) (source seed).state (checkpoint seed).agrees
      (completed seed supported)
  obtain ⟨nextNoise, joint⟩ := primary_sample_joint_of_marginal name distribution setup leaks
    scheduler focal deviation event ownerless alone horizon prior source execution
    (sampledTrafficValue setup leaks event outputEq) noise factor
    (fun seed supported _ => readyAt seed supported) sampled
  refine ⟨nextNoise, ?_, ?_⟩
  · calc
      _ = prior.bind (fun seed => (app.runUntilHorizon scheduler
          (focalPlayers setup leaks focal deviation)
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            (sampleSuccessor name (source seed) (readChoice final),
              (bindingTraffic timeouts) leaks focal final)) := by
        apply bind_congr_on_support _
        intro seed supported
        rw [phaseEq seed supported]
      _ = _ := by simpa only [sampledTrafficValue_eq, sampledValue] using joint
  · intro seed supported final reached
    have ready := readyAt seed supported
    have quiescent : ∀ query, ¬ (execution seed).application.AutomaticReady query := by
      intro query eligible
      cases alone _ query ready eligible.1
      obtain ⟨owner, acting, _inactive⟩ := eligible.owned
      rw [ownerless] at acting
      cases acting
    obtain ⟨action, native, primary, drained⟩ := runUntil_completed_primary_drain timeouts leaks
      scheduler players event _ (execution seed) final ready
      (fun query queryReady => alone _ query ready queryReady) quiescent reached
      (completed seed supported final reached)
    have actionEq : action = cast (congrArg EventField.Action outputEq.symm) PUnit.unit :=
      ((graph setup).nodes event).action_eq_of_actor_none ownerless action _
    rw [actionEq, sample_step (execution seed).application.config event ready outputEq refs
      distribution (codeEq seed) (source seed).state (checkpoint seed).agrees,
      PMF.support_map] at primary
    obtain ⟨value, _drawn, configEq⟩ := primary
    have nextCheckpoint := (checkpoint seed).sample name event eventRank ready outputEq
      (fun ref => refsBefore ref index) decodedAction value
    change SourceCheckpoint setup _ _ (rank + 1)
      ((execution seed).application.config.complete event ready _ _) at nextCheckpoint
    have checked : SourceCheckpoint setup (sampleSuccessor name (source seed) value)
        (refs.cons (name := name) sampleRef) (rank + 1) native.config :=
      Eq.mp (congrArg (fun config : (graph setup).Config =>
        SourceCheckpoint (mode := .sequential) setup (sampleSuccessor name (source seed) value)
          (refs.cons (name := name) sampleRef) (rank + 1) config) configEq) nextCheckpoint
    refine ⟨value, native, checked, drained, ?_⟩
    have stored : native.config.store (.inr event) =
        some (cast (congrArg EventField.Value outputEq.symm) value) := by
      rw [← configEq]
      exact Function.update_self ..
    have retained := path_store_value native.drain_graph_steps (.inr event) _ stored
    change native.drain.config.outputs event = _ at retained
    dsimp only [readChoice]
    rw [drained, retained]
    simp only [Option.map_some, cast_cast, cast_eq, Option.getD_some]

variable {setup : Setup (Player := Player) (L := L)}

omit [IExpr.ResultTypes L] in
private theorem binding_admission_reflects
    {Γ : SourceCtx Player L} {owner focal : Player} {payload : L.Ty}
    (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (left right : Config Player L Γ)
    (leftChoice rightChoice : Option (PublicationResult (L.Val payload)))
    (leftActive : owner ∉ left.defaulted) (rightActive : owner ∉ right.defaulted)
    (same : (commitSuccessor name guard left leftChoice).view focal =
      (commitSuccessor name guard right rightChoice).view focal) :
    leftChoice.isSome = rightChoice.isSome := by
  have newest := congrArg
    (fun view : DecisionView focal ((name, .commitment owner payload) :: Γ) =>
      view.defaults.events.head?) same
  cases leftChoice <;> cases rightChoice <;>
    simp_all [Config.view, commitSuccessor, DefaultHistory.record]

private theorem effective_supported_result
    {Γ : SourceCtx Player L} {names : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ names)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (names.erase name))
    (profile : BehavioralProfile (.reveal published owner name fresh selected unresolved next))
    (config : Config Player L Γ) (active : owner ∉ config.defaulted)
    (effective : (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh selected unresolved next) config.registry
      config.revelations)
    (chosen : true ∈ (revealKernel profile (config.view owner) active).support) :
    ∃ value, disclosureResult published selected config true = .success value := by
  have supported : true ∈ ((profile owner).1 rfl (config.view owner) active).support := chosen
  have fixed := effective.1 rfl (config.view owner) active true supported
  rw [effectiveDisclosureView_observe] at fixed
  cases evaluated : disclosureResult published selected config true with
  | failure =>
      simp only [effectiveDisclosure, evaluated] at fixed
      cases fixed
  | success value => exact ⟨value, rfl⟩


private theorem foreign_binding_callback
    (timeouts : EventTimeouts (graph setup))
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
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile refs source.revelations source.registry
      embedding refsBefore rank)
    (execution : (application setup timeouts leaks).Execution)
    (checkpoint : SourceCheckpoint setup source refs rank execution.application.config)
    (active : owner ∉ source.defaulted)
    :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let outputEq : (graph setup).outputLayout event = .binding owner payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    ∀ current : (application setup timeouts leaks).Execution,
      current.application.config = execution.application.config →
      sourceServiceCanonicalPolicy setup timeouts leaks wholeProfile owner (current.logs owner)
          (current.observe (application setup timeouts leaks) owner) =
        (commitKernel profile (source.view owner) active).map (fun choice =>
          (canonicalServiceDecision timeouts) leaks owner (current.logs owner)
            (current.observe (application setup timeouts leaks) owner) event
              (cast (congrArg EventField.Action outputEq.symm) choice)) := by
  intro index event outputEq current same
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have ready : current.application.config.cut.Ready event := by
    rw [same]
    have ordered := checkpoint.ordered
    rw [← eventRank] at ordered
    exact ordered.ready event.isLt
  have law := sourceServiceCanonicalPolicy_commit setup leaks fresh guard next wholeProfile
    profile refs source embedding refsBefore rank aligned current
    (by rw [same]; exact checkpoint.agrees) (by rw [same]; exact checkpoint.history)
    (by rw [same]; exact checkpoint.defaults) ready
  simpa only [active, dite_false] using law

private theorem foreign_binding_fixed_endpoint
    (timeouts : EventTimeouts (graph setup))
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
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile refs source.revelations source.registry
      embedding refsBefore rank)
    (execution : (application setup timeouts leaks).Execution)
    (checkpoint : SourceCheckpoint setup source refs rank execution.application.config)
    (active : owner ∉ source.defaulted)
    {horizon : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : (graph setup).EventId → Nat) (turns : Nat)
    (contract : AsyncContract timeouts leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (focal : Player) (deviation : (application setup timeouts leaks).Policy)
    (foreign : owner ≠ focal)
    (boundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup .sequential timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) rank execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (choice : Option (PublicationResult (L.Val payload))) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let outputEq : (graph setup).outputLayout event = .binding owner payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    let action := cast (congrArg EventField.Action outputEq.symm) choice
    let fixed := Function.update (focalPlayers setup leaks focal deviation) owner
      (decidedTurnPolicy setup leaks bound owner event action)
    let readChoice := fun final : (application setup timeouts leaks).Execution =>
      OwnAction.binding owner name payload
        ((final.application.config.history.find?
          (fun record => decide (record.event = event))).bind
          fun record => record.decision.bind (decodeEventAction setup.program record.event))
    ∀ final ∈ ((application setup timeouts leaks).runUntilHorizon scheduler fixed
        (fun current => event ∈ current.application.config.cut.completed) horizon
        execution).support,
      ∃ native : EventGraphRuntime.State (graph setup),
        SourceCheckpoint setup (commitSuccessor name guard source choice)
          (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1) native.config ∧
        final.application.config = native.drain.config ∧ readChoice final = choice := by
  intro index event outputEq action fixed readChoice
  let app := application setup timeouts leaks
  let baseline := serviceTurnPolicy setup .sequential timeouts.duration leaks bound turns
    (firstTurnTiming setup turns) wholeProfile
  let background := Function.update baseline focal deviation
  let member := fun past view =>
    if serviceTurn setup .sequential timeouts.duration leaks owner event past view = some 0 then
      decidedOpportunity setup leaks bound owner event action past view
    else baseline owner past view
  let patched := Function.update background owner member
  let reference : (graph setup).BehavioralProfile := compileEventProfile setup.program wholeProfile
  let plan := (graph setup).policyPlan reference (graph setup).canonicalScheduler
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  have codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload := by
    change cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have decodedAction : decodeEventAction setup.program event action =
      some (.commit owner name payload choice) := by
    have lookup := aligned.actionEq index action
    simpa [action, event, index, outputEq, decodeEventAction] using lookup
  have boundaryAt : CompletionBoundary setup leaks scheduler background event.val execution := by
    rw [eventRank]
    exact boundary
  have ready : execution.application.config.cut.Ready event :=
    boundaryAt.ordered.ready event.isLt
  have nativeActive : owner ∉ execution.application.config.defaulted := by
    have status : execution.application.config.defaulted = source.defaulted :=
      congrArg DefaultHistory.defaulted checkpoint.defaults
    rw [status]
    exact active
  have effective : EffectiveAction execution.application.config event action := by
    unfold EffectiveAction
    rw [nodeView_eq_bind outputEq codeEq]
    trivial
  have follows : background owner = baseline owner := Function.update_of_ne foreign _ _
  have continuation := sourceService_fixedAction_continuation timeouts leaks scheduler delay bound
    wholeProfile reference contract timely owner event owned background follows action execution
    boundaryAt bounded effective
  have runEq := sourceService_foreign_fixedRun (horizon := horizon) timeouts leaks scheduler bound
    turns wholeProfile
    focal deviation owner event owned action execution ready
  change app.runUntilHorizon scheduler patched _ horizon execution =
    app.runUntilHorizon scheduler fixed _ horizon execution at runEq
  have law : (app.runUntilHorizon scheduler fixed
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
        (fun final => (graph setup).runPlan plan final.application.config.remaining
          final.application.config) =
      (execution.application.config.step event ready action).bind
        (fun config => (graph setup).runPlan plan config.remaining config) := by
    rw [← runEq]
    exact continuation
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler background _
    bounded execution boundaryAt.supported
  have quiescent := (legalFacts setup leaks horizon scheduler _ trace).quiescent
  have completeAfter : ∀ final ∈ (app.runUntilHorizon scheduler fixed
      (fun current => event ∈ current.application.config.cut.completed) horizon execution).support,
      event ∈ final.application.config.cut.completed := by
    intro final reached
    let remaining := horizon - execution.environmentRecall.length
    change final ∈ (app.runUntil scheduler fixed
      (fun current => event ∈ current.application.config.cut.completed) remaining
      execution).support at reached
    rcases app.runUntil_stopped scheduler fixed _ remaining execution final reached
        with done | spent
    · exact done
    · obtain ⟨used, enough, rounds, _length⟩ := app.runUntil_runRounds scheduler fixed _
        remaining execution final reached
      obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler fixed
        (remaining - used) used execution final
        (by simpa only [Nat.sub_add_cancel enough] using trace) rounds
      have terminal := contract.completes _ finalTrace (by
        change remaining - used = 0 ∧ _
        exact ⟨by dsimp only [remaining] at *; omega, rfl⟩)
      change final.application.config.cut.completed = Finset.univ at terminal
      rw [terminal]
      exact Finset.mem_univ _
  intro final reached
  obtain ⟨native, primary, drained⟩ := runUntil_fixed_primary_drain timeouts leaks scheduler fixed
    event (horizon - execution.environmentRecall.length) execution ready
    (fun other otherReady => setup.eventGraph.sequentialize_ready_unique _ otherReady ready)
    owner owned nativeActive quiescent action plan law completeAfter final reached
  have status : execution.application.config.defaulted = source.defaulted :=
    congrArg DefaultHistory.defaulted checkpoint.defaults
  have stepLaw := commit_step execution.application.config event ready outputEq codeEq choice
  have stepLaw' : execution.application.config.step event ready action =
      PMF.pure (execution.application.config.complete event ready action
        (cast (congrArg EventField.Value outputEq.symm)
          ((commitSuccessor name guard source choice).state.get .here))) := by
    simpa only [action, status, commitSuccessor, Env.get, Env.cons] using stepLaw
  have configEq : native.config = execution.application.config.complete event ready action
      (cast (congrArg EventField.Value outputEq.symm)
        ((commitSuccessor name guard source choice).state.get .here)) := by
    rw [stepLaw', PMF.mem_support_pure_iff] at primary
    exact primary
  have nextCheckpoint := checkpoint.commit name guard event eventRank ready outputEq
    (fun ref => refsBefore ref index) choice decodedAction
  have typed : SourceCheckpoint setup (commitSuccessor name guard source choice)
      (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1) native.config := by
    rw [configEq]
    exact nextCheckpoint
  refine ⟨native, typed, drained, ?_⟩
  obtain ⟨value, _output, history⟩ := execution.application.config.step_completion event ready
    action native.config primary
  rw [execution.application.config.actualDecision_of_active event owner owned nativeActive action]
    at history
  have absent : execution.application.config.history.find?
      (fun record => decide (record.event = event)) = none := by
    apply List.find?_eq_none.mpr
    intro record present matching
    have eventEq : record.event = event := of_decide_eq_true matching
    have completed : event ∈ execution.application.config.cut.completed :=
      (execution.application.config.history_exact event).mp
        (List.mem_map.mpr ⟨record, present, eventEq⟩)
    exact ready.1 completed
  have nativeFind : native.config.history.find? (fun record => decide (record.event = event)) =
      some (EventGraph.completion (graph setup) event (some action) value) := by
    rw [history, List.find?_append, absent]
    simp [EventGraph.completion]
  obtain ⟨extra, growth⟩ := EventGraph.Config.Step.path_history_prefix native.drain_graph_steps
  have finalFind : final.application.config.history.find?
      (fun record => decide (record.event = event)) =
        some (EventGraph.completion (graph setup) event (some action) value) := by
    rw [drained, ← growth, List.find?_append, nativeFind]
    rfl
  simp only [readChoice, finalFind, Option.bind_some, EventGraph.completion, decodedAction,
    OwnAction.binding_commit]


private theorem binding_joint_mixed
    (timeouts : EventTimeouts (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Seed : Type} {horizon : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (focal owner : Player)
    (deviation : (application setup timeouts leaks).Policy) (foreign : owner ≠ focal)
    {Γ : SourceCtx Player L} {name : VarId} {payload : L.Ty}
    (guard : SourceGuard L Γ owner name payload) (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup timeouts leaks).Execution)
    (boundary : ∀ seed ∈ prior.support, owner ∉ (source seed).defaulted →
      CompletionBoundary setup leaks scheduler
        (Function.update (serviceTurnPolicy setup .sequential timeouts.duration leaks bound turns
          (firstTurnTiming setup turns) wholeProfile) focal deviation) event.val (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => (source seed, (bindingTraffic timeouts) leaks focal
      (execution seed))) = (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun traffic => (config, traffic))
    (choice : Config Player L Γ → PMF (Option (PublicationResult (L.Val payload)))) :
    let phase := fun seed decision =>
      if owner ∈ (source seed).defaulted then PMF.pure (execution seed)
      else (application setup timeouts leaks).runUntilHorizon scheduler
        (Function.update (focalPlayers setup leaks focal deviation) owner
          (decidedTurnPolicy setup leaks bound owner event
            (cast (congrArg EventField.Action outputEq.symm) decision)))
        (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
    ∃ nextNoise : DecisionView focal ((name, .commitment owner payload) :: Γ) → PMF _,
      (prior.bind fun seed => (choice (source seed)).bind fun decision =>
        ((phase seed decision).map fun final =>
          (commitSuccessor name guard (source seed) decision,
            (bindingTraffic timeouts) leaks focal final))) =
      ((prior.map source).bind fun config =>
        (choice config).map (commitSuccessor name guard config)).bind fun config =>
          (nextNoise (config.view focal)).map fun traffic => (config, traffic) := by
  intro phase
  let step := fun seed decision => (phase seed decision).map ((bindingTraffic timeouts) leaks focal)
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior source
    (fun seed => (bindingTraffic timeouts) leaks focal (execution seed))
    (fun config => config.view focal) noise factor choice (commitSuccessor name guard)
    (fun config => config.view focal) step
    (fun left _ leftChoice _ right _ rightChoice _ same => by
      have backed := congrArg (DecisionView.back (decide (owner = focal))) same
      simpa only [back_commit_view] using backed)
    (fun left leftSupport leftChoice _ right rightSupport rightChoice _ same traffic => by
      have backed := congrArg (DecisionView.back (decide (owner = focal))) same
      simp only [back_commit_view] at backed
      have defaults : (source left).defaulted = (source right).defaulted :=
        congrArg DecisionView.defaulted backed
      by_cases inactive : owner ∈ (source left).defaulted
      · have rightInactive : owner ∈ (source right).defaulted := defaults ▸ inactive
        simp only [step, phase, inactive, rightInactive, ite_true, PMF.pure_map, traffic]
      · have rightActive : owner ∉ (source right).defaulted := defaults ▸ inactive
        simp only [step, phase, inactive, rightActive, ite_false]
        have admitted := binding_admission_reflects name guard (source left) (source right)
          leftChoice rightChoice inactive rightActive same
        exact sourceService_binding_traffic_congr timeouts leaks scheduler bound turns wholeProfile
          focal owner deviation foreign event outputEq codeEq node leftChoice rightChoice admitted
          (execution left) (execution right) (boundary left leftSupport inactive)
          (boundary right rightSupport rightActive) (bounded left leftSupport)
          (bounded right rightSupport) traffic)
  exact ⟨nextNoise, by simpa only [step, PMF.map_comp, Function.comp_def] using law⟩

/-- An honest foreign binding retains its prescribed source kernel jointly with
actual focal traffic, including source heads already passed by automatic service. -/
theorem sourceService_foreign_commit_law
    (timeouts : EventTimeouts (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}
    (delay bound : (graph setup).EventId → Nat) (turns : Nat)
    (contract : AsyncContract timeouts leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (wholeProfile : BehavioralProfile setup.program) (focal owner : Player)
    (deviation : (application setup timeouts leaks).Policy) (foreign : owner ≠ focal)
    {Seed : Type} {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup timeouts leaks).Execution)
    (ghost : Seed → EventGraphRuntime.State (graph setup))
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile refs (source seed).revelations
      (source seed).registry embedding refsBefore rank)
    (checkpoint : ∀ seed, SourceCheckpoint setup (source seed) refs rank (ghost seed).config)
    (lag : ∀ seed ∈ prior.support, ∃ caught : EventGraphRuntime.State (graph setup),
      Relation.ReflTransGen EventGraphRuntime.State.AutomaticStep (ghost seed) caught ∧
        caught.config = (execution seed).application.config)
    (boundary : ∀ seed ∈ prior.support, ∃ physicalRank, CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup .sequential timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) physicalRank (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => (source seed, (bindingTraffic timeouts) leaks focal
      (execution seed))) = (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun traffic => (config, traffic)) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let outputEq : (graph setup).outputLayout event = .binding owner payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    let bindingRef : FieldRef (graphLayout setup.program) (.binding owner payload) :=
      ⟨.inr event, outputEq⟩
    let players := Function.update
      (serviceTurnPolicy setup .sequential timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation
    let readChoice := fun final : (application setup timeouts leaks).Execution =>
      OwnAction.binding owner name payload
        ((final.application.config.history.find? (fun record => decide (record.event = event))).bind
          fun record => record.decision.bind (decodeEventAction setup.program record.event))
    let kernel := fun config : Config Player L Γ =>
      if inactive : owner ∈ config.defaulted then PMF.pure none
      else commitKernel profile (config.view owner) inactive
    ∃ nextNoise : DecisionView focal ((name, .commitment owner payload) :: Γ) → PMF _,
      ((prior.bind fun seed =>
        ((application setup timeouts leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            (commitSuccessor name guard (source seed) (readChoice final),
              (bindingTraffic timeouts) leaks focal final)) =
        ((prior.map source).bind fun config =>
          (kernel config).map (commitSuccessor name guard config)).bind fun config =>
            (nextNoise (config.view focal)).map (fun traffic => (config, traffic))) ∧
      ∀ seed ∈ prior.support, ∀ final ∈
          ((application setup timeouts leaks).runUntilHorizon scheduler players
            (fun current => event ∈ current.application.config.cut.completed) horizon
            (execution seed)).support,
        ∃ (choice : Option (PublicationResult (L.Val payload)))
          (native : EventGraphRuntime.State (graph setup)),
          SourceCheckpoint setup (commitSuccessor name guard (source seed) choice)
            (refs.cons (name := name) bindingRef) (rank + 1) native.config ∧
          (∃ caught : EventGraphRuntime.State (graph setup),
            Relation.ReflTransGen EventGraphRuntime.State.AutomaticStep native caught ∧
              caught.config = final.application.config) ∧
          (owner ∉ (source seed).defaulted → final.application.config = native.drain.config) ∧
          readChoice final = choice := by
  intro index event outputEq bindingRef players readChoice kernel
  let app := application setup timeouts leaks
  let fixed := fun choice => Function.update (focalPlayers setup leaks focal deviation) owner
    (decidedTurnPolicy setup leaks bound owner event
      (cast (congrArg EventField.Action outputEq.symm) choice))
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using
      (aligned prior.support_nonempty.choose).actorEq index
  have codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload := by
    change cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using
      (aligned prior.support_nonempty.choose).graphSuffix.nodeEq index
  have decodedAction (choice : Option (PublicationResult (L.Val payload))) :
      decodeEventAction setup.program event
        (cast (congrArg EventField.Action outputEq.symm) choice) =
      some (.commit owner name payload choice) := by
    have lookup := (aligned prior.support_nonempty.choose).actionEq index
      (cast (congrArg EventField.Action outputEq.symm) choice)
    simpa [event, index, outputEq, decodeEventAction] using lookup
  have alone : ∀ (cut : (graph setup).order.Cut) other,
      cut.Ready event → cut.Ready other → other = event := by
    intro cut other ready otherReady
    exact setup.eventGraph.sequentialize_ready_unique cut otherReady ready
  have ghostReady (seed : Seed) : (ghost seed).config.cut.Ready event := by
    have ordered := (checkpoint seed).ordered
    rw [← eventRank] at ordered
    exact ordered.ready event.isLt
  have traceAt (seed : Seed) (supported : seed ∈ prior.support) :
      Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨horizon - (execution seed).environmentRecall.length, none, execution seed⟩)) := by
    obtain ⟨physicalRank, physical⟩ := boundary seed supported
    exact app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players _
      (bounded seed supported) _ physical.supported
  have quiescentAt (seed : Seed) (supported : seed ∈ prior.support) :
      ∀ query, ¬ (execution seed).application.AutomaticReady query := by
    obtain ⟨trace⟩ := traceAt seed supported
    exact (legalFacts setup leaks horizon scheduler _ trace).quiescent
  have pendingConfig (seed : Seed) (supported : seed ∈ prior.support)
      (pending : event ∉ (execution seed).application.config.cut.completed) :
      (execution seed).application.config = (ghost seed).config := by
    obtain ⟨caught, path, same⟩ := lag seed supported
    have unchanged := EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
      (fun other otherReady => alone _ other (ghostReady seed) otherReady)
      (by simpa only [same] using pending)
      (EventGraphRuntime.State.automatic_path_graph_steps path)
    exact same.symm.trans unchanged
  have activeConfig (seed : Seed) (supported : seed ∈ prior.support)
      (active : owner ∉ (source seed).defaulted) :
      (execution seed).application.config = (ghost seed).config := by
    obtain ⟨caught, path, same⟩ := lag seed supported
    have quiet : ∀ query, ¬ (ghost seed).AutomaticReady query := by
      intro query eligible
      cases alone _ query (ghostReady seed) eligible.1
      have status : (ghost seed).config.defaulted = (source seed).defaulted :=
        congrArg DefaultHistory.defaulted (checkpoint seed).defaults
      have inactive := eligible.2
      rw [owned, status] at inactive
      exact active inactive
    exact same.symm.trans (congrArg EventGraphRuntime.State.config
      (EventGraphRuntime.State.automatic_path_eq_of_quiescent path quiet))
  have activeCheckpoint (seed : Seed) (supported : seed ∈ prior.support)
      (active : owner ∉ (source seed).defaulted) :
      SourceCheckpoint setup (source seed) refs rank (execution seed).application.config := by
    rw [activeConfig seed supported active]
    exact checkpoint seed
  have boundaryAt (seed : Seed) (supported : seed ∈ prior.support)
      (active : owner ∉ (source seed).defaulted) :
      CompletionBoundary setup leaks scheduler players event.val (execution seed) := by
    obtain ⟨physicalRank, physical⟩ := boundary seed supported
    have ordered : (execution seed).application.config.cut.IsPrefix rank :=
      (activeCheckpoint seed supported active).ordered
    have ranks := physical.ordered.unique ordered
    rw [eventRank, ← ranks]
    exact physical
  have inactiveCompleted (seed : Seed) (supported : seed ∈ prior.support)
      (inactive : owner ∈ (source seed).defaulted) :
      event ∈ (execution seed).application.config.cut.completed := by
    by_contra pending
    have same := pendingConfig seed supported pending
    apply quiescentAt seed supported event
    refine ⟨?_, ?_⟩
    · rw [same]
      exact ghostReady seed
    · rw [owned]
      change owner ∈ (execution seed).application.config.defaulted
      rw [same]
      have status : (ghost seed).config.defaulted = (source seed).defaulted :=
        congrArg DefaultHistory.defaulted (checkpoint seed).defaults
      rw [status]
      exact inactive
  have stopped (seed : Seed) (supported : seed ∈ prior.support)
      (inactive : owner ∈ (source seed).defaulted) :
      app.runUntilHorizon scheduler players
        (fun current => event ∈ current.application.config.cut.completed) horizon (execution seed) =
      PMF.pure (execution seed) :=
    app.runUntil_of_stop scheduler players
      (fun current => event ∈ current.application.config.cut.completed)
      (horizon - (execution seed).environmentRecall.length) (execution seed)
      (inactiveCompleted seed supported inactive)
  have activeMixture (seed : Seed) (supported : seed ∈ prior.support)
      (active : owner ∉ (source seed).defaulted) :
      app.runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed) =
      (kernel (source seed)).bind fun choice => app.runUntilHorizon scheduler (fixed choice)
        (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed) := by
    have callback := foreign_binding_callback timeouts leaks fresh guard next wholeProfile profile
      refs (source seed) embedding refsBefore rank (aligned seed) (execution seed)
      (activeCheckpoint seed supported active) active
    have mixed := sourceService_foreign_mixture timeouts leaks scheduler bound turns wholeProfile
      focal deviation owner event owned foreign (execution seed) (boundaryAt seed supported active)
      (bounded seed supported)
      ((kernel (source seed)).map (cast (congrArg EventField.Action outputEq.symm)))
      (fun current same => by
        simpa only [kernel, active, dite_false, PMF.map_comp, Function.comp_def]
          using callback current same)
    simpa only [PMF.bind_map, Function.comp_def, fixed, app, players] using mixed
  have endpoint (seed : Seed) (supported : seed ∈ prior.support)
      (active : owner ∉ (source seed).defaulted) (choice)
      (final : app.Execution) (reached : final ∈ (app.runUntilHorizon scheduler (fixed choice)
        (fun current => event ∈ current.application.config.cut.completed) horizon
        (execution seed)).support) :
      ∃ native : EventGraphRuntime.State (graph setup),
        SourceCheckpoint setup (commitSuccessor name guard (source seed) choice)
          (refs.cons (name := name) bindingRef) (rank + 1) native.config ∧
        final.application.config = native.drain.config ∧ readChoice final = choice :=
    foreign_binding_fixed_endpoint timeouts leaks fresh guard next wholeProfile profile refs
      (source seed) embedding refsBefore rank (aligned seed) (execution seed)
      (activeCheckpoint seed supported active) active scheduler delay bound turns contract timely
      focal deviation foreign (by rw [← eventRank]; exact boundaryAt seed supported active)
      (bounded seed supported) choice final reached
  obtain ⟨nextNoise, factored⟩ := binding_joint_mixed timeouts leaks scheduler bound turns
    wholeProfile focal owner deviation foreign guard event outputEq codeEq
    (nodeView_eq_bind outputEq codeEq) prior source execution boundaryAt bounded noise factor kernel
  refine ⟨nextNoise, ?_, ?_⟩
  · calc
      _ = prior.bind (fun seed => (kernel (source seed)).bind fun choice =>
          ((if owner ∈ (source seed).defaulted then PMF.pure (execution seed)
            else app.runUntilHorizon scheduler (fixed choice)
              (fun final => event ∈ final.application.config.cut.completed) horizon
              (execution seed)).map fun final =>
                (commitSuccessor name guard (source seed) choice,
                  (bindingTraffic timeouts) leaks focal final))) := by
        apply bind_congr_on_support _
        intro seed supported
        by_cases inactive : owner ∈ (source seed).defaulted
        · rw [stopped seed supported inactive]
          simp only [kernel, inactive, dite_true, ite_true, PMF.pure_bind, PMF.pure_map,
            commitSuccessor]
        · simp only [inactive, ite_false]
          rw [activeMixture seed supported inactive, PMF.map_bind]
          apply bind_congr_on_support _
          intro choice _chosen
          apply map_congr_on_support _
          intro final reached
          obtain ⟨native, _typed, _drained, picked⟩ :=
            endpoint seed supported inactive choice final reached
          rw [picked]
      _ = _ := factored
  · intro seed supported final reached
    by_cases inactive : owner ∈ (source seed).defaulted
    · rw [stopped seed supported inactive, PMF.mem_support_pure_iff] at reached
      subst final
      have status : (ghost seed).config.defaulted = (source seed).defaulted :=
        congrArg DefaultHistory.defaulted (checkpoint seed).defaults
      have eligible : (ghost seed).AutomaticReady event := by
        refine ⟨ghostReady seed, ?_⟩
        rw [owned, status]
        exact inactive
      obtain ⟨caught, path, same⟩ := lag seed supported
      have quiet : ∀ query, ¬ caught.AutomaticReady query := by
        intro query allowed
        exact quiescentAt seed supported query (by
          simpa only [EventGraphRuntime.State.AutomaticReady, same] using allowed)
      have tail := EventGraphRuntime.State.automatic_path_tail_of_quiescent path event eligible
        (fun other otherReady => alone _ other (ghostReady seed) otherReady) quiet
      have typed := (checkpoint seed).commitAutomatic name guard event eventRank eligible outputEq
        (fun ref => refsBefore ref index) codeEq (decodedAction none)
      have ignored : commitSuccessor name guard (source seed) (readChoice (execution seed)) =
          commitSuccessor name guard (source seed) none := by
        simp only [commitSuccessor, inactive, ite_true]
      refine ⟨readChoice (execution seed), (ghost seed).completeAutomatic event eligible,
        ?_, ⟨caught, tail, same⟩, fun active => (active inactive).elim, rfl⟩
      rw [ignored]
      exact typed
    · rw [activeMixture seed supported inactive, PMF.support_bind] at reached
      obtain ⟨choice, _chosen, fixedReached⟩ := Set.mem_iUnion₂.mp reached
      obtain ⟨native, typed, drained, picked⟩ :=
        endpoint seed supported inactive choice final fixedReached
      exact ⟨choice, native, typed,
        ⟨native.drain, native.drain_trace, drained.symm⟩, fun _ => drained, picked⟩

omit [IExpr.ResultTypes L] in
private theorem disclosure_binding_of_success
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (selected : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (active : owner ∉ config.defaulted) (value : L.Val payload)
    (success : disclosureResult published selected config true = .success value) :
    config.state.get selected = .success value := by
  simp only [disclosureResult, revealSuccessor, active, ↓reduceIte, Env.get, Env.cons] at success
  split at success
  · exact success
  · cases success

omit [IExpr.ResultTypes L] in
private theorem reveal_choice_reflects
    {Γ : SourceCtx Player L} {name : VarId} {owner focal : Player} {payload : L.Ty}
    (published : VarId) (selected : HasVar Γ name (.commitment owner payload))
    (left right : Config Player L Γ) (leftChoice rightChoice : Bool)
    (leftActive : owner ∉ left.defaulted) (rightActive : owner ∉ right.defaulted)
    (leftLoud : leftChoice = true → ∃ value,
      disclosureResult published selected left true = .success value)
    (rightLoud : rightChoice = true → ∃ value,
      disclosureResult published selected right true = .success value)
    (same : (revealSuccessor published selected left leftChoice).view focal =
      (revealSuccessor published selected right rightChoice).view focal) :
    leftChoice = rightChoice ∧ (leftChoice = true → ∃ value,
      left.state.get selected = .success value ∧ right.state.get selected = .success value) := by
  have output : disclosureResult published selected left leftChoice =
      disclosureResult published selected right rightChoice :=
    congrArg (fun view => view.observation.cells.get .here) same
  cases leftChoice <;> cases rightChoice
  · exact ⟨rfl, Bool.noConfusion⟩
  · obtain ⟨value, success⟩ := rightLoud rfl
    rw [disclosureResult_false, success] at output
    cases output
  · obtain ⟨value, success⟩ := leftLoud rfl
    rw [success, disclosureResult_false] at output
    cases output
  · obtain ⟨value, success⟩ := leftLoud rfl
    refine ⟨rfl, fun _ => ⟨value, ?_, ?_⟩⟩
    · exact disclosure_binding_of_success published selected left leftActive value success
    · exact disclosure_binding_of_success published selected right rightActive value
        (output.symm.trans success)

private theorem foreign_reveal_callback
    (timeouts : EventTimeouts (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next) profile refs source.revelations
      source.registry
      embedding refsBefore rank)
    (execution : (application setup timeouts leaks).Execution)
    (checkpoint : SourceCheckpoint setup source refs rank execution.application.config)
    (active : owner ∉ source.defaulted)
    :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let outputEq : (graph setup).outputLayout event = .publication payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    ∀ current : (application setup timeouts leaks).Execution,
      current.application.config = execution.application.config →
      sourceServiceCanonicalPolicy setup timeouts leaks wholeProfile owner (current.logs owner)
          (current.observe (application setup timeouts leaks) owner) =
        (revealKernel profile (source.view owner) active).map (fun choice =>
          (canonicalServiceDecision timeouts) leaks owner (current.logs owner)
            (current.observe (application setup timeouts leaks) owner) event
              (cast (congrArg EventField.Action outputEq.symm) choice)) := by
  intro index event outputEq current same
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have ready : current.application.config.cut.Ready event := by
    rw [same]
    have ordered := checkpoint.ordered
    rw [← eventRank] at ordered
    exact ordered.ready event.isLt
  have law := sourceServiceCanonicalPolicy_reveal setup leaks fresh binding unresolved next
    wholeProfile
    profile refs source embedding refsBefore rank aligned current
    (by rw [same]; exact checkpoint.agrees) (by rw [same]; exact checkpoint.history)
    (by rw [same]; exact checkpoint.defaults) ready
  simpa only [active, dite_false] using law

private theorem foreign_reveal_fixed_endpoint
    (timeouts : EventTimeouts (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next) profile refs source.revelations
      source.registry
      embedding refsBefore rank)
    (execution : (application setup timeouts leaks).Execution)
    (checkpoint : SourceCheckpoint setup source refs rank execution.application.config)
    (active : owner ∉ source.defaulted)
    (sourceEffective : (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next) source.registry
      source.revelations)
    {horizon : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : (graph setup).EventId → Nat) (turns : Nat)
    (contract : AsyncContract timeouts leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (focal : Player) (deviation : (application setup timeouts leaks).Policy)
    (foreign : owner ≠ focal)
    (boundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup .sequential timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) rank execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (choice : Bool) (chosen : choice ∈ (revealKernel profile (source.view owner) active).support) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let outputEq : (graph setup).outputLayout event = .publication payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    let action := cast (congrArg EventField.Action outputEq.symm) choice
    let fixed := Function.update (focalPlayers setup leaks focal deviation) owner
      (decidedTurnPolicy setup leaks bound owner event action)
    let readChoice := fun final : (application setup timeouts leaks).Execution =>
      OwnAction.disclosure
        ((final.application.config.history.find?
          (fun record => decide (record.event = event))).bind
          fun record => record.decision.bind (decodeEventAction setup.program record.event))
    (choice = true → ∃ value, EventCode.resolveOutput? (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      true execution.application.config.store = some (.success value)) ∧
    ∀ final ∈ ((application setup timeouts leaks).runUntilHorizon scheduler fixed
        (fun current => event ∈ current.application.config.cut.completed) horizon
        execution).support,
      ∃ native : EventGraphRuntime.State (graph setup),
        SourceCheckpoint setup (revealSuccessor published binding source choice)
          (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1) native.config ∧
        final.application.config = native.drain.config ∧ readChoice final = choice := by
  intro index event outputEq action fixed readChoice
  let app := application setup timeouts leaks
  let baseline := serviceTurnPolicy setup .sequential timeouts.duration leaks bound turns
    (firstTurnTiming setup turns) wholeProfile
  let background := Function.update baseline focal deviation
  let member := fun past view =>
    if serviceTurn setup .sequential timeouts.duration leaks owner event past view = some 0 then
      decidedOpportunity setup leaks bound owner event action past view
    else baseline owner past view
  let patched := Function.update background owner member
  let reference : (graph setup).BehavioralProfile := compileEventProfile setup.program wholeProfile
  let plan := (graph setup).policyPlan reference (graph setup).canonicalScheduler
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  have codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding) :=
      by
    change cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have decodedAction : decodeEventAction setup.program event action =
      some (.reveal owner name choice) := by
    have lookup := aligned.actionEq index action
    simpa [action, event, index, outputEq, decodeEventAction] using lookup
  have boundaryAt : CompletionBoundary setup leaks scheduler background event.val execution := by
    rw [eventRank]
    exact boundary
  have ready : execution.application.config.cut.Ready event :=
    boundaryAt.ordered.ready event.isLt
  have nativeActive : owner ∉ execution.application.config.defaulted := by
    have status : execution.application.config.defaulted = source.defaulted :=
      congrArg DefaultHistory.defaulted checkpoint.defaults
    rw [status]
    exact active
  have nativeSuccess : choice = true → ∃ value, EventCode.resolveOutput? (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      true execution.application.config.store = some (.success value) := by
    intro requested
    have trueSupported : true ∈ (revealKernel profile (source.view owner) active).support := by
      simpa only [requested] using chosen
    obtain ⟨value, success⟩ := effective_supported_result fresh binding unresolved next profile
      source active sourceEffective trueSupported
    have compiled := compileResolve_eval? (published := published) refs source.registry
      source.revelations source.state
      execution.application.config.store checkpoint.agrees binding true
    have evaluated : (EventCode.resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry
          source.revelations binding)).eval? true execution.application.config.store =
          some (PMF.pure (disclosureResult published binding source true)) := by
      simpa only [disclosureResult, revealSuccessor, active, ite_false, Env.get, Env.cons]
        using compiled
    rw [success] at evaluated
    change (EventCode.resolveOutput? (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      true execution.application.config.store).map PMF.pure = some (PMF.pure (.success value))
        at evaluated
    cases resolved : EventCode.resolveOutput? (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding)
        true execution.application.config.store with
    | none => simp only [resolved, Option.map_none, reduceCtorEq] at evaluated
    | some result =>
        rw [resolved, Option.map_some] at evaluated
        have masses : PMF.pure result = PMF.pure (.success value) := Option.some.inj evaluated
        have member : result ∈ (PMF.pure (.success value)).support := by
          rw [← masses, PMF.mem_support_pure_iff]
        have same := (PMF.mem_support_pure_iff _ _).mp member
        exact ⟨value, congrArg some same⟩
  have effective : EffectiveAction execution.application.config event action := by
    unfold EffectiveAction
    rw [nodeView_eq_resolve outputEq codeEq]
    intro requested
    have requestedTrue : choice = true := by
      simpa only [action, cast_cast, cast_eq] using requested
    obtain ⟨value, success⟩ := nativeSuccess requestedTrue
    exact ⟨value, EventCode.binding_success_of_resolve_success (graph := graph setup)
      (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      true execution.application.config.store value success⟩
  have follows : background owner = baseline owner := Function.update_of_ne foreign _ _
  have continuation := sourceService_fixedAction_continuation timeouts leaks scheduler delay bound
    wholeProfile reference contract timely owner event owned background follows action execution
    boundaryAt bounded effective
  have runEq := sourceService_foreign_fixedRun (horizon := horizon) timeouts leaks scheduler bound
    turns wholeProfile
    focal deviation owner event owned action execution ready
  change app.runUntilHorizon scheduler patched _ horizon execution =
    app.runUntilHorizon scheduler fixed _ horizon execution at runEq
  have law : (app.runUntilHorizon scheduler fixed
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
        (fun final => (graph setup).runPlan plan final.application.config.remaining
          final.application.config) =
      (execution.application.config.step event ready action).bind
        (fun config => (graph setup).runPlan plan config.remaining config) := by
    rw [← runEq]
    exact continuation
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler background _
    bounded execution boundaryAt.supported
  have quiescent := (legalFacts setup leaks horizon scheduler _ trace).quiescent
  have completeAfter : ∀ final ∈ (app.runUntilHorizon scheduler fixed
      (fun current => event ∈ current.application.config.cut.completed) horizon execution).support,
      event ∈ final.application.config.cut.completed := by
    intro final reached
    let remaining := horizon - execution.environmentRecall.length
    change final ∈ (app.runUntil scheduler fixed
      (fun current => event ∈ current.application.config.cut.completed) remaining
      execution).support at reached
    rcases app.runUntil_stopped scheduler fixed _ remaining execution final reached
        with done | spent
    · exact done
    · obtain ⟨used, enough, rounds, _length⟩ := app.runUntil_runRounds scheduler fixed _
        remaining execution final reached
      obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler fixed
        (remaining - used) used execution final
        (by simpa only [Nat.sub_add_cancel enough] using trace) rounds
      have terminal := contract.completes _ finalTrace (by
        change remaining - used = 0 ∧ _
        exact ⟨by dsimp only [remaining] at *; omega, rfl⟩)
      change final.application.config.cut.completed = Finset.univ at terminal
      rw [terminal]
      exact Finset.mem_univ _
  refine ⟨nativeSuccess, ?_⟩
  intro final reached
  obtain ⟨native, primary, drained⟩ := runUntil_fixed_primary_drain timeouts leaks scheduler fixed
    event (horizon - execution.environmentRecall.length) execution ready
    (fun other otherReady => setup.eventGraph.sequentialize_ready_unique _ otherReady ready)
    owner owned nativeActive quiescent action plan law completeAfter final reached
  have status : execution.application.config.defaulted = source.defaulted :=
    congrArg DefaultHistory.defaulted checkpoint.defaults
  have stepLaw := reveal_step execution.application.config event ready outputEq refs
    source.revelations source.registry binding codeEq source.state checkpoint.agrees choice
  have stepLaw' : execution.application.config.step event ready action =
      PMF.pure (execution.application.config.complete event ready action
        (cast (congrArg EventField.Value outputEq.symm)
          (disclosureResult published binding source choice))) := by
    simpa only [action, status, disclosureResult, revealSuccessor, Env.get, Env.cons] using stepLaw
  have configEq : native.config = execution.application.config.complete event ready action
      (cast (congrArg EventField.Value outputEq.symm)
        (disclosureResult published binding source choice)) := by
    rw [stepLaw', PMF.mem_support_pure_iff] at primary
    exact primary
  have nextCheckpoint := checkpoint.reveal published binding event eventRank ready outputEq
    (fun ref => refsBefore ref index) choice decodedAction
  have typed : SourceCheckpoint setup (revealSuccessor published binding source choice)
      (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1) native.config := by
    rw [configEq]
    exact nextCheckpoint
  refine ⟨native, typed, drained, ?_⟩
  obtain ⟨value, _output, history⟩ := execution.application.config.step_completion event ready
    action native.config primary
  rw [execution.application.config.actualDecision_of_active event owner owned nativeActive action]
    at history
  have absent : execution.application.config.history.find?
      (fun record => decide (record.event = event)) = none := by
    apply List.find?_eq_none.mpr
    intro record present matching
    have eventEq : record.event = event := of_decide_eq_true matching
    have completed : event ∈ execution.application.config.cut.completed :=
      (execution.application.config.history_exact event).mp
        (List.mem_map.mpr ⟨record, present, eventEq⟩)
    exact ready.1 completed
  have nativeFind : native.config.history.find? (fun record => decide (record.event = event)) =
      some (EventGraph.completion (graph setup) event (some action) value) := by
    rw [history, List.find?_append, absent]
    simp [EventGraph.completion]
  obtain ⟨extra, growth⟩ := EventGraph.Config.Step.path_history_prefix native.drain_graph_steps
  have finalFind : final.application.config.history.find?
      (fun record => decide (record.event = event)) =
        some (EventGraph.completion (graph setup) event (some action) value) := by
    rw [drained, ← growth, List.find?_append, nativeFind]
    rfl
  simp only [readChoice, finalFind, Option.bind_some, EventGraph.completion, decodedAction,
    OwnAction.disclosure]

private theorem reveal_joint_mixed
    (timeouts : EventTimeouts (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Seed : Type} {horizon : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (focal owner : Player)
    (deviation : (application setup timeouts leaks).Policy) (foreign : owner ≠ focal)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (checks : List (GuardCheck (graph setup).layout payload))
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding) checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get binding) checks outputEq codeEq)
    (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup timeouts leaks).Execution)
    (boundary : ∀ seed ∈ prior.support, owner ∉ (source seed).defaulted →
      CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup .sequential timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) event.val (execution seed))
    (agrees : ∀ seed ∈ prior.support, owner ∉ (source seed).defaulted →
      refs.Agrees (source seed).state (execution seed).application.config.store)
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (effective : ∀ seed ∈ prior.support, (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next) (source seed).registry
      (source seed).revelations)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => (source seed, (bindingTraffic timeouts) leaks focal
      (execution seed))) = (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun traffic => (config, traffic)) :
    let choice := fun config : Config Player L Γ =>
      if inactive : owner ∈ config.defaulted then PMF.pure false
      else revealKernel profile (config.view owner) inactive
    let phase := fun seed decision =>
      if owner ∈ (source seed).defaulted then PMF.pure (execution seed)
      else (application setup timeouts leaks).runUntilHorizon scheduler
        (Function.update (focalPlayers setup leaks focal deviation) owner
          (decidedTurnPolicy setup leaks bound owner event
            (cast (congrArg EventField.Action outputEq.symm) decision)))
        (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
    ∃ nextNoise : DecisionView focal ((published, .publication payload) :: Γ) → PMF _,
      (prior.bind fun seed => (choice (source seed)).bind fun decision =>
        ((phase seed decision).map fun final =>
          (revealSuccessor published binding (source seed) decision,
            (bindingTraffic timeouts) leaks focal final))) =
      ((prior.map source).bind fun config =>
        (choice config).map (revealSuccessor published binding config)).bind fun config =>
          (nextNoise (config.view focal)).map fun traffic => (config, traffic) := by
  intro choice phase
  let step := fun seed decision => (phase seed decision).map ((bindingTraffic timeouts) leaks focal)
  have loud (seed : Seed) (supported : seed ∈ prior.support)
      (active : owner ∉ (source seed).defaulted) (decision : Bool)
      (chosen : decision ∈ (choice (source seed)).support) (yes : decision = true) :
      ∃ value, disclosureResult published binding (source seed) true = .success value := by
    apply effective_supported_result fresh binding unresolved next profile (source seed)
      active (effective seed supported)
    simpa only [choice, active, dite_false, yes] using chosen
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior source
    (fun seed => (bindingTraffic timeouts) leaks focal (execution seed))
    (fun config => config.view focal) noise factor choice (revealSuccessor published binding)
    (fun config => config.view focal) step
    (fun left _ leftChoice _ right _ rightChoice _ same => by
      have backed := congrArg (DecisionView.back (decide (owner = focal))) same
      simpa only [back_reveal_view] using backed)
    (fun left leftSupport leftChoice leftChosen right rightSupport rightChoice rightChosen
        same traffic => by
      have backed := congrArg (DecisionView.back (decide (owner = focal))) same
      simp only [back_reveal_view] at backed
      have defaults : (source left).defaulted = (source right).defaulted :=
        congrArg DecisionView.defaulted backed
      by_cases inactive : owner ∈ (source left).defaulted
      · have rightInactive : owner ∈ (source right).defaulted := defaults ▸ inactive
        simp only [step, phase, inactive, rightInactive, ite_true, PMF.pure_map, traffic]
      · have rightActive : owner ∉ (source right).defaulted := defaults ▸ inactive
        simp only [step, phase, inactive, rightActive, ite_false]
        obtain ⟨equal, stored⟩ := reveal_choice_reflects published binding (source left)
          (source right) leftChoice rightChoice inactive rightActive
          (loud left leftSupport inactive leftChoice leftChosen)
          (loud right rightSupport rightActive rightChoice rightChosen) same
        subst rightChoice
        cases leftChoice with
        | false =>
            exact sourceService_withholding_traffic_congr timeouts leaks scheduler bound turns
              wholeProfile focal owner deviation foreign event (refs.get binding) checks outputEq
              codeEq node (execution left) (execution right) (boundary left leftSupport inactive)
              (boundary right rightSupport rightActive) (bounded left leftSupport)
              (bounded right rightSupport)
              traffic
        | true =>
            obtain ⟨value, leftStored, rightStored⟩ := stored rfl
            have leftNative : (refs.get binding).get? (execution left).application.config.store =
                some (.success value) := by
              simpa only [leftStored, cellValue] using agrees left leftSupport inactive binding
            have rightNative : (refs.get binding).get? (execution right).application.config.store =
                some (.success value) := by
              simpa only [rightStored, cellValue] using
                agrees right rightSupport rightActive binding
            exact sourceService_opening_traffic_congr timeouts leaks scheduler bound turns
              wholeProfile focal owner deviation foreign event (refs.get binding) checks outputEq
              codeEq node (execution left) (execution right) (boundary left leftSupport inactive)
              (boundary right rightSupport rightActive) (bounded left leftSupport)
              (bounded right rightSupport)
              value leftNative rightNative traffic)
  exact ⟨nextNoise, by
    simpa only [step, PMF.map_comp, Function.comp_def] using law⟩

/-- An honest foreign disclosure retains its prescribed source kernel jointly with
actual focal traffic, including source heads already passed by automatic service. -/
theorem sourceService_foreign_reveal_law
    (timeouts : EventTimeouts (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}
    (delay bound : (graph setup).EventId → Nat) (turns : Nat)
    (contract : AsyncContract timeouts leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (wholeProfile : BehavioralProfile setup.program) (focal owner : Player)
    (deviation : (application setup timeouts leaks).Policy) (foreign : owner ≠ focal)
    {Seed : Type} {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup timeouts leaks).Execution)
    (ghost : Seed → EventGraphRuntime.State (graph setup))
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next) profile refs
      (source seed).revelations (source seed).registry embedding refsBefore rank)
    (checkpoint : ∀ seed, SourceCheckpoint setup (source seed) refs rank (ghost seed).config)
    (lag : ∀ seed ∈ prior.support, ∃ caught : EventGraphRuntime.State (graph setup),
      Relation.ReflTransGen EventGraphRuntime.State.AutomaticStep (ghost seed) caught ∧
        caught.config = (execution seed).application.config)
    (boundary : ∀ seed ∈ prior.support, ∃ physicalRank, CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup .sequential timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) physicalRank (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (effective : ∀ seed ∈ prior.support, (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next) (source seed).registry
      (source seed).revelations)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => (source seed, (bindingTraffic timeouts) leaks focal
      (execution seed))) = (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun traffic => (config, traffic)) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let outputEq : (graph setup).outputLayout event = .publication payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    let publicationRef : FieldRef (graphLayout setup.program) (.publication payload) :=
      ⟨.inr event, outputEq⟩
    let players := Function.update
      (serviceTurnPolicy setup .sequential timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation
    let readChoice := fun final : (application setup timeouts leaks).Execution =>
      OwnAction.disclosure
        ((final.application.config.history.find? (fun record => decide (record.event = event))).bind
          fun record => record.decision.bind (decodeEventAction setup.program record.event))
    let kernel := fun config : Config Player L Γ =>
      if inactive : owner ∈ config.defaulted then PMF.pure false
      else revealKernel profile (config.view owner) inactive
    ∃ nextNoise : DecisionView focal ((published, .publication payload) :: Γ) → PMF _,
      ((prior.bind fun seed =>
        ((application setup timeouts leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            (revealSuccessor published binding (source seed) (readChoice final),
              (bindingTraffic timeouts) leaks focal final)) =
        ((prior.map source).bind fun config =>
          (kernel config).map (revealSuccessor published binding config)).bind fun config =>
            (nextNoise (config.view focal)).map (fun traffic => (config, traffic))) ∧
      ∀ seed ∈ prior.support, ∀ final ∈
          ((application setup timeouts leaks).runUntilHorizon scheduler players
            (fun current => event ∈ current.application.config.cut.completed) horizon
            (execution seed)).support,
        ∃ (choice : Bool)
          (native : EventGraphRuntime.State (graph setup)),
          SourceCheckpoint setup (revealSuccessor published binding (source seed) choice)
            (refs.cons (name := published) publicationRef) (rank + 1) native.config ∧
          (∃ caught : EventGraphRuntime.State (graph setup),
            Relation.ReflTransGen EventGraphRuntime.State.AutomaticStep native caught ∧
              caught.config = final.application.config) ∧
          (owner ∉ (source seed).defaulted → final.application.config = native.drain.config) ∧
          readChoice final = choice := by
  intro index event outputEq publicationRef players readChoice kernel
  let app := application setup timeouts leaks
  let fixed := fun choice => Function.update (focalPlayers setup leaks focal deviation) owner
    (decidedTurnPolicy setup leaks bound owner event
      (cast (congrArg EventField.Action outputEq.symm) choice))
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using
      (aligned prior.support_nonempty.choose).actorEq index
  have codeEq (seed : Seed) : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs (source seed).registry
          (source seed).revelations binding) := by
    change cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using (aligned seed).graphSuffix.nodeEq index
  have decodedAction (choice : Bool) :
      decodeEventAction setup.program event
        (cast (congrArg EventField.Action outputEq.symm) choice) =
      some (.reveal owner name choice) := by
    have lookup := (aligned prior.support_nonempty.choose).actionEq index
      (cast (congrArg EventField.Action outputEq.symm) choice)
    simpa [event, index, outputEq, decodeEventAction] using lookup
  have alone : ∀ (cut : (graph setup).order.Cut) other,
      cut.Ready event → cut.Ready other → other = event := by
    intro cut other ready otherReady
    exact setup.eventGraph.sequentialize_ready_unique cut otherReady ready
  have ghostReady (seed : Seed) : (ghost seed).config.cut.Ready event := by
    have ordered := (checkpoint seed).ordered
    rw [← eventRank] at ordered
    exact ordered.ready event.isLt
  have traceAt (seed : Seed) (supported : seed ∈ prior.support) :
      Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨horizon - (execution seed).environmentRecall.length, none, execution seed⟩)) := by
    obtain ⟨physicalRank, physical⟩ := boundary seed supported
    exact app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players _
      (bounded seed supported) _ physical.supported
  have quiescentAt (seed : Seed) (supported : seed ∈ prior.support) :
      ∀ query, ¬ (execution seed).application.AutomaticReady query := by
    obtain ⟨trace⟩ := traceAt seed supported
    exact (legalFacts setup leaks horizon scheduler _ trace).quiescent
  have pendingConfig (seed : Seed) (supported : seed ∈ prior.support)
      (pending : event ∉ (execution seed).application.config.cut.completed) :
      (execution seed).application.config = (ghost seed).config := by
    obtain ⟨caught, path, same⟩ := lag seed supported
    have unchanged := EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
      (fun other otherReady => alone _ other (ghostReady seed) otherReady)
      (by simpa only [same] using pending)
      (EventGraphRuntime.State.automatic_path_graph_steps path)
    exact same.symm.trans unchanged
  have activeConfig (seed : Seed) (supported : seed ∈ prior.support)
      (active : owner ∉ (source seed).defaulted) :
      (execution seed).application.config = (ghost seed).config := by
    obtain ⟨caught, path, same⟩ := lag seed supported
    have quiet : ∀ query, ¬ (ghost seed).AutomaticReady query := by
      intro query eligible
      cases alone _ query (ghostReady seed) eligible.1
      have status : (ghost seed).config.defaulted = (source seed).defaulted :=
        congrArg DefaultHistory.defaulted (checkpoint seed).defaults
      have inactive := eligible.2
      rw [owned, status] at inactive
      exact active inactive
    exact same.symm.trans (congrArg EventGraphRuntime.State.config
      (EventGraphRuntime.State.automatic_path_eq_of_quiescent path quiet))
  have activeCheckpoint (seed : Seed) (supported : seed ∈ prior.support)
      (active : owner ∉ (source seed).defaulted) :
      SourceCheckpoint setup (source seed) refs rank (execution seed).application.config := by
    rw [activeConfig seed supported active]
    exact checkpoint seed
  have boundaryAt (seed : Seed) (supported : seed ∈ prior.support)
      (active : owner ∉ (source seed).defaulted) :
      CompletionBoundary setup leaks scheduler players event.val (execution seed) := by
    obtain ⟨physicalRank, physical⟩ := boundary seed supported
    have ordered : (execution seed).application.config.cut.IsPrefix rank :=
      (activeCheckpoint seed supported active).ordered
    have ranks := physical.ordered.unique ordered
    rw [eventRank, ← ranks]
    exact physical
  have inactiveCompleted (seed : Seed) (supported : seed ∈ prior.support)
      (inactive : owner ∈ (source seed).defaulted) :
      event ∈ (execution seed).application.config.cut.completed := by
    by_contra pending
    have same := pendingConfig seed supported pending
    apply quiescentAt seed supported event
    refine ⟨?_, ?_⟩
    · rw [same]
      exact ghostReady seed
    · rw [owned]
      change owner ∈ (execution seed).application.config.defaulted
      rw [same]
      have status : (ghost seed).config.defaulted = (source seed).defaulted :=
        congrArg DefaultHistory.defaulted (checkpoint seed).defaults
      rw [status]
      exact inactive
  have stopped (seed : Seed) (supported : seed ∈ prior.support)
      (inactive : owner ∈ (source seed).defaulted) :
      app.runUntilHorizon scheduler players
        (fun current => event ∈ current.application.config.cut.completed) horizon (execution seed) =
      PMF.pure (execution seed) :=
    app.runUntil_of_stop scheduler players
      (fun current => event ∈ current.application.config.cut.completed)
      (horizon - (execution seed).environmentRecall.length) (execution seed)
      (inactiveCompleted seed supported inactive)
  have activeMixture (seed : Seed) (supported : seed ∈ prior.support)
      (active : owner ∉ (source seed).defaulted) :
      app.runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed) =
      (kernel (source seed)).bind fun choice => app.runUntilHorizon scheduler (fixed choice)
        (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed) := by
    have callback := foreign_reveal_callback timeouts leaks fresh binding unresolved next
      wholeProfile profile refs (source seed) embedding refsBefore rank (aligned seed)
      (execution seed) (activeCheckpoint seed supported active) active
    have mixed := sourceService_foreign_mixture timeouts leaks scheduler bound turns wholeProfile
      focal deviation owner event owned foreign (execution seed) (boundaryAt seed supported active)
      (bounded seed supported)
      ((kernel (source seed)).map (cast (congrArg EventField.Action outputEq.symm)))
      (fun current same => by
        simpa only [kernel, active, dite_false, PMF.map_comp, Function.comp_def]
          using callback current same)
    simpa only [PMF.bind_map, Function.comp_def, fixed, app, players] using mixed
  have endpoint (seed : Seed) (supported : seed ∈ prior.support)
      (active : owner ∉ (source seed).defaulted) (choice : Bool)
      (chosen : choice ∈ (kernel (source seed)).support)
      (final : app.Execution) (reached : final ∈ (app.runUntilHorizon scheduler (fixed choice)
        (fun current => event ∈ current.application.config.cut.completed) horizon
        (execution seed)).support) :
      ∃ native : EventGraphRuntime.State (graph setup),
        SourceCheckpoint setup (revealSuccessor published binding (source seed) choice)
          (refs.cons (name := published) publicationRef) (rank + 1) native.config ∧
        final.application.config = native.drain.config ∧ readChoice final = choice :=
    (foreign_reveal_fixed_endpoint timeouts leaks fresh binding unresolved next wholeProfile profile
      refs (source seed) embedding refsBefore rank (aligned seed) (execution seed)
      (activeCheckpoint seed supported active) active (effective seed supported) scheduler delay
      bound turns contract timely focal deviation foreign
      (by rw [← eventRank]; exact boundaryAt seed supported active) (bounded seed supported) choice
      (by simpa only [kernel, active, dite_false] using chosen)).2 final reached
  obtain ⟨nextNoise, factored⟩ := reveal_joint_mixed timeouts leaks scheduler bound turns
    wholeProfile focal owner deviation foreign fresh binding unresolved next profile refs event
    outputEq (compileChecks (published := published) refs
      (source prior.support_nonempty.choose).registry
      (source prior.support_nonempty.choose).revelations binding)
    (codeEq prior.support_nonempty.choose)
    (nodeView_eq_resolve outputEq (codeEq prior.support_nonempty.choose)) prior source execution
    boundaryAt (fun seed supported active => (activeCheckpoint seed supported active).agrees)
    bounded effective noise factor
  refine ⟨nextNoise, ?_, ?_⟩
  · calc
      _ = prior.bind (fun seed => (kernel (source seed)).bind fun choice =>
          ((if owner ∈ (source seed).defaulted then PMF.pure (execution seed)
            else app.runUntilHorizon scheduler (fixed choice)
              (fun final => event ∈ final.application.config.cut.completed) horizon
              (execution seed)).map fun final =>
                (revealSuccessor published binding (source seed) choice,
                  (bindingTraffic timeouts) leaks focal final))) := by
        apply bind_congr_on_support _
        intro seed supported
        by_cases inactive : owner ∈ (source seed).defaulted
        · rw [stopped seed supported inactive]
          simp only [kernel, inactive, dite_true, ite_true, PMF.pure_bind, PMF.pure_map,
            revealSuccessor]
        · simp only [inactive, ite_false]
          rw [activeMixture seed supported inactive, PMF.map_bind]
          apply bind_congr_on_support _
          intro choice chosen
          apply map_congr_on_support _
          intro final reached
          obtain ⟨native, _typed, _drained, picked⟩ :=
            endpoint seed supported inactive choice chosen final reached
          rw [picked]
      _ = _ := factored
  · intro seed supported final reached
    by_cases inactive : owner ∈ (source seed).defaulted
    · rw [stopped seed supported inactive, PMF.mem_support_pure_iff] at reached
      subst final
      have status : (ghost seed).config.defaulted = (source seed).defaulted :=
        congrArg DefaultHistory.defaulted (checkpoint seed).defaults
      have eligible : (ghost seed).AutomaticReady event := by
        refine ⟨ghostReady seed, ?_⟩
        rw [owned, status]
        exact inactive
      obtain ⟨caught, path, same⟩ := lag seed supported
      have quiet : ∀ query, ¬ caught.AutomaticReady query := by
        intro query allowed
        exact quiescentAt seed supported query (by
          simpa only [EventGraphRuntime.State.AutomaticReady, same] using allowed)
      have tail := EventGraphRuntime.State.automatic_path_tail_of_quiescent path event eligible
        (fun other otherReady => alone _ other (ghostReady seed) otherReady) quiet
      have typed := (checkpoint seed).revealAutomatic published binding event eventRank eligible
        outputEq (fun ref => refsBefore ref index) (codeEq seed) (decodedAction false)
      have ignored : revealSuccessor published binding (source seed) (readChoice (execution seed)) =
          revealSuccessor published binding (source seed) false := by
        simp only [revealSuccessor, inactive, ite_true]
      refine ⟨readChoice (execution seed), (ghost seed).completeAutomatic event eligible,
        ?_, ⟨caught, tail, same⟩, fun active => (active inactive).elim, rfl⟩
      rw [ignored]
      exact typed
    · rw [activeMixture seed supported inactive, PMF.support_bind] at reached
      obtain ⟨choice, chosen, fixedReached⟩ := Set.mem_iUnion₂.mp reached
      obtain ⟨native, typed, drained, picked⟩ :=
        endpoint seed supported inactive choice chosen final fixedReached
      exact ⟨choice, native, typed,
        ⟨native.drain, native.drain_trace, drained.symm⟩, fun _ => drained, picked⟩

end Vegas
