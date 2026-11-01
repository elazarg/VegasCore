/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceChanceContinuation
import Vegas.Game.SourceServiceDeviationChoice
import GameTheoryExtensions.Math.Probability.ObservedChoice

/-! # Source successors jointly with native deviation traffic

A stopped public-chance run pairs its actual focal traffic with the latent
sampled source successor. The traffic factors through that successor's full
source view. Its native endpoint is the primary typed checkpoint followed by
automatic completion, whose length need not be fixed.
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
    {setup : Setup (Player := Player) (L := L)} (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : (graph setup).BehavioralProfile)
    (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy)
    (event : (graph setup).EventId) (ownerless : (graph setup).actor? event = none)
    (count : Nat) (execution : (application setup runtime leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    {Γ : SourceCtx Player L} {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (refs : ContextRefs (graph setup).layout Γ)
    (distribution : L.DistExpr (SourcePublicCtx L Γ) payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload (compilePublicDist refs distribution))
    (source : State L Γ) (agrees : refs.Agrees source execution.application.config.store)
    (completed : ∀ final ∈ ((application setup runtime leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count execution).support,
      event ∈ final.application.config.cut.completed) :
    ((application setup runtime leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count execution).map
        (fun final => sampledValue event outputEq final.application.config) =
      L.evalDist distribution (sourcePublicEnv source) := by
  have raw := chance_completed_output_law runtime leaks profile scheduler players event ownerless
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
    ((application setup runtime leaks).runUntil scheduler players
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
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (event : (serviceGraph setup mode).EventId) {payload : L.Ty}
    (outputEq : (serviceGraph setup mode).outputLayout event = .publicData payload)
    (traffic : MessageNetwork Player (serviceApplication setup mode deadline leaks).Payload ×
      List (MessageId Player × Bool) ×
      List (serviceApplication setup mode deadline leaks).EnvironmentEntry ×
      List (serviceApplication setup mode deadline leaks).PlayerEntry ×
      PlayerView (serviceGraph setup mode) × PublicView (serviceGraph setup mode)) :
    L.Val payload :=
  ((traffic.2.2.2.2.2.observation.store (.inr event)).map
    (cast (congrArg EventField.Value outputEq))).getD (L.someValue payload)

private theorem sampledTrafficValue_eq
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (focal : Player) (event : (serviceGraph setup mode).EventId) {payload : L.Ty}
    (outputEq : (serviceGraph setup mode).outputLayout event = .publicData payload)
    (execution : (serviceApplication setup mode deadline leaks).Execution) :
    sampledTrafficValue setup leaks event outputEq
      ((serviceRuntime setup mode deadline).bindingTraffic leaks focal execution) =
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
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (focal : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (event : (serviceGraph setup mode).EventId)
    (ownerless : (serviceGraph setup mode).actor? event = none)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (horizon : Nat) (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (pick : MessageNetwork Player (serviceApplication setup mode deadline leaks).Payload ×
      List (MessageId Player × Bool) ×
      List (serviceApplication setup mode deadline leaks).EnvironmentEntry ×
      List (serviceApplication setup mode deadline leaks).PlayerEntry ×
      PlayerView (serviceGraph setup mode) × PublicView (serviceGraph setup mode) → L.Val payload)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
      (serviceRuntime setup mode deadline).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun traffic => (config, traffic))
    (ready : ∀ seed ∈ prior.support, event ∉ (execution seed).application.config.cut.completed →
      (execution seed).application.config.cut.Ready event)
    (sampled : ∀ seed ∈ prior.support,
      (((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
        (focalPlayers setup leaks focal deviation)
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).map fun final =>
          pick ((serviceRuntime setup mode deadline).bindingTraffic leaks focal final)) =
      L.evalDist distribution (sourcePublicEnv (source seed).state)) :
    ∃ nextNoise : DecisionView focal ((name, .publicData payload) :: Γ) → PMF _,
      (prior.bind fun seed =>
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
          (focalPlayers setup leaks focal deviation)
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            (sampleSuccessor name (source seed)
              (pick ((serviceRuntime setup mode deadline).bindingTraffic leaks focal final)),
              (serviceRuntime setup mode deadline).bindingTraffic leaks focal final)) =
      ((prior.map source).bind fun config =>
        (L.evalDist distribution (sourcePublicEnv config.state)).map
          (sampleSuccessor name config)).bind fun config =>
          (nextNoise (config.view focal)).map fun traffic => (config, traffic) := by
  let app := serviceApplication setup mode deadline leaks
  let read := fun seed => (serviceRuntime setup mode deadline).bindingTraffic leaks focal
    (execution seed)
  let phase := fun seed => (app.runUntilHorizon scheduler (focalPlayers setup leaks focal deviation)
    (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)).map
      ((serviceRuntime setup mode deadline).bindingTraffic leaks focal)
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
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
    (complete : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    (focal : Player) (deviation : (application setup runtime leaks).Policy)
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
    (execution : Seed → (application setup runtime leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.sample name fresh distribution next) profile refs (source seed).revelations
      (source seed).registry embedding refsBefore rank)
    (checkpoint : ∀ seed, SourceCheckpoint setup (source seed) refs rank
      (execution seed).application.config)
    (boundary : ∀ seed ∈ prior.support, CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) rank (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => (source seed, runtime.bindingTraffic leaks focal
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
      (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation
    let readChoice := fun final : (application setup runtime leaks).Execution =>
      ((final.application.config.outputs event).map
        (cast (congrArg EventField.Value outputEq))).getD (L.someValue payload)
    ∃ nextNoise : DecisionView focal ((name, .publicData payload) :: Γ) → PMF _,
      ((prior.bind fun seed =>
        ((application setup runtime leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            (sampleSuccessor name (source seed) (readChoice final),
              runtime.bindingTraffic leaks focal final)) =
        ((prior.map source).bind fun config =>
          (L.evalDist distribution (sourcePublicEnv config.state)).map
            (sampleSuccessor name config)).bind fun config =>
              (nextNoise (config.view focal)).map (fun traffic => (config, traffic))) ∧
      ∀ seed ∈ prior.support, ∀ final ∈
          ((application setup runtime leaks).runUntilHorizon scheduler players
            (fun current => event ∈ current.application.config.cut.completed) horizon
            (execution seed)).support,
        ∃ (value : L.Val payload) (native : EventGraphRuntime.State (graph setup)),
          SourceCheckpoint setup (sampleSuccessor name (source seed) value)
            (refs.cons (name := name) sampleRef) (rank + 1) native.config ∧
          final.application.config = native.drain.config ∧ readChoice final = value := by
  intro index event outputEq sampleRef players readChoice
  let app := application setup runtime leaks
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
          (runtime.bindingTraffic leaks focal final)) =
      L.evalDist distribution (sourcePublicEnv (source seed).state) := by
    rw [← phaseEq seed supported]
    have pointwise (final : app.Execution) :
        sampledTrafficValue setup leaks event outputEq (runtime.bindingTraffic leaks focal final) =
          sampledValue event outputEq final.application.config :=
      sampledTrafficValue_eq setup (mode := .sequential) (deadline := runtime.deadline)
        leaks focal event outputEq final
    simp_rw [pointwise]
    exact chance_completed_value_law runtime leaks (compileEventProfile setup.program wholeProfile)
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
              runtime.bindingTraffic leaks focal final)) := by
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
    obtain ⟨action, native, primary, drained⟩ := runUntil_completed_primary_drain runtime leaks
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

end Vegas
