module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import GameTheory.Math.Probability.ConditionalObservation
public import Vegas.Game.SampleReadout
public import Vegas.Game.GraphForfeit
public import Vegas.Game.IntendedPrefixContinuation
public import Vegas.Game.PrefixDeviation.Boundary
public import Vegas.Game.RevealPhaseBoundary
public import Vegas.Pending.FocalTraffic
public import Vegas.Game.SourceStateKernel

@[expose] public section

/-! # Chance and terminal continuation bounds -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph Interaction GameTheory.Math.Probability EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def representativeSampleTail
    {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}
    {rank : Nat} {origin : setup.informationGraph.Config}
    (frame : SourceResidual setup profile rank origin)
    {name : VarId} {payload : L.Ty}
    (fresh : name ∉ frame.Γ.map Prod.fst)
    (distribution : L.DistExpr (SourcePublicCtx L frame.Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: frame.Γ) frame.names)
    (programEq : frame.program = .sample name fresh distribution next)
    (value : L.Val payload) :
    let embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (.sample name fresh distribution next) := programEq ▸ frame.embedding
    let index : Fin (eventCount (.sample name fresh distribution next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : setup.informationGraph.outputLayout (embedding.event index) =
        .publicData payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    let atRank : (embedding.event index).val = rank := by
      rcases frame with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
        aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
        transport, checkpoint⟩
      dsimp only at fresh distribution next programEq value ⊢
      cases programEq
      simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
    let ready : origin.cut.Ready (embedding.event index) := by
      have ordered := frame.checkpoint.ordered
      rw [← atRank] at ordered
      exact ordered.ready (embedding.event index).isLt
    SourceResidual setup profile (rank + 1)
      (origin.complete (embedding.event index) ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          value)) := by
  rcases frame with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, checkpoint⟩
  dsimp only at fresh distribution next programEq value ⊢
  cases programEq
  let index : Fin (eventCount (.sample name fresh distribution next)) :=
    ⟨0, by simp [eventCount]⟩
  have outputEq : setup.informationGraph.outputLayout (embedding.event index) =
      .publicData payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  have atRank : (embedding.event index).val = rank := by
    simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have ready : origin.cut.Ready (embedding.event index) := by
    have ordered := checkpoint.ordered
    rw [← atRank] at ordered
    exact ordered.ready (embedding.event index).isLt
  have decoded : decodeEventAction setup.program (embedding.event index)
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) =
        none := by
    have lookup := aligned.actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
    simpa [index, outputEq, decodeEventAction] using lookup
  let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
  let tailRefs : ContextRefs (graphLayout setup.program)
      ((name, .publicData payload) :: Γ) :=
    refs.cons ⟨.inr (embedding.event index), outputEq⟩
  have tailBefore : ContextRefsBefore tailRefs tailEmbedding :=
    refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl
  have tailAligned : CompiledPolicySuffix setup.program profile next
      (afterSample residualProfile) tailRefs
      (sampleSuccessor name source value).revelations
      (sampleSuccessor name source value).registry
      tailEmbedding tailBefore (rank + 1) := by
    simpa only [sampleSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
      aligned.sampleTail setup.program profile (_openNames := names) fresh distribution next
        residualProfile refs source.revelations source.registry embedding refsBefore rank
  refine {
    Γ := _, names := _, program := next, residualProfile := afterSample residualProfile,
    source := sampleSuccessor name source value, refs := tailRefs,
    embedding := tailEmbedding, refsBefore := tailBefore, aligned := tailAligned,
    admitted := fun whole who => admitted whole who,
    authentic := fun whole who => authentic whole who,
    supports := fun whole who => supports whole who,
    disclosing := fun whole who => disclosing whole who,
    lift := lift ∘ Sum.inr,
    commutes := fun state => ?_, steps := fun state joint => ?_,
    injective := injective.comp Sum.inr_injective,
    transport := fun more store history defaults => ?_,
    checkpoint := checkpoint.sample (native := origin) name
      (embedding.event index) atRank ready outputEq (fun ref => refsBefore ref index)
        decoded value }
  · rw [Function.comp_apply, commutes, ProtocolState.behavioralStateStep_sample_tail,
      PMF.map_comp]
  · rw [Function.comp_apply, steps]
    change PMF.map lift ((ProtocolState.step next state joint).map Sum.inr) = _
    rw [PMF.map_comp]
  · rw [show rank + 1 + more = rank + (more + 1) by omega, transport,
      decodeSourcePrefix?_sample, Option.map_map]
    rfl

private theorem sample_source_successor
    {setup : Setup (Player := Player) (L := L)} [Finite Player]
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    {rank : Nat} {origin : setup.informationGraph.Config}
    (frame : SourceResidual setup (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target) rank origin)
    {name : VarId} {payload : L.Ty}
    (fresh : name ∉ frame.Γ.map Prod.fst)
    (distribution : L.DistExpr (SourcePublicCtx L frame.Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: frame.Γ) frame.names)
    (programEq : frame.program = .sample name fresh distribution next)
    (source : Config Player L frame.Γ)
    (revelations : @source.revelations = @frame.source.revelations)
    (registry : source.registry = frame.source.registry)
    (ghost : setup.informationGraph.Config)
    {inputs : setup.informationGraph.Inputs} (reachable : ghost.Reachable inputs)
    (checkpoint : SourceCheckpoint setup source frame.refs rank ghost)
    (history : setup.intendedProtocol.History)
    (historyAt : history.state = some (frame.lift (ProtocolState.entry frame.program source)))
    (reference : setup.informationGraph.BehavioralProfile) :
    let embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (.sample name fresh distribution next) := programEq ▸ frame.embedding
    let lifted : ProtocolState (.sample name fresh distribution next) →
        ProtocolState setup.program := programEq ▸ frame.lift
    let index : Fin (eventCount (.sample name fresh distribution next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : setup.informationGraph.EventId := embedding.event index
    let outputEq : setup.informationGraph.outputLayout event = .publicData payload :=
      (embedding.layout_eq index).trans rfl
    ∃ ready : ghost.cut.Ready event,
      let after := fun value : L.Val payload => ghost.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventField.Value outputEq.symm) value)
      setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan reference setup.informationGraph.canonicalScheduler)
          1 ghost = (L.evalDist distribution (sourcePublicEnv source.state)).map after ∧
      ∀ value ∈ (L.evalDist distribution (sourcePublicEnv source.state)).support,
        SourceCheckpoint setup (sampleSuccessor name source value)
          (frame.refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1) (after value) ∧
        (after value).Reachable inputs ∧
        ∃ nextHistory : setup.intendedProtocol.History,
          nextHistory.state = some (lifted (.inr (ProtocolState.entry next
            (sampleSuccessor name source value)))) := by
  rcases frame with ⟨Γ, names, program, residualProfile, original, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, originalCheckpoint⟩
  dsimp only at fresh distribution next programEq source revelations registry checkpoint historyAt ⊢
  cases programEq
  let _ := Fintype.ofFinite Player
  let frame : SourceResidual setup (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target) rank origin :=
    ⟨Γ, names, .sample name fresh distribution next, residualProfile, original, refs, embedding,
      refsBefore, aligned, admitted, authentic, supports, disclosing, lift, commutes, steps,
      injective, transport, originalCheckpoint⟩
  let index : Fin (eventCount (.sample name fresh distribution next)) :=
    ⟨0, by simp [eventCount]⟩
  let event := embedding.event index
  have outputEq : setup.informationGraph.outputLayout event = .publicData payload :=
    (embedding.layout_eq index).trans rfl
  have atRank : event.val = rank := by
    simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have ready : ghost.cut.Ready event := by
    have ordered := checkpoint.ordered
    rw [← atRank] at ordered
    exact ordered.ready event.isLt
  have decoded : decodeEventAction setup.program event
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit) = none := by
    simpa [index, event, outputEq, decodeEventAction] using aligned.actionEq index
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
  have codeEq : cast (congrArg (EventCode setup.informationGraph.layout) outputEq)
      (setup.informationGraph.nodes event) =
        .sample payload (compilePublicDist refs distribution) := by
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have graphLaw := sample_step ghost event ready outputEq refs distribution codeEq source.state
    checkpoint.agrees
  have ownerless : setup.informationGraph.actor? event = none := by
    exact (EventCode.actor_cast outputEq _).symm.trans (by rw [codeEq]; rfl)
  have least : ∀ other, other ∉ ghost.cut.completed → event.val ≤ other.val := by
    intro other missing
    rw [atRank]
    exact Nat.le_of_not_gt fun lower => missing ((checkpoint.ordered.2 other).mpr lower)
  refine ⟨ready, ?_, ?_⟩
  · rw [runPlan_canonical_ownerless reference 0 ghost event ready least ownerless]
    let : Subsingleton (setup.informationGraph.Action event) := by
      change Subsingleton ((setup.informationGraph.outputLayout event).Action)
      rw [outputEq]
      infer_instance
    rw [Subsingleton.elim ((setup.informationGraph.nodes event).actionOfActorNone ownerless)
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)]
    simpa only [EventGraph.runPlan, PMF.bind_pure] using graphLaw
  · intro value drawn
    have nextCheckpoint := checkpoint.sample (native := ghost) name event atRank
      ready outputEq (fun ref => refsBefore ref index) decoded value
    have graphStep : ghost.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventField.Value outputEq.symm) value) ∈
          (ghost.step event ready
            (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)).support := by
      rw [graphLaw]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨value, drawn, rfl⟩
    let actual := residualAt frame source revelations registry ghost checkpoint
    have atGhost : history.state = sourceServicePrefix? setup rank ghost :=
      historyAt.trans actual.decode.symm
    have sourceStep : Sum.inr (ProtocolState.entry next (sampleSuccessor name source value)) ∈
        (ProtocolState.behavioralStateStep (.sample name fresh distribution next) residualProfile
          (.inl source)).support := by
      rw [ProtocolState.behavioralStateStep_sample_entry]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨value, drawn, rfl⟩
    obtain ⟨nextHistory, nextHistoryAt⟩ := actual.intendedHistory_of_step intended target agrees
      history atGhost _ sourceStep
    exact ⟨nextCheckpoint, Config.Step.path_reachable
      (.single ⟨event, ready, _, graphStep⟩) reachable, nextHistory, nextHistoryAt⟩

private theorem chance_source_ghost_joint
    {Seed : Type} {Γ : SourceCtx Player L} {payload : L.Ty}
    (name : VarId) (distribution : L.DistExpr (SourcePublicCtx L Γ) payload)
    (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
    {duration : (serviceGraph setup deps).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (event : (serviceGraph setup deps).EventId)
    (ownerless : (serviceGraph setup deps).actor? event = none)
    (alone : ∀ (cut : (serviceGraph setup deps).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (horizon : Nat) (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (ghost : Seed → setup.informationGraph.Config)
    (stepGhost : setup.informationGraph.Config → L.Val payload → setup.informationGraph.Config)
    (execution : Seed → (serviceApplication setup deps duration leaks).Execution)
    (pick : MessageNetwork Player (serviceApplication setup deps duration leaks).Payload ×
      List (MessageId Player × Bool) ×
      List (serviceApplication setup deps duration leaks).EnvironmentEntry ×
      List (serviceApplication setup deps duration leaks).PlayerEntry ×
      PlayerView (serviceGraph setup deps) × PublicView (serviceGraph setup deps) → L.Val payload)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, ghost seed),
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, ghost seed))).bind fun config =>
        (noise (config.1.view focal)).map fun traffic => (config, traffic))
    (ready : ∀ seed ∈ prior.support, event ∉ (execution seed).application.config.cut.completed →
      (execution seed).application.config.cut.Ready event)
    (sampled : ∀ seed ∈ prior.support,
      (((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
        (focalPlayers (serviceTimeouts setup deps duration) leaks focal deviation)
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).map fun final =>
          pick ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal final)) =
      L.evalDist distribution (sourcePublicEnv (source seed).state)) :
    ∃ nextNoise : DecisionView focal ((name, .publicData payload) :: Γ) → PMF _,
      (prior.bind fun seed =>
        ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
          (focalPlayers (serviceTimeouts setup deps duration) leaks focal deviation)
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            ((sampleSuccessor name (source seed)
              (pick ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal final)),
              stepGhost (ghost seed)
                (pick ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal final))),
              (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal final)) =
      ((prior.map (fun seed => (source seed, ghost seed))).bind fun config =>
        (L.evalDist distribution (sourcePublicEnv config.1.state)).map
          (fun value => (sampleSuccessor name config.1 value, stepGhost config.2 value))).bind
            fun config => (nextNoise (config.1.view focal)).map
              fun traffic => (config, traffic) := by
  let app := serviceApplication setup deps duration leaks
  let read := fun seed => (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
    (execution seed)
  let phase := fun seed => (app.runUntilHorizon scheduler
    (focalPlayers (serviceTimeouts setup deps duration) leaks focal deviation)
    (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)).map
      ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal)
  obtain ⟨channel, channelLaw⟩ := exists_updated_observation_kernel_of_readout prior
    (fun seed => (source seed, ghost seed)) read (fun config => config.1.view focal) noise factor
    (fun _ => PMF.pure ()) (fun config _ => config) (fun config => config.1.view focal)
    (fun seed _ => phase seed)
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left leftSupport _ _ right rightSupport _ _ _ same => by
      have recalled := congrArg (fun traffic => traffic.2.2.1) same
      change (execution left).environmentRecall = (execution right).environmentRecall at recalled
      simp only [phase, ReactiveApplication.runUntilHorizon, recalled]
      exact focalPhase_traffic_congr scheduler focal deviation (Or.inl ownerless) alone
        (horizon - (execution right).environmentRecall.length)
        (execution left) (execution right) (ready left leftSupport) (ready right rightSupport) same)
  have joint : (prior.bind fun seed => (phase seed).map fun traffic =>
      ((source seed, ghost seed), traffic)) =
      (prior.map (fun seed => (source seed, ghost seed))).bind fun config =>
        (channel (config.1.view focal)).map fun traffic => (config, traffic) := by
    simpa only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure] using channelLaw
  let choice := fun view => (channel view).map pick
  let nextNoise := fun view : DecisionView focal ((name, .publicData payload) :: Γ) =>
    fiberPosterior (channel (view.back false)) pick (view.observation.cells.get .here)
  let advance := fun (config : Config Player L Γ × setup.informationGraph.Config) value =>
    (sampleSuccessor name config.1 value, stepGhost config.2 value)
  have factored : (prior.bind fun seed => (phase seed).map fun traffic =>
      (advance (source seed, ghost seed) (pick traffic), traffic)) =
      ((prior.map (fun seed => (source seed, ghost seed))).bind fun config =>
        (choice (config.1.view focal)).map (advance config)).bind fun config =>
          (nextNoise (config.1.view focal)).map fun traffic => (config, traffic) := by
    calc
      _ = (prior.bind fun seed => (phase seed).map fun traffic =>
          ((source seed, ghost seed), traffic)).map
            (fun pair => (advance pair.1 (pick pair.2), pair.2)) := by
        simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      _ = ((prior.map (fun seed => (source seed, ghost seed))).bind fun config =>
          (channel (config.1.view focal)).map fun traffic => (config, traffic)).map
            (fun pair => (advance pair.1 (pick pair.2), pair.2)) := by rw [joint]
      _ = _ := by
        simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_bind, PMF.bind_map]
        apply bind_congr_on_support _
        intro seed _supported
        rw [map_readout_choice (channel ((source seed).view focal)) pick
          (fun value traffic => (advance (source seed, ghost seed) value, traffic))]
        apply bind_congr_on_support _
        intro value _chosen
        have backed := back_sample_view focal name (source seed) value
        dsimp only [nextNoise, advance]
        rw [backed]
        rfl
  have projected := congrArg (PMF.map Prod.fst) factored
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_fun_const,
    PMF.bind_pure] at projected
  have marginal : (prior.bind fun seed => (phase seed).map
      (fun traffic => advance (source seed, ghost seed) (pick traffic))) =
      (prior.map (fun seed => (source seed, ghost seed))).bind fun config =>
        (L.evalDist distribution (sourcePublicEnv config.1.state)).map (advance config) := by
    rw [PMF.bind_map]
    apply bind_congr_on_support _
    intro seed supported
    have actual := congrArg (PMF.map (advance (source seed, ghost seed))) (sampled seed supported)
    simpa only [phase, PMF.map_comp, Function.comp_def] using actual
  refine ⟨nextNoise, ?_⟩
  rw [← projected, marginal] at factored
  simpa only [phase, advance, PMF.map_bind, PMF.map_comp, Function.comp_def] using factored

private theorem native_chance_clear_endpoint
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {duration : (serviceGraph setup deps).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (event : (serviceGraph setup deps).EventId)
    (ownerless : (serviceGraph setup deps).actor? event = none)
    (solitary : (serviceGraph setup deps).Solitary event)
    (count rank : Nat) (before after : (serviceApplication setup deps duration leaks).Execution)
    (ordered : before.application.config.cut.IsPrefix rank) (atRank : event.val = rank)
    (clear : before.application.config.defaulted = ∅)
    (reached : after ∈ ((serviceApplication setup deps duration leaks).runUntil scheduler players
      (fun current => event ∈ current.application.config.cut.completed) count before).support)
    (completed : event ∈ after.application.config.cut.completed) :
    after.application.config.defaulted = ∅ ∧
      after.application.config.cut.IsPrefix (rank + 1) ∧
      ∃ ready : before.application.config.cut.Ready event, ∃ action,
        after.application.config ∈ (before.application.config.step event ready action).support := by
  have ready : before.application.config.cut.Ready event := by
    have orderedBefore := ordered
    rw [← atRank] at orderedBefore
    exact orderedBefore.ready event.isLt
  have quiescent (query : (serviceGraph setup deps).EventId) :
      ¬ before.application.AutomaticReady query := by
    intro automatic
    obtain ⟨owner, _, defaulted⟩ := automatic.owned
    simp only [clear, Finset.notMem_empty] at defaulted
  obtain ⟨action, native, primary, drained⟩ := runUntil_completed_primary_drain
    (serviceTimeouts setup deps duration) leaks scheduler players event count before after ready
    (fun query queryReady => solitary _ queryReady ready) quiescent reached completed
  have primaryClear : native.config.defaulted = ∅ := by
    unfold EventGraph.Config.step at primary
    obtain ⟨value, _sampled, recorded⟩ := (PMF.mem_support_map_iff _ _ _).mp primary
    rw [← recorded]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro who defaulted
    have original := (mem_defaulted_complete_of_actor_ne before.application.config event ready
      action value who (by rw [ownerless]; intro impossible; cases impossible)).mp defaulted
    simp only [clear, Finset.notMem_empty] at original
  have configEq : after.application.config = native.config := by
    rw [drained, native.drain_eq_of_empty primaryClear]
  refine ⟨configEq ▸ primaryClear, ?_, ready, action, configEq ▸ primary⟩
  have orderedAfter := ordered.complete_at event ready atRank
  unfold EventGraph.Config.step at primary
  obtain ⟨value, _sampled, recorded⟩ := (PMF.mem_support_map_iff _ _ _).mp primary
  rw [configEq, ← recorded]
  exact orderedAfter

private theorem native_chance_completionBoundary
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {duration : (serviceGraph setup deps).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}
    {horizon : Nat} (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (event : (serviceGraph setup deps).EventId)
    (ownerless : (serviceGraph setup deps).actor? event = none)
    (solitary : (serviceGraph setup deps).Solitary event)
    (before after : (serviceApplication setup deps duration leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val before)
    (budget : before.environmentRecall.length ≤ horizon)
    (clear : before.application.config.defaulted = ∅)
    (reached : after ∈ ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      players (fun current => event ∈ current.application.config.cut.completed) horizon
      before).support)
    (completed : event ∈ after.application.config.cut.completed) :
    CompletionBoundary setup leaks scheduler players (event.val + 1) after ∧
      after.environmentRecall.length ≤ horizon ∧ after.application.config.defaulted = ∅ := by
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  obtain ⟨supported, bounded⟩ := runUntilHorizon_bounded boundary.supported budget reached
  obtain ⟨afterClear, afterOrdered, _⟩ := native_chance_clear_endpoint scheduler players event
    ownerless solitary (horizon - before.environmentRecall.length) event.val before after
    boundary.ordered rfl clear reached completed
  have shaped : BlockShaped (graph := G) event.val (event.val + 1) := by
    intro config inside unfinished query queryReady
    have pending : event ∉ config.cut.completed := by
      intro done
      apply unfinished
      intro other early
      by_cases prior : other.val < event.val
      · exact inside.1 other prior
      · have same : other = event := Fin.ext (by omega)
        exact same ▸ done
    have ready : config.cut.Ready event :=
      ⟨pending, fun prior predecessor => inside.1 prior (G.order.predecessor_lt predecessor)⟩
    have same := solitary _ queryReady ready
    subst query
    exact ⟨le_rfl, Nat.lt_succ_self _⟩
  have inside : InBlock event.val (event.val + 1) before.application.config :=
    ⟨fun query prior => (boundary.ordered.2 query).mpr prior,
      fun query late done => Nat.not_lt.mpr (by omega) ((boundary.ordered.2 query).mp done)⟩
  have untouched := blockRun_untouched shaped scheduler players
    (fun current => event ∈ current.application.config.cut.completed)
    (fun _ done => done event (Nat.lt_succ_self _))
    (horizon - before.environmentRecall.length) before after inside
    (fun query late => boundary.untouched query (by omega)) reached
  exact ⟨⟨supported, afterOrdered, untouched⟩, bounded, afterClear⟩

theorem nativeSourceContinuation_sample [Finite Player]
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wellFormed : setup.WellFormed)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (reference : setup.informationGraph.BehavioralProfile) (focal : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    (nativePayoff : (serviceApplication setup deps duration leaks).Execution → ℝ)
    (sourcePayoff : setup.informationGraph.Config → ℝ)
    {rank : Nat} {point : setup.informationGraph.Config}
    (frame : SourceResidual setup (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target) rank point)
    {name : VarId} {payload : L.Ty}
    (fresh : name ∉ frame.Γ.map Prod.fst)
    (distribution : L.DistExpr (SourcePublicCtx L frame.Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: frame.Γ) frame.names)
    (programEq : frame.program = .sample name fresh distribution next)
    (continuation : nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns
      (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)
      reference focal deviation nativePayoff sourcePayoff
      (representativeSampleTail frame fresh distribution next programEq (L.someValue payload))) :
    nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns
      (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)
      reference focal deviation nativePayoff sourcePayoff frame := by
  classical
  rcases frame with ⟨Γ, names, program, residualProfile, original, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, originalCheckpoint⟩
  dsimp only at fresh distribution next programEq continuation ⊢
  cases programEq
  let whole := setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target
  let frame : SourceResidual setup whole rank point :=
    ⟨Γ, names, .sample name fresh distribution next, residualProfile, original, refs, embedding,
      refsBefore, aligned, admitted, authentic, supports, disclosing, lift, commutes, steps,
      injective, transport, originalCheckpoint⟩
  let tail := representativeSampleTail frame fresh distribution next rfl (L.someValue payload)
  change nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns whole
    reference focal deviation nativePayoff sourcePayoff tail at continuation
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  let index : Fin (eventCount (.sample name fresh distribution next)) :=
    ⟨0, by simp [eventCount]⟩
  let event := embedding.event index
  have atRank : event.val = rank := by
    simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have outputEq : G.outputLayout event = .publicData payload :=
    (embedding.layout_eq index).trans rfl
  have codeEq : cast (congrArg (EventCode G.layout) outputEq) (G.nodes event) =
      .sample payload (compilePublicDist refs distribution) := by
    change cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
      ((toInformationGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have ownerless : G.actor? event = none :=
    (EventCode.actor_cast outputEq _).symm.trans (by rw [codeEq]; rfl)
  have solitary : G.Solitary event := by
    intro cut other otherReady eventReady
    apply relaxed.ready_alone_of_not_publication cut _ _ eventReady otherReady
    · rw [outputEq]; trivial
    · rw [outputEq]; exact False.elim
  have alone : ∀ (cut : G.order.Cut) (other : G.EventId),
      cut.Ready event → cut.Ready other → other = event :=
    fun cut _ ready otherReady => solitary cut otherReady ready
  intro covered Seed prior source ghost revelations registry checkpoints reachable histories members
    submitting future execution players boundary budget keys noise factor
  let pick := fun final : app.Execution => sampledValue event outputEq final.application.config
  let phase := fun seed => app.runUntilHorizon scheduler (players seed)
    (fun current => event ∈ current.application.config.cut.completed) horizon (execution seed)
  let afterGhost := fun (config : setup.informationGraph.Config) (value : L.Val payload) =>
    if ready : config.cut.Ready event then config.complete event ready
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
      (cast (congrArg EventField.Value outputEq.symm) value) else config
  let staged := prior.bind fun seed => (phase seed).map fun final => (seed, final)
  let nextSource := fun sample : Seed × app.Execution =>
    sampleSuccessor name (source sample.1) (pick sample.2)
  let nextGhost := fun sample : Seed × app.Execution => afterGhost (ghost sample.1) (pick sample.2)
  have support (sample : Seed × app.Execution) (present : sample ∈ staged.support) :
      sample.1 ∈ prior.support ∧ sample.2 ∈ (phase sample.1).support := by
    obtain ⟨seed, supported, selected⟩ := (PMF.mem_support_bind_iff _ _ _).mp present
    obtain ⟨final, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp selected
    cases same
    exact ⟨supported, reached⟩
  have ready (seed : Seed) (present : seed ∈ prior.support) :
      (execution seed).application.config.cut.Ready event := by
    have ordered := (boundary seed present).ordered
    rw [← atRank] at ordered
    exact ordered.ready event.isLt
  have ghostReady (seed : Seed) (present : seed ∈ prior.support) :
      (ghost seed).cut.Ready event := by
    have ordered := (checkpoints seed present).ordered
    rw [← atRank] at ordered
    exact ordered.ready event.isLt
  have clear (seed : Seed) (present : seed ∈ prior.support) :
      (execution seed).application.config.defaulted = ∅ := by
    let residual := residualAt frame (source seed) (revelations seed present)
      (registry seed present) (ghost seed) (checkpoints seed present)
    obtain ⟨history, historyAt⟩ := histories seed present
    have decoded := residual.decode
    change sourceServicePrefix? setup rank (ghost seed) =
      some (lift (ProtocolState.entry (.sample name fresh distribution next) (source seed)))
        at decoded
    have sourceClear := residual.clear_of_intended_history wellFormed history
      (historyAt.trans decoded.symm)
    exact (defaulted_eq_of_completionOf_eq
      (congrArg (fun key => key.2.2) (keys seed present))).trans sourceClear
  have agree (seed : Seed) (present : seed ∈ prior.support) :
      refs.Agrees (source seed).state (execution seed).application.config.store := by
    have stores := congrArg (fun key => key.2.1) (keys seed present)
    change (execution seed).application.config.store =
      (G.fromSequentialConfig (ghost seed)).store at stores
    have converted : (G.fromSequentialConfig (ghost seed)).store = (ghost seed).store := by
      funext field
      cases field <;> rfl
    rw [stores, converted]
    intro readName cell ref
    exact (checkpoints seed present).agrees ref
  have complete (seed : Seed) (present : seed ∈ prior.support) :
      ∀ final ∈ (phase seed).support, event ∈ final.application.config.cut.completed :=
    runUntilHorizon_stop contract (players seed)
      (fun current => event ∈ current.application.config.cut.completed)
      (fun _ terminal => by rw [terminal]; exact Finset.mem_univ _)
      (execution seed) (boundary seed present).supported (budget seed present)
  have focalLaw (seed : Seed) (present : seed ∈ prior.support) : phase seed =
      app.runUntilHorizon scheduler
        (focalPlayers (serviceTimeouts setup deps duration) leaks focal deviation)
        (fun current => event ∈ current.application.config.cut.completed)
        horizon (execution seed) :=
    runUntil_reference_focal scheduler bound turns (firstTurnTiming setup turns deps)
      (effectiveOpening (G.prefixProfile (members seed))) focal deviation event (Or.inl ownerless)
      alone _ (execution seed) (fun _ => ready seed present)
  have sampled (seed : Seed) (present : seed ∈ prior.support) :
      (phase seed).map pick = L.evalDist distribution (sourcePublicEnv (source seed).state) := by
    have raw := chance_completed_output_distribution (serviceTimeouts setup deps duration) leaks
      relaxed.actorSerial scheduler (players seed) event ownerless solitary
      (horizon - (execution seed).environmentRecall.length) (execution seed) (ready seed present)
      (complete seed present)
    rw [(G.nodes event).action_eq_of_actor_none ownerless
      (EventCode.actionOfActorNone (G.nodes event) ownerless)
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit),
      sample_step (execution seed).application.config event (ready seed present) outputEq refs
        distribution codeEq (source seed).state (agree seed present), PMF.map_comp] at raw
    have projected := congrArg (PMF.map fun value : Option (G.outputLayout event).Value =>
      (value.map (cast (congrArg EventField.Value outputEq))).getD (L.someValue payload)) raw
    simpa only [phase, pick, sampledValue, PMF.map_comp, Function.comp_def,
      Config.complete, Function.update_self, Option.map_some, cast_cast, cast_eq,
      Option.getD_some, ReactiveApplication.runUntilHorizon, show (fun x : L.Val payload => x) =
        id from rfl, PMF.map_id] using projected
  have trafficPick (final : app.Execution) : sampledTrafficValue setup leaks event outputEq
      ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal final) = pick final := by
    have publicField : (G.layout (.inr event)).IsPublic := by
      change (G.outputLayout event).IsPublic
      rw [outputEq]; trivial
    dsimp only [sampledTrafficValue, bindingTraffic, State.publicView, EventGraph.publicObserve]
    rw [EventGraph.publicStore_of_public _ _ _ publicField]
    rfl
  obtain ⟨nextNoise, jointFocal⟩ := chance_source_ghost_joint name distribution setup leaks
    scheduler
    focal deviation event ownerless alone horizon prior source ghost afterGhost execution
    (sampledTrafficValue setup leaks event outputEq) noise factor
    (fun seed present _ => ready seed present)
    (fun seed present => by
      rw [← focalLaw seed present]
      simpa only [trafficPick] using sampled seed present)
  have joint : staged.map (fun sample => ((nextSource sample, nextGhost sample),
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal sample.2)) =
      ((prior.map (fun seed => (source seed, ghost seed))).bind fun current =>
        (L.evalDist distribution (sourcePublicEnv current.1.state)).map fun value =>
          (sampleSuccessor name current.1 value, afterGhost current.2 value)).bind fun current =>
            (nextNoise (current.1.view focal)).map fun observed => (current, observed) := by
    rw [← jointFocal]
    simp only [staged, PMF.map_bind, PMF.map_comp, Function.comp_def]
    apply bind_congr_on_support _
    intro seed present
    rw [← focalLaw seed present]
    apply map_congr_on_support _
    intro final _
    simp only [nextSource, nextGhost, trafficPick]
  have marginal := congrArg (PMF.map Prod.fst) joint
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind, pmf_map_fun_const, PMF.bind_pure]
    at marginal
  have factorNext : staged.map (fun sample => ((nextSource sample, nextGhost sample),
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal sample.2)) =
      (staged.map fun sample => (nextSource sample, nextGhost sample)).bind fun current =>
        (nextNoise (current.1.view focal)).map fun observed => (current, observed) := by
    rw [marginal]
    exact joint
  have nextFacts (sample : Seed × app.Execution) (present : sample ∈ staged.support) :
      SourceCheckpoint setup (nextSource sample) tail.refs (rank + 1) (nextGhost sample) ∧
      (∃ inputs, (nextGhost sample).Reachable inputs) ∧
      (∃ history : setup.intendedProtocol.History, history.state =
        some (tail.lift (ProtocolState.entry tail.program (nextSource sample)))) ∧
      runKey sample.2.application.config = runKey (G.fromSequentialConfig (nextGhost sample)) := by
    have supported := (support sample present).1
    have reached := (support sample present).2
    obtain ⟨history, historyAt⟩ := histories sample.1 supported
    obtain ⟨inputs, sourceReach⟩ := reachable sample.1 supported
    obtain ⟨sourceReady, headLaw, sourceGood⟩ := sample_source_successor intended target agrees
      frame fresh distribution next rfl (source sample.1) (revelations sample.1 supported)
      (registry sample.1 supported) (ghost sample.1) sourceReach (checkpoints sample.1 supported)
      history historyAt (setup.informationGraph.prefixProfile reference)
    have chosen : pick sample.2 ∈
        (L.evalDist distribution (sourcePublicEnv (source sample.1).state)).support := by
      rw [← sampled sample.1 supported]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨sample.2, reached, rfl⟩
    have decoded := sourceGood (pick sample.2) chosen
    change (ghost sample.1).cut.Ready event at sourceReady
    have ghostEq : nextGhost sample = (ghost sample.1).complete event sourceReady
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventField.Value outputEq.symm) (pick sample.2)) := by
      simp only [nextGhost, afterGhost, dite_eq_left sourceReady]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ghostEq]
      exact decoded.1
    · rw [ghostEq]
      exact ⟨inputs, decoded.2.1⟩
    · exact decoded.2.2
    · obtain ⟨_, _, actualReady, action, primary⟩ := native_chance_clear_endpoint scheduler
        (players sample.1) event ownerless solitary
        (horizon - (execution sample.1).environmentRecall.length) rank
        (execution sample.1) sample.2 (boundary sample.1 supported).ordered atRank
        (clear sample.1 supported) reached (complete sample.1 supported _ reached)
      have actionEq := (G.nodes event).action_eq_of_actor_none ownerless action
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
      rw [actionEq, sample_step (execution sample.1).application.config event actualReady outputEq
        refs distribution codeEq (source sample.1).state (agree sample.1 supported),
        PMF.support_map] at primary
      obtain ⟨value, _drawn, configEq⟩ := primary
      have readValue : pick sample.2 = value := by
        change sampledValue event outputEq sample.2.application.config = value
        rw [← configEq]
        simp only [sampledValue, Config.complete, Function.update_self, Option.map_some,
          cast_cast, cast_eq, Option.getD_some]
      rw [ghostEq, readValue, ← configEq]
      have readyNative : (G.fromSequentialConfig (ghost sample.1)).cut.Ready event :=
        ⟨sourceReady.1, fun prior predecessor => sourceReady.2
          ((EventOrder.sequential.mem_predecessors prior event).mpr
            (G.order.predecessor_lt predecessor))⟩
      exact runKey_complete_congr (keys sample.1 supported) event actualReady readyNative _ _
  have nextCovered : tail.refs.CoversPrefix setup.program (rank + 1) := by
    change ContextRefs.CoversPrefix setup.program
      (refs.cons (name := name) (cell := .publicData payload) ⟨Sum.inr event, outputEq⟩) (rank + 1)
    exact covered.cons setup.program _ event rfl atRank
  have tailComparison := continuation nextCovered staged nextSource nextGhost
    (fun sample present => by
      change @(sampleSuccessor name (source sample.1) (pick sample.2)).revelations =
        @(sampleSuccessor name original (L.someValue payload)).revelations
      simp only [sampleSuccessor]
      rw [revelations sample.1 (support sample present).1])
    (fun sample present => by
      change (sampleSuccessor name (source sample.1) (pick sample.2)).registry =
        (sampleSuccessor name original (L.someValue payload)).registry
      simp only [sampleSuccessor]
      rw [registry sample.1 (support sample present).1])
    (fun sample present => (nextFacts sample present).1)
    (fun sample present => (nextFacts sample present).2.1)
    (fun sample present => (nextFacts sample present).2.2.1)
    (fun sample => members sample.1)
    (fun sample present => submitting sample.1 (support sample present).1)
    (fun sample present owner node actor observation active later =>
      future sample.1 (support sample present).1 owner node actor observation active (by omega))
    Prod.snd
    (fun sample present => by
      have supported := (support sample present).1
      have reached := (support sample present).2
      have nextBoundary := native_chance_completionBoundary scheduler (players sample.1) event
        ownerless solitary (execution sample.1) sample.2
        (by simpa only [atRank] using boundary sample.1 supported) (budget sample.1 supported)
        (clear sample.1 supported) reached (complete sample.1 supported _ reached)
      simpa only [atRank] using nextBoundary.1)
    (fun sample present => (native_chance_completionBoundary scheduler (players sample.1) event
      ownerless solitary (execution sample.1) sample.2
      (by simpa only [atRank] using boundary sample.1 (support sample present).1)
      (budget sample.1 (support sample present).1) (clear sample.1 (support sample present).1)
      (support sample present).2 (complete sample.1 (support sample present).1 _
        (support sample present).2)).2.1)
    (fun sample present => (nextFacts sample present).2.2.2) nextNoise factorNext
  obtain ⟨policy, comparison⟩ := tailComparison
  refine ⟨policy, ?_⟩
  have nativeDistribution : (staged.bind fun sample => app.runToHorizon scheduler (players sample.1)
      horizon sample.2) = prior.bind (fun seed => app.runToHorizon scheduler (players seed)
        horizon (execution seed)) := by
    simp only [staged, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    apply bind_congr_on_support _
    intro seed _
    exact (app.runToHorizon_eq_runUntilHorizon_bind scheduler (players seed)
      (fun current => event ∈ current.application.config.cut.completed) horizon
      (execution seed)).symm
  rw [nativeDistribution] at comparison
  have sourceDistribution : (staged.bind fun sample => setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (Function.update
        (setup.informationGraph.prefixProfile reference) focal policy)
        setup.informationGraph.canonicalScheduler) (eventCount next) (nextGhost sample)) =
      prior.bind (fun seed => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler)
        (eventCount (.sample name fresh distribution next)) (ghost seed)) := by
    let onward := fun current : Config Player L ((name, .publicData payload) :: Γ) ×
        setup.informationGraph.Config => setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (Function.update
        (setup.informationGraph.prefixProfile reference) focal policy)
        setup.informationGraph.canonicalScheduler) (eventCount next) current.2
    have initial : (staged.bind fun sample => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler) (eventCount next) (nextGhost sample)) =
        (staged.map (fun sample => (nextSource sample, nextGhost sample))).bind onward := by
      rw [PMF.bind_map]
      rfl
    rw [initial, marginal, PMF.bind_bind, PMF.bind_map]
    apply bind_congr_on_support _
    intro seed supported
    obtain ⟨history, historyAt⟩ := histories seed supported
    obtain ⟨inputs, sourceReach⟩ := reachable seed supported
    obtain ⟨sourceReady, headLaw, _⟩ := sample_source_successor intended target agrees frame fresh
      distribution next rfl (source seed) (revelations seed supported) (registry seed supported)
      (ghost seed) sourceReach (checkpoints seed supported) history historyAt
      (Function.update (setup.informationGraph.prefixProfile reference) focal policy)
    change (ghost seed).cut.Ready event at sourceReady
    rw [eventCount, show Nat.succ (eventCount next) = 1 + eventCount next by omega,
      runPlan_add]
    rw [headLaw, PMF.bind_map]
    simp only [Function.comp_def, PMF.bind_map]
    apply bind_congr_on_support _
    intro value _
    simp only [afterGhost, dite_eq_left sourceReady, onward]
    rfl
  change expect _ nativePayoff ≤ expect _ sourcePayoff at comparison
  change expect _ nativePayoff ≤ expect _ sourcePayoff
  rw [← sourceDistribution]
  exact comparison

private theorem graphPayoff_fromSequentialConfig
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excluded : Player → ℝ) (focal : Player) (ghost : setup.informationGraph.Config)
    {inputs : setup.informationGraph.Inputs} (reachable : ghost.Reachable inputs) :
    setup.graphPayoff deps parameter utility excluded focal
      ((serviceGraph setup deps).fromSequentialConfig ghost) =
        setup.graphPayoff setup.informationDependencies parameter utility excluded focal ghost := by
  unfold Setup.graphPayoff
  by_cases terminal : ghost.cut.Terminal
  · have nativeTerminal : ((serviceGraph setup deps).fromSequentialConfig ghost).cut.Terminal :=
      terminal
    rw [dite_eq_left nativeTerminal, dite_eq_left terminal]
    have nativeRanked := rankedConfig_fromSequentialConfig
      (graph := serviceGraph setup deps) reachable nativeTerminal
    have ranked : rankedConfig (graph := setup.informationGraph) ghost terminal = ghost := by
      exact rankedConfig_fromSequentialConfig (graph := setup.informationGraph) reachable terminal
    have same : (⟨rankedConfig (graph := serviceGraph setup deps)
        ((serviceGraph setup deps).fromSequentialConfig ghost) nativeTerminal,
        rankedConfig_terminal _ _⟩ : setup.informationGraph.gameSignature.Outcome) =
        ⟨rankedConfig (graph := setup.informationGraph) ghost terminal,
          rankedConfig_terminal _ _⟩ := Subtype.ext (nativeRanked.trans ranked.symm)
    exact congrArg (fun outcome => exclusionUtility setup.program excluded utility
      (setup.eventParameterOutcome parameter outcome) focal) same
  · have nativeNonterminal :
        ¬ ((serviceGraph setup deps).fromSequentialConfig ghost).cut.Terminal := terminal
    rw [dite_eq_right nativeNonterminal, dite_eq_right terminal]

theorem nativeSourceContinuation_terminal
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    (reference : setup.informationGraph.BehavioralProfile) (focal : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (spread : ∀ high low who, utility high who - utility low who ≤ forfeit)
    {rank : Nat} {point : setup.informationGraph.Config}
    (frame : SourceResidual setup wholeProfile rank point) (ended : eventCount frame.program = 0) :
    nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns wholeProfile
      reference focal deviation
      (fun final => setup.graphForfeitConfigPayoff deps parameter utility forfeit
        final.application.config focal)
      (setup.graphPayoff setup.informationDependencies parameter utility
        (Setup.leastUtility utility) focal) frame := by
  classical
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  let nativeValue := fun config : G.Config =>
    setup.graphForfeitConfigPayoff deps parameter utility forfeit config focal
  let sourceValue := setup.graphPayoff setup.informationDependencies parameter utility
    (Setup.leastUtility utility) focal
  intro _covered Seed prior _source ghost _revelations _registry _checkpoints reachable _histories
    members _submitting _future execution players boundary budget keys _noise _factor
  have atEnd : rank = G.order.eventCount := by
    have counts := frame.aligned.graphSuffix.countEq
    change rank + eventCount frame.program = G.order.eventCount at counts
    omega
  have terminal (seed : Seed) (supported : seed ∈ prior.support) :
      (execution seed).application.config.cut.Terminal := by
    change (execution seed).application.config.cut.completed = Finset.univ
    ext event
    simp only [Finset.mem_univ, iff_true]
    exact ((boundary seed supported).ordered.2 event).mpr (by rw [atEnd]; exact event.isLt)
  have nativeDistribution : (prior.bind fun seed => app.runToHorizon scheduler
    (players seed) horizon
      (execution seed)).map (fun final => final.application.config) =
        prior.map (fun seed => (execution seed).application.config) := by
    rw [PMF.map_bind]
    apply bind_congr_on_support _
    intro seed supported
    calc
      _ = (app.runToHorizon scheduler (players seed) horizon (execution seed)).map
          (fun _ => (execution seed).application.config) := by
        apply map_congr_on_support _
        intro final reached
        exact runRounds_config_eq_of_terminal scheduler (players seed) _ (execution seed) final
          (terminal seed supported) reached
      _ = PMF.pure _ := pmf_map_fun_const _ _
  have comparison (seed : Seed) (supported : seed ∈ prior.support) :
      nativeValue (execution seed).application.config ≤ sourceValue (ghost seed) := by
    obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialDistribution setup deps) horizon
      scheduler
      (players seed) (execution seed).environmentRecall.length (budget seed supported)
        (execution seed) (boundary seed supported).supported
    rw [serviceInitialDistribution_eq_inputs setup] at trace
    obtain ⟨inputs, _, facts⟩ := reactive_history_invariant (serviceTimeouts setup deps duration)
      leaks (setup.initialDistribution.map setup.eventInputs) horizon scheduler trace
    change setup.graphForfeitConfigPayoff deps parameter utility forfeit
      (execution seed).application.config focal ≤ sourceValue (ghost seed)
    rw [Setup.graphForfeitConfigPayoff_terminal _ _ _ _ _ _ (terminal seed supported)]
    have less := setup.graphForfeitPayoff_le deps parameter utility spread
      ⟨(execution seed).application.config, terminal seed supported⟩ facts.reachable focal
    refine less.trans_eq ?_
    rw [setup.graphPayoff_factors deps parameter utility (Setup.leastUtility utility) focal _ _
      (keys seed supported)]
    obtain ⟨_, ghostReach⟩ := reachable seed supported
    exact graphPayoff_fromSequentialConfig setup deps parameter utility (Setup.leastUtility utility)
      focal (ghost seed) ghostReach
  refine ⟨reference focal, ?_⟩
  have sourceDistribution : (prior.bind fun seed => setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (Function.update
        (setup.informationGraph.prefixProfile reference) focal (reference focal))
        setup.informationGraph.canonicalScheduler) (eventCount frame.program) (ghost seed)) =
        prior.map ghost := by
    simp only [ended, runPlan]
    rfl
  rw [sourceDistribution]
  change expect _ (nativeValue ∘ fun final : app.Execution => final.application.config) ≤ _
  rw [← expect_map, nativeDistribution, expect_map, expect_map]
  obtain ⟨nativeBound, _, nativeBounded⟩ :=
    setup.graphForfeitConfigPayoff_abs_bound deps parameter utility spread focal
  obtain ⟨sourceBound, _, sourceBounded⟩ :=
    setup.graphPayoff_abs_bound setup.informationDependencies parameter utility spread focal
  exact expect_mono comparison
    (payoffIntegrable_of_bounded prior _ fun seed => nativeBounded _)
    (payoffIntegrable_of_bounded prior _ fun seed => sourceBounded _)

end Vegas
