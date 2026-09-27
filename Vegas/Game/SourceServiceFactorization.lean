/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDisclosureMemory
import Vegas.Game.SourceServiceCandidateObservation
import Vegas.Game.SourceServiceDisclosure
import Vegas.Pending.ReactiveOpeningLikelihood
import GameTheoryExtensions.Math.Probability.ConditionalNoise
import Vegas.Source.ObservationRecall

/-! # Source memory and actual service-channel factorization

The proof law retains both the effective source configuration and its original
private intentions. Only the former is decoded from the native execution.
Binding timing, passive sampling, replay, and inclusion use the existing
runtime evaluator. Their conditional likelihood is derived from those actual
operations, rather than supplied as an independent channel hypothesis.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Correlated initial draws with the same source view have identical native
traffic projections, including the genuine owned initial candidate catalogue. -/
theorem source_initial_traffic_eq
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (focal : Player) (left right : State L setup.context)
    (same : (setup.initialConfig left).view focal = (setup.initialConfig right).view focal) :
    (runtime setup).bindingTraffic leaks focal
        (ReactiveApplication.Execution.initial (application setup leaks)
          (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs left))) =
      (runtime setup).bindingTraffic leaks focal
        (ReactiveApplication.Execution.initial (application setup leaks)
          (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs right))) := by
  have first := SourceCheckpoint.initial setup left
  have second := SourceCheckpoint.initial setup right
  have observed := checkpoint_playerObservation_eq setup _ 0
    (ContextRefs.initial_coversPrefix setup.program) focal _ _ _ _
      (EventGraphRuntime.State.initial_invariant
        (graph := graph setup) (setup.eventInputs left)).reachable
      (EventGraphRuntime.State.initial_invariant
        (graph := graph setup) (setup.eventInputs right)).reachable
      first.ordered second.ordered first.agrees second.agrees first.history second.history same
  have paired := NativeReplay.initial (runtime setup) focal
    (setup.eventInputs left) (setup.eventInputs right) observed
  have publics : (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs left)).publicView =
      (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs right)).publicView := paired.publicView
  have candidates := EventGraphRuntime.State.initial_candidates_eq_of_observation
    (graph := graph setup) focal (setup.eventInputs left) (setup.eventInputs right) observed
  have views : (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs left)).playerView focal =
      (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs right)).playerView focal := by
    unfold EventGraphRuntime.State.playerView
    rw [publics, observed, candidates]
    rfl
  unfold EventGraphRuntime.bindingTraffic
  dsimp only [ReactiveApplication.Execution.initial]
  rw [views, publics]

/-- The induction starts from the actual supplied initial law. There is no
independence assumption on private types, and original and effective histories
are paired only at initialization, before any intention can be erased. -/
theorem source_initial_memory_factorization
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (focal : Player) :
    ∃ noise : DecisionView focal setup.context → FinDist _,
      setup.initialLaw.map (fun initial =>
        ((setup.initialConfig initial, setup.initialConfig initial),
          (runtime setup).bindingTraffic leaks focal
            (ReactiveApplication.Execution.initial (application setup leaks)
              (EventGraphRuntime.State.initial (graph := graph setup)
                (setup.eventInputs initial))))) =
      (setup.initialLaw.map fun initial =>
        (setup.initialConfig initial, setup.initialConfig initial)).bind fun pair =>
          (noise (pair.1.view focal)).map fun extra => (pair, extra) := by
  classical
  let read := fun initial : State L setup.context =>
    (runtime setup).bindingTraffic leaks focal
      (ReactiveApplication.Execution.initial (application setup leaks)
        (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)))
  let noise := fun view : DecisionView focal setup.context =>
    if present : ∃ initial ∈ setup.initialLaw.support,
        (setup.initialConfig initial).view focal = view then
      FinDist.pure (read present.choose)
    else FinDist.pure (read setup.initialLaw.support_nonempty.choose)
  refine ⟨noise, ?_⟩
  rw [FinDist.bind_map]
  change setup.initialLaw.bind (fun initial => FinDist.pure
      ((setup.initialConfig initial, setup.initialConfig initial), read initial)) = _
  apply FinDist.bind_congr
  intro initial supported
  have present : ∃ other ∈ setup.initialLaw.support,
      (setup.initialConfig other).view focal = (setup.initialConfig initial).view focal :=
    ⟨initial, supported, rfl⟩
  simp only [noise, dite_eq_left present, FinDist.map_pure]
  rw [show read initial = read present.choose from
    source_initial_traffic_eq setup leaks focal initial present.choose present.choose_spec.2.symm]

/-- A real grant, clock step or expiry preserves the traffic factorization.
The carried source configuration is proof data; the native application still
performs the specified command, including its public effects and service recall. -/
theorem source_maintenance_factorization
    {Seed : Type*} {Γ : SourceCtx Player L}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (focal : Player) (prior : FinDist Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (noise : DecisionView focal Γ → FinDist _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun extra => (config, extra))
    (command : EnvironmentCommand (graph setup))
    (maintenance : ∀ event, command ≠ .executeSample event) :
    ∃ nextNoise : DecisionView focal Γ → FinDist _,
      (prior.bind fun seed =>
        ((execution seed).environmentStep (application setup leaks) (.application command)).map
          fun final => (source seed, (runtime setup).bindingTraffic leaks focal final)) =
      (prior.map source).bind fun config =>
        (nextNoise (config.view focal)).map fun extra => (config, extra) := by
  obtain ⟨nextNoise, law⟩ := FinDist.exists_updated_observation_kernel_of_readout prior source
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun config => config.view focal) noise factor (fun _ => FinDist.pure Unit.unit)
    (fun config _ => config) (fun config => config.view focal)
    (fun seed _ => ((execution seed).environmentStep (application setup leaks)
      (.application command)).map ((runtime setup).bindingTraffic leaks focal))
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left _ _ _ right _ _ _ _ same =>
      (runtime setup).bindingTraffic_maintenance leaks (execution left) (execution right)
        focal same command maintenance)
  exact ⟨nextNoise, by simpa only [FinDist.pure_bind, FinDist.map_pure,
    FinDist.bind_pure, FinDist.map_id, FinDist.map_comp, Function.comp_def] using law⟩

/-- An actual replay roster preserves the same source-conditioned traffic
law while retaining all passive samples and all players' previous responses. -/
theorem source_replay_factorization
    {Seed : Type*} {Γ : SourceCtx Player L}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (focal : Player) (prior : FinDist Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (recalled : ∀ seed ∈ prior.support, (execution seed).InputRecall (application setup leaks))
    (noise : DecisionView focal Γ → FinDist _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun extra => (config, extra))
    (network : (runtime setup).NetworkPolicy leaks) (roster : List Player) :
    ∃ nextNoise : DecisionView focal Γ → FinDist _,
      (prior.bind fun seed =>
        ((runtime setup).runInteractionPlan leaks
          (fun _ => (application setup leaks).replayPolicy) network
          (roster.map ServiceInstruction.player) (execution seed)).map fun final =>
            (source seed, (runtime setup).bindingTraffic leaks focal final)) =
      (prior.map source).bind fun config =>
        (nextNoise (config.view focal)).map fun extra => (config, extra) := by
  obtain ⟨nextNoise, law⟩ := FinDist.exists_updated_observation_kernel_of_readout prior source
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun config => config.view focal) noise factor (fun _ => FinDist.pure Unit.unit)
    (fun config _ => config) (fun config => config.view focal)
    (fun seed _ => ((runtime setup).runInteractionPlan leaks
      (fun _ => (application setup leaks).replayPolicy) network
      (roster.map ServiceInstruction.player) (execution seed)).map
        ((runtime setup).bindingTraffic leaks focal))
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left leftSupport _ _ right rightSupport _ _ _ same =>
      (runtime setup).replay_window_focal_law leaks network roster focal
        (execution left) (execution right) (recalled left leftSupport)
        (recalled right rightSupport) same)
  exact ⟨nextNoise, by simpa only [FinDist.pure_bind, FinDist.map_pure,
    FinDist.bind_pure, FinDist.map_id, FinDist.map_comp, Function.comp_def] using law⟩

/-- Passive activation turns the complete traffic factorization into a law
for the player's actual input: its response history and current observation.
The same network sample is used on each coupled branch; no observer receives
another player's sample or any of the auxiliary proof projection. -/
theorem source_activation_input_factorization
    {Seed : Type*} {Γ : SourceCtx Player L}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (focal : Player) (prior : FinDist Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (noise : DecisionView focal Γ → FinDist _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun extra => (config, extra)) :
    ∃ channel : DecisionView focal Γ → FinDist
        (List (application setup leaks).PlayerEntry × (application setup leaks).PlayerView),
      (prior.bind fun seed =>
        ((execution seed).environmentStep (application setup leaks) (.activate focal)).map
          fun final => (source seed,
            (final.recall focal, final.observe (application setup leaks) focal))) =
      (prior.map source).bind fun config =>
        (channel (config.view focal)).map fun input => (config, input) := by
  let app := application setup leaks
  have coupled (left right : app.Execution)
      (same : (runtime setup).bindingTraffic leaks focal left =
        (runtime setup).bindingTraffic leaks focal right) :
      (left.environmentStep app (.activate focal)).map
          (fun final => (final.recall focal, final.observe app focal)) =
        (right.environmentStep app (.activate focal)).map
          (fun final => (final.recall focal, final.observe app focal)) := by
    have networks : left.network = right.network := congrArg Prod.fst same
    simp only [ReactiveApplication.Execution.activation_samples, FinDist.map_comp]
    rw [networks]
    apply FinDist.map_congr_of_eq_on_support
    intro sample _supported
    let first := left.sampledActivation app focal sample
    let second := right.sampledActivation app focal sample
    have equal := (runtime setup).bindingTraffic_activation leaks left right focal focal same sample
    have sampledNetworks : first.network = second.network := congrArg Prod.fst equal
    have receipts : first.receipts = second.receipts :=
      congrArg (fun traffic => traffic.2.1) equal
    have recalled : first.recall focal = second.recall focal :=
      congrArg (fun traffic => traffic.2.2.2.1) equal
    have views : first.application.playerView focal = second.application.playerView focal :=
      congrArg (fun traffic => traffic.2.2.2.2.1) equal
    have projected := congrArg (fun view : EventGraphRuntime.PlayerView (graph setup) =>
      (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
        ReactivePlayerView (graph setup))) views
    change (first.recall focal, first.observe app focal) =
      (second.recall focal, second.observe app focal)
    apply Prod.ext recalled
    change ReactiveApplication.PlayerView.mk _ _ _ = _
    rw [sampledNetworks]
    exact congrArg₂ (fun view evidence =>
      (⟨second.network.observe focal, view, evidence⟩ : app.PlayerView)) projected receipts
  obtain ⟨channel, law⟩ := FinDist.exists_updated_observation_kernel_of_readout prior source
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun config => config.view focal) noise factor (fun _ => FinDist.pure Unit.unit)
    (fun config _ => config) (fun config => config.view focal)
    (fun seed _ => ((execution seed).environmentStep app (.activate focal)).map
      fun final => (final.recall focal, final.observe app focal))
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left _ _ _ right _ _ _ _ same => coupled (execution left) (execution right) same)
  exact ⟨channel, by simpa only [FinDist.pure_bind, FinDist.map_pure,
    FinDist.bind_pure, FinDist.map_id, FinDist.map_comp, Function.comp_def] using law⟩

omit [IExpr.ResultTypes L] in
private theorem commit_view_reflects {Γ : SourceCtx Player L} {owner : Player}
    {payload : L.Ty} (focal : Player) (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (left right : Config Player L Γ)
    (first second : PublicationResult (L.Val payload))
    (same : (commitSuccessor name guard left first).view focal =
      (commitSuccessor name guard right second).view focal) :
    left.view focal = right.view focal := by
  have earlier := congrArg (DecisionView.back (decide (owner = focal))) same
  simpa only [back_commit_view] using earlier

omit [IExpr.ResultTypes L] in
private theorem commit_choice_of_owner_view {Γ : SourceCtx Player L} {owner : Player}
    {payload : L.Ty} (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (left right : Config Player L Γ) (first second : PublicationResult (L.Val payload))
    (same : (commitSuccessor name guard left first).view owner =
      (commitSuccessor name guard right second).view owner) : first = second := by
  have cell := congrArg (fun view : DecisionView owner ((name, .commitment owner payload) :: Γ) =>
    view.1.cells.get .here) same
  simp only [Config.view, commitSuccessor, sourceObserve, Env.get, Env.cons, ite_true] at cell
  exact Option.some.inj cell

/-- The actual randomized binding window, including protected final inclusion.
The allocator is read from the current public application state. Timing is a
proof mixture with its existing behavioral realization, not player scratch state. -/
def bindingPhaseTranscript
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks) (roster : List Player)
    (owner focal : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (offset : Nat) {slots : Nat} (timing : FinDist (Option (Fin slots)))
    (execution : (application setup leaks).Execution)
    (result : PublicationResult (L.Val payload)) :=
  let app := application setup leaks
  let serial := execution.application.publicView.bindingCount owner
  let family := fun selected => app.scheduledPolicy offset selected
    (fun _ _ => FinDist.pure
      ((runtime setup).reactiveBinding leaks owner event payload result serial)) app.replayPolicy
  let players := Function.update (fun _ => app.replayPolicy) owner
    (app.policyMixture timing family).policy
  ((runtime setup).runInteractionPlan leaks players network
    (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) execution).map
      ((runtime setup).bindingTraffic leaks focal)

/-- The binding constructor preserves the joint source/auxiliary factorization
even when original private histories differ from the decoded effective history.
The factor premise is the induction hypothesis for the previous prefix. Every
new channel equality is proved from the real scheduled response and inclusion. -/
theorem binding_successor_memory_factorization
    {Seed : Type*} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks) (roster : List Player)
    {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty}
    (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (focal : Player) (event : (graph setup).EventId)
    (prior : FinDist Seed) (source original : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (recalled : ∀ seed ∈ prior.support,
      (execution seed).InputRecall (application setup leaks))
    (published : ∀ seed ∈ prior.support, (execution seed).network.Satisfies fun message =>
      message.id ∈ (execution seed).network.ledger.map Message.id)
    (offset : Nat) (counts : ∀ seed ∈ prior.support,
      ((execution seed).recall owner).length = offset)
    {slots : Nat} (timing : FinDist (Option (Fin slots)))
    (noise : DecisionView focal Γ → FinDist _)
    (factor : prior.map (fun seed => ((source seed, original seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra))
    (choice : Config Player L Γ → FinDist (PublicationResult (L.Val payload))) :
    ∃ nextNoise : DecisionView focal ((name, .commitment owner payload) :: Γ) → FinDist _,
      (prior.bind fun seed => (choice (original seed)).bind fun result =>
        (bindingPhaseTranscript setup leaks network roster owner focal event payload offset
          timing (execution seed) result).map fun extra =>
            ((commitSuccessor name guard (source seed) result,
              commitSuccessor name guard (original seed) result), extra)) =
      ((prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (choice pair.2).map fun result =>
          (commitSuccessor name guard pair.1 result,
            commitSuccessor name guard pair.2 result)).bind fun pair =>
        (nextNoise (pair.1.view focal)).map fun extra => (pair, extra) := by
  apply FinDist.exists_updated_observation_kernel_of_readout prior
    (fun seed => (source seed, original seed))
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun pair => pair.1.view focal) noise factor (fun pair => choice pair.2)
    (fun pair result => (commitSuccessor name guard pair.1 result,
      commitSuccessor name guard pair.2 result)) (fun pair => pair.1.view focal)
  · intro left _ first _ right _ second _ same
    exact commit_view_reflects focal name guard left.1 right.1 first second same
  · intro left leftSupport first _ right rightSupport second _ same traffic
    have visible : focal = owner → first = second := by
      intro equal
      subst focal
      exact commit_choice_of_owner_view name guard (source left) (source right) first second same
    have publicEq : (execution left).application.publicView =
        (execution right).application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) traffic
    have serialEq := congrArg (fun view => view.bindingCount owner) publicEq
    have coupled := (runtime setup).scheduled_binding_mixture_inclusion_coupling leaks network
      roster (execution left) (execution right) (recalled left leftSupport)
        (recalled right rightSupport) owner focal event payload first second visible
          ((execution left).application.publicView.bindingCount owner) offset timing traffic
            ((counts left leftSupport).trans (counts right rightSupport).symm)
            (le_of_eq (counts left leftSupport)) (published left leftSupport)
    simpa only [bindingPhaseTranscript, serialEq] using coupled

/-- Restoring the owner's original intentions commutes with the real binding
window. The same conditional memory law supplies both the chosen binding and
the entire original source successor; foreign source state is retained. -/
theorem binding_phase_memory
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks) (roster : List Player)
    {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty}
    (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (focal : Player) (event : (graph setup).EventId)
    (source : Config Player L Γ) (execution : (application setup leaks).Execution)
    (offset : Nat) {slots : Nat} (timing : FinDist (Option (Fin slots)))
    (remember : DecisionView owner Γ → FinDist (List (OwnAction Player L)))
    (choose : DecisionView owner Γ → FinDist (PublicationResult (L.Val payload))) :
    let memory := bindingMemoryLaw name payload remember choose (source.view owner)
    ((source.restoreMemory owner remember).bind fun original =>
      (choose (original.view owner)).bind fun result =>
        (bindingPhaseTranscript setup leaks network roster owner focal event payload offset
          timing execution result).map fun traffic =>
            (traffic, commitSuccessor name guard original result)) =
      (memory.map Prod.fst).bind fun result =>
        ((memory.condOnFibre Prod.fst result).map Prod.snd).bind fun past =>
          (bindingPhaseTranscript setup leaks network roster owner focal event payload offset
            timing execution result).map fun traffic =>
              (traffic, (commitSuccessor name guard source result).withOwnHistory owner past) := by
  intro memory
  have law := bindingMemoryLaw_disintegrate name payload remember choose (source.view owner)
    (fun result past =>
      (bindingPhaseTranscript setup leaks network roster owner focal event payload offset
        timing execution result).map fun traffic =>
          (traffic, (commitSuccessor name guard source result).withOwnHistory owner past))
  simpa only [Config.restoreMemory, FinDist.bind_map, Config.view, Config.withOwnHistory,
    commitSuccessor, Function.update_self, Function.update_idem, memory] using law

/-- Failed disclosure intentions stay distinct in the proof joint law even
after an arbitrary actual service suffix. The runtime receives the effective
response; the original assessment's private history is restored conditionally.
No posterior about original intentions is inferred from the decoded native state. -/
theorem guarded_disclosure_service_memory
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding))
    (node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq)
    (remember : DecisionView owner Γ → FinDist (List (OwnAction Player L)))
    (choose : DecisionView owner Γ → FinDist Bool)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (remaining : List (ServiceInstruction (graph setup))) :
    let response := fun disclose => (runtime setup).serviceDecision leaks owner
      (execution.recall owner) (execution.observe (application setup leaks) owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    let memory := disclosureMemoryLaw published binding source.registry source.revelations
      remember choose (source.view owner)
    ((source.restoreMemory owner remember).bind fun original =>
      (choose (original.view owner)).bind fun intended =>
        ((runtime setup).runInteractionPlan leaks players network remaining
          (execution.respond (application setup leaks) owner (response intended))).map fun final =>
            (final, revealSuccessor published binding original intended)) =
      (memory.map Prod.fst).bind fun effective =>
        ((memory.condOnFibre Prod.fst effective).map Prod.snd).bind fun past =>
          ((runtime setup).runInteractionPlan leaks players network remaining
            (execution.respond (application setup leaks) owner (response effective))).map
              fun final =>
                (final, (revealSuccessor published binding source effective).withOwnHistory
                  owner past) := by
  intro response memory
  have law := guarded_disclosure_response_memory setup leaks published binding source refs
    execution agree event outputEq codeEq node remember choose
  have continued := congrArg (fun law => law.bind fun pair =>
    ((runtime setup).runInteractionPlan leaks players network remaining pair.1).map fun final =>
      (final, pair.2)) law
  simpa only [FinDist.bind_bind, FinDist.bind_map, response, memory] using continued

/-- Equal successful guarded publications supply the handler agreement needed
by the actual focal window coupling. Both candidates are recovered from their
current dynamic binding invariants; no initial-catalogue equality is assumed. -/
theorem guarded_opening_handler_focal
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (refs : ContextRefs (graph setup).layout Γ) (leftSource rightSource : Config Player L Γ)
    (left right : (application setup leaks).Execution)
    (leftAgrees : refs.Agrees leftSource.state left.application.config.store)
    (rightAgrees : refs.Agrees rightSource.state right.application.config.store)
    (leftBinding : left.application.BindingInvariant)
    (rightBinding : right.application.BindingInvariant)
    (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (leftCode : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs leftSource.registry
          leftSource.revelations binding))
    (rightCode : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs rightSource.registry
          rightSource.revelations binding))
    (leftNode : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs leftSource.registry leftSource.revelations
        binding) outputEq leftCode)
    (rightNode : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs rightSource.registry rightSource.revelations
        binding) outputEq rightCode)
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (leftTimely : left.application.WithinDeadline (runtime setup) event)
    (rightTimely : right.application.WithinDeadline (runtime setup) event)
    (value : L.Val payload)
    (leftSuccess : disclosureResult published binding leftSource true = .success value)
    (rightSuccess : disclosureResult published binding rightSource true = .success value)
    (focal : Player)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    ∃ candidate, candidate.1 = owner ∧
      left.application.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
      right.application.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
      rosterOpening? setup leaks owner event (left.observe (application setup leaks) owner) =
        some (candidate, ⟨payload, value⟩) ∧
      rosterOpening? setup leaks owner event (right.observe (application setup leaks) owner) =
        some (candidate, ⟨payload, value⟩) ∧
      ((application setup leaks).handle left.application
        ((runtime setup).windowEnvelope leaks owner event candidate ⟨payload, value⟩ left)).map
          (fun state => state.playerView focal) =
      ((application setup leaks).handle right.application
        ((runtime setup).windowEnvelope leaks owner event candidate ⟨payload, value⟩ left)).map
          (fun state => state.playerView focal) := by
  obtain ⟨candidate, leftAssociated, owned, leftValid, leftOpening⟩ :=
    guarded_rosterOpening_success setup leaks published binding leftSource refs left leftAgrees
      leftBinding event outputEq leftCode leftNode value leftSuccess
  obtain ⟨other, rightAssociated, _, rightValid, rightOpening⟩ :=
    guarded_rosterOpening_success setup leaks published binding rightSource refs right rightAgrees
      rightBinding event outputEq rightCode rightNode value rightSuccess
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun read => read.2.2.2.2.2) same
  have accepted : left.application.accepted = right.application.accepted :=
    congrArg EventGraphRuntime.PublicView.accepted publics
  have candidateEq : candidate = other := Option.some.inj
    (leftAssociated.symm.trans ((congrFun accepted (refs.get binding).field).trans rightAssociated))
  subst other
  refine ⟨candidate, owned, leftValid, rightValid, leftOpening, rightOpening, ?_⟩
  have stored (source : Config Player L Γ) (native : EventGraphRuntime.State (graph setup))
      (agrees : refs.Agrees source.state native.config.store)
      (success : disclosureResult published binding source true = .success value) :
      (refs.get binding).get? native.config.store = some (.success value) := by
    have original : source.state.get binding = .success value := by
      simp only [disclosureResult, revealSuccessor, ite_true, Env.cons_get_here] at success
      split at success
      · exact success
      · cases success
    simpa only [original, cellValue] using agrees binding
  have leftResolved := compiled_disclosure_result published binding leftSource refs
    left.application.config.store leftAgrees true
  have rightResolved := compiled_disclosure_result published binding rightSource refs
    right.application.config.store rightAgrees true
  rw [leftSuccess, EventGraph.EventCode.resolveOutput?_playerStore] at leftResolved
  rw [rightSuccess, EventGraph.EventCode.resolveOutput?_playerStore] at rightResolved
  have first := handle_opening_eq (runtime setup) left.application
    (owner, left.network.nextSerial owner) event candidate owner payload (refs.get binding)
      _ outputEq leftCode leftNode leftReady leftTimely rfl owned leftAssociated value leftValid
        (stored leftSource left.application leftAgrees leftSuccess) (.success value) leftResolved
  have second := handle_opening_eq (runtime setup) right.application
    (owner, left.network.nextSerial owner) event candidate owner payload (refs.get binding)
      _ outputEq rightCode rightNode rightReady rightTimely rfl owned rightAssociated value
        rightValid (stored rightSource right.application rightAgrees rightSuccess)
          (.success value) rightResolved
  change (handle (runtime setup) left.application
      ⟨(owner, left.network.nextSerial owner), .opening event candidate ⟨payload, value⟩⟩).map _ =
    (handle (runtime setup) right.application
      ⟨(owner, left.network.nextSerial owner), .opening event candidate ⟨payload, value⟩⟩).map _
  rw [first, second, Option.map_some, Option.map_some]
  apply congrArg some
  have views : left.application.playerView focal = right.application.playerView focal :=
    congrArg (fun read => read.2.2.2.2.1) same
  exact EventGraphRuntime.State.complete_playerView_congr left.application right.application focal
    publics (left.application.playerView_observation_eq right.application focal views)
      (congrArg EventGraphRuntime.PlayerView.remembered views)
      (congrArg EventGraphRuntime.PlayerView.candidates views) event leftReady rightReady
        _ _ _ _ (fun _ => rfl) (fun _ => rfl)

end Vegas.SourceProgram.RevealService
