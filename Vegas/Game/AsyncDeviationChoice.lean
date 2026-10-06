/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncDeviationForeign
import Vegas.Game.SourceServiceDeviationChoice

/-! # Phases of one deviating player as source steps

Against the first-turn clients of a source profile, under a scheduler
satisfying the asynchronous contract, one player follows an arbitrary native
policy. Each phase completes the current event with one source step, and the
deviator's native traffic keeps depending on the decoded source state only
through the deviator's source view:

* in a phase of the deviator's own binding or disclosure, its choice of a
  source action is a behavioral choice of its source view
  (`Vegas.asyncDeviator_binding_factorization`,
  `Vegas.asyncDeviator_reveal_factorization`); the binding may fail;
* in a phase of public chance, the decoded state follows the source sampling
  law (`Vegas.asyncDeviation_sample_factorization`);
* in a phase of another player, that player's choice follows its source
  decision kernel, and the deviator's traffic depends on it only through its
  public effect (`Vegas.asyncDeviation_binding_factorization`,
  `Vegas.asyncDeviation_reveal_factorization`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Steps

/-- A completion run from a completion boundary within the horizon stops with
one source step of the ready event, at the next boundary within the horizon. -/
theorem completionRun_boundary_step {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (complete : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    {players : Player → (application setup leaks).Policy} (event : (graph setup).EventId)
    (start : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val start)
    (bounded : start.environmentRecall.length ≤ horizon)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon start).support) :
    ∃ (ready : start.application.config.cut.Ready event) (action : (graph setup).Action event),
      stopped.application.config ∈ (start.application.config.step event ready action).support ∧
      stopped.environmentRecall.length ≤ horizon ∧
      CompletionBoundary setup leaks scheduler players (event.val + 1) stopped := by
  have ready : start.application.config.cut.Ready event :=
    (ready_iff_rank setup _ event.val boundary.ordered event).mpr rfl
  have finished := completionRun_completes complete event start boundary bounded stopped reached
  obtain ⟨action, member⟩ := runUntil_completion_step setup leaks scheduler players event
    start.application.config boundary.ordered ready _ start stopped rfl reached finished
  obtain ⟨stoppedBounded, stoppedBoundary⟩ := CompletionBoundary.stopped event start boundary
    bounded stopped reached finished
  exact ⟨ready, action, member, stoppedBounded, stoppedBoundary⟩

end Steps

section Own

/-- **The deviator's binding.** In the phase of its own binding, the deviator's
arbitrary policy draws a source binding, possibly failed, that is a behavioral
choice of its source view; its traffic again factors through its new view. -/
theorem asyncDeviator_binding_factorization
    {Seed : Type} {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (turns : Nat) (wholeProfile : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup leaks).Policy)
    {Γ : SourceCtx Player L} {openNames : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ who name payload)
    (next : SourceProgram Player L ((name, .commitment who payload) :: Γ)
      (insert name openNames))
    (profile : BehavioralProfile (.commit name who fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name who fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.commit name who fresh guard next) profile refs (source seed).revelations
        (source seed).registry embedding refsBefore rank)
    (checkpoint : ∀ seed, SourceCheckpoint setup (source seed) refs rank
      (execution seed).application.config)
    (boundary : ∀ seed ∈ prior.support, CompletionBoundary setup leaks scheduler
      (deviatedTurnProfile bound turns (firstTurnTiming setup turns) wholeProfile who deviation)
      rank (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (noise : DecisionView who Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view who)).map fun extra => (config, extra)) :
    let index : Fin (eventCount (.commit name who fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let players := deviatedTurnProfile bound turns (firstTurnTiming setup turns) wholeProfile who
      deviation
    ∃ kernel : DecisionView who Γ → PMF (PublicationResult (L.Val payload)),
      ∃ nextNoise : DecisionView who ((name, .commitment who payload) :: Γ) → PMF _,
        (prior.bind fun seed =>
          ((application setup leaks).runUntilHorizon scheduler players
            (fun final => event ∈ final.application.config.cut.completed) horizon
            (execution seed)).map fun final =>
              (decodeSourcePrefix? (.commit name who fresh guard next) refs
                (source seed).registry (source seed).revelations embedding.ref 1
                final.application.config.store (decodeHistory setup.program
                  (final.application.config.history.map
                    (setup.eventGraph.fromModeCompletion .sequential))),
                (runtime setup).bindingTraffic leaks who final)) =
        ((prior.map source).bind fun config =>
          (kernel (config.view who)).map (commitSuccessor name guard config)).bind fun config =>
            (nextNoise (config.view who)).map fun extra =>
              ((some (Sum.inr (ProtocolState.entry next config)) :
                Option (ProtocolState (.commit name who fresh guard next))), extra) := by
  intro index event players
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have owned : (graph setup).actor? event = some who := by
    change (toEventGraph setup.program).actor? event = some who
    simpa [event, index, eventOwner?, eventCount] using
      (aligned prior.support_nonempty.choose).actorEq index
  have outputEq : (graph setup).outputLayout event = .binding who payload := by
    change outputLayout setup.program event = _
    simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using
      (aligned prior.support_nonempty.choose).graphSuffix.nodeEq index
  have decodedAction (choice : PublicationResult (L.Val payload)) :
      decodeEventAction setup.program event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
          some (.commit who name payload choice) := by
    have lookup := (aligned prior.support_nonempty.choose).actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
    simpa [event, index, outputEq, decodeEventAction] using lookup
  let decode := fun (seed : Seed) (final : (application setup leaks).Execution) =>
    decodeSourcePrefix? (.commit name who fresh guard next) refs (source seed).registry
      (source seed).revelations embedding.ref 1 final.application.config.store
      (decodeHistory setup.program (final.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)))
  let embed := fun config : Config Player L ((name, .commitment who payload) :: Γ) =>
    (some (Sum.inr (ProtocolState.entry next config)) :
      Option (ProtocolState (.commit name who fresh guard next)))
  have boundaryAt (seed : Seed) (supported : seed ∈ prior.support) :
      CompletionBoundary setup leaks scheduler players event.val (execution seed) := by
    rw [eventRank]
    exact boundary seed supported
  have successor (seed : Seed) (supported : seed ∈ prior.support)
      (final : (application setup leaks).Execution)
      (reached : final ∈ ((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).support) :
      ∃ choice : PublicationResult (L.Val payload),
        SourceCheckpoint setup (commitSuccessor name guard (source seed) choice)
          (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1)
          final.application.config ∧
        decode seed final = embed (commitSuccessor name guard (source seed) choice) := by
    obtain ⟨ready, action, member, _, _⟩ := completionRun_boundary_step contract.completes
      event (execution seed) (boundaryAt seed supported) (bounded seed supported) final reached
    let choice : PublicationResult (L.Val payload) :=
      cast (congrArg EventGraph.EventField.Action outputEq) action
    have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
      by simp only [choice, cast_cast, cast_eq]
    rw [actionEq, commit_step _ event ready outputEq codeEq choice,
      PMF.mem_support_pure_iff] at member
    have nextCheckpoint := (checkpoint seed).commit name guard event eventRank ready outputEq
      (fun ref => refsBefore ref index) choice (decodedAction choice)
    change SourceCheckpoint setup _ _ (rank + 1)
      ((execution seed).application.config.complete event ready _ _) at nextCheckpoint
    rw [← member] at nextCheckpoint
    refine ⟨choice, nextCheckpoint, ?_⟩
    simp only [decode, decodeSourcePrefix?_commit]
    exact congrArg (Option.map Sum.inr)
      (nextCheckpoint.decode next (fun tail => embedding.ref tail.succ))
  have embedInjective : Function.Injective embed := fun left right same =>
    ProtocolState.entry_injective next (Sum.inr_injective (Option.some.inj same))
  have : Nonempty (PublicationResult (L.Val payload)) := ⟨.failure⟩
  obtain ⟨kernel, _, nextNoise, law⟩ := exists_observed_choice_factorization prior
    source (fun seed => (runtime setup).bindingTraffic leaks who (execution seed))
    (fun config => config.view who) noise factor
    (fun seed => (application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed))
    ((runtime setup).bindingTraffic leaks who)
    (fun left leftSupport right rightSupport same => by
      have counts : horizon - (execution left).environmentRecall.length =
          horizon - (execution right).environmentRecall.length := by
        rw [show (execution left).environmentRecall = (execution right).environmentRecall from
          congrArg (fun value => value.2.2.1) same]
      obtain ⟨leftRank, leftRanked, leftSeen⟩ := roundsFrom_ranked setup leaks scheduler players
        _ (execution left) (boundaryAt left leftSupport).supported
      obtain ⟨rightRank, rightRanked, rightSeen⟩ := roundsFrom_ranked setup leaks scheduler
        players _ (execution right) (boundaryAt right rightSupport).supported
      have leftRankEq := isPrefix_unique leftRanked (boundaryAt left leftSupport).ordered
      have rightRankEq := isPrefix_unique rightRanked (boundaryAt right rightSupport).ordered
      subst leftRankEq
      unfold ReactiveApplication.runUntilHorizon
      rw [counts, runUntil_deviation_focal scheduler bound turns wholeProfile who deviation event
          (Or.inr owned) _ (execution left) (boundaryAt left leftSupport).ordered leftSeen,
        runUntil_deviation_focal scheduler bound turns wholeProfile who deviation event
          (Or.inr owned) _ (execution right) (boundaryAt right rightSupport).ordered
          (rightRankEq ▸ rightSeen)]
      exact focalPhase_traffic_congr scheduler who deviation (Or.inr owned) _ _ _
        (Or.inl ⟨(boundaryAt left leftSupport).ordered,
          (ready_iff_rank setup _ event.val (boundaryAt left leftSupport).ordered event).mpr rfl⟩)
        (Or.inl ⟨(boundaryAt right rightSupport).ordered,
          (ready_iff_rank setup _ event.val (boundaryAt right rightSupport).ordered event).mpr
            rfl⟩) same)
    (commitSuccessor name guard) (fun config => config.view who) decode embed
    (fun seed supported final reached => by
      obtain ⟨choice, _, decoded⟩ := successor seed supported final reached
      exact ⟨choice, decoded⟩)
    (fun left leftSupport leftFinal leftReached right rightSupport rightFinal rightReached
        leftChoice rightChoice leftDecoded rightDecoded same => by
      obtain ⟨leftActual, leftCheckpoint, leftEq⟩ := successor left leftSupport leftFinal
        leftReached
      obtain ⟨rightActual, rightCheckpoint, rightEq⟩ := successor right rightSupport rightFinal
        rightReached
      have leftConfig := embedInjective (leftDecoded.symm.trans leftEq)
      have rightConfig := embedInjective (rightDecoded.symm.trans rightEq)
      rw [leftConfig, rightConfig]
      exact Vegas.source_view_eq_of_observe_eq setup leaks _ who _ _ leftFinal rightFinal
        leftCheckpoint.agrees rightCheckpoint.agrees leftCheckpoint.history
        rightCheckpoint.history (observe_eq_of_bindingTraffic who same))
    (fun left leftChoice right rightChoice same =>
      commit_owner_view_reflects name guard left right leftChoice rightChoice same)
    (commitKernel profile)
  exact ⟨kernel, nextNoise, law⟩

/-- **The deviator's disclosure.** In the phase of its own guarded disclosure,
the deviator's arbitrary policy draws a source disclosure that is a behavioral
choice of its source view; its traffic again factors through its new view. -/
theorem asyncDeviator_reveal_factorization
    {Seed : Type} {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (turns : Nat) (wholeProfile : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup leaks).Policy)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment who payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (profile : BehavioralProfile (.reveal published who name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published who name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.reveal published who name fresh binding unresolved next) profile
      refs (source seed).revelations (source seed).registry embedding refsBefore rank)
    (checkpoint : ∀ seed, SourceCheckpoint setup (source seed) refs rank
      (execution seed).application.config)
    (boundary : ∀ seed ∈ prior.support, CompletionBoundary setup leaks scheduler
      (deviatedTurnProfile bound turns (firstTurnTiming setup turns) wholeProfile who deviation)
      rank (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (noise : DecisionView who Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view who)).map fun extra => (config, extra)) :
    let index : Fin (eventCount (.reveal published who name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let players := deviatedTurnProfile bound turns (firstTurnTiming setup turns) wholeProfile who
      deviation
    ∃ kernel : DecisionView who Γ → PMF Bool,
      ∃ nextNoise : DecisionView who ((published, .publication payload) :: Γ) → PMF _,
        (prior.bind fun seed =>
          ((application setup leaks).runUntilHorizon scheduler players
            (fun final => event ∈ final.application.config.cut.completed) horizon
            (execution seed)).map fun final =>
              (decodeSourcePrefix? (.reveal published who name fresh binding unresolved next)
                refs (source seed).registry (source seed).revelations embedding.ref 1
                final.application.config.store (decodeHistory setup.program
                  (final.application.config.history.map
                    (setup.eventGraph.fromModeCompletion .sequential))),
                (runtime setup).bindingTraffic leaks who final)) =
        ((prior.map source).bind fun config =>
          (kernel (config.view who)).map (revealSuccessor published binding config)).bind
            fun config => (nextNoise (config.view who)).map fun extra =>
              ((some (Sum.inr (ProtocolState.entry next config)) :
                Option (ProtocolState (.reveal published who name fresh binding unresolved
                  next))), extra) := by
  intro index event players
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have owned : (graph setup).actor? event = some who := by
    change (toEventGraph setup.program).actor? event = some who
    simpa [event, index, eventOwner?, eventCount] using
      (aligned prior.support_nonempty.choose).actorEq index
  have outputEq : (graph setup).outputLayout event = .publication payload := by
    change outputLayout setup.program event = _
    simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq (seed : Seed) :
      cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .resolve who payload (refs.get binding)
          (compileChecks (published := published) refs (source seed).registry
            (source seed).revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using (aligned seed).graphSuffix.nodeEq index
  have decodedAction (disclose : Bool) : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
        some (.reveal who name disclose) := by
    have lookup := (aligned prior.support_nonempty.choose).actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    simpa [event, index, outputEq, decodeEventAction] using lookup
  let decode := fun (seed : Seed) (final : (application setup leaks).Execution) =>
    decodeSourcePrefix? (.reveal published who name fresh binding unresolved next) refs
      (source seed).registry (source seed).revelations embedding.ref 1
      final.application.config.store
      (decodeHistory setup.program (final.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)))
  let embed := fun config : Config Player L ((published, .publication payload) :: Γ) =>
    (some (Sum.inr (ProtocolState.entry next config)) :
      Option (ProtocolState (.reveal published who name fresh binding unresolved next)))
  have boundaryAt (seed : Seed) (supported : seed ∈ prior.support) :
      CompletionBoundary setup leaks scheduler players event.val (execution seed) := by
    rw [eventRank]
    exact boundary seed supported
  have successor (seed : Seed) (supported : seed ∈ prior.support)
      (final : (application setup leaks).Execution)
      (reached : final ∈ ((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).support) :
      ∃ disclose : Bool,
        SourceCheckpoint setup (revealSuccessor published binding (source seed) disclose)
          (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1)
          final.application.config ∧
        decode seed final = embed (revealSuccessor published binding (source seed) disclose) := by
    obtain ⟨ready, action, member, _, _⟩ := completionRun_boundary_step contract.completes
      event (execution seed) (boundaryAt seed supported) (bounded seed supported) final reached
    let disclose : Bool := cast (congrArg EventGraph.EventField.Action outputEq) action
    have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose :=
      by simp only [disclose, cast_cast, cast_eq]
    rw [actionEq, (execution seed).application.config.step_eq_map_of_code _ ready outputEq _
      (codeEq seed) disclose
      (PMF.pure (disclosureResult published binding (source seed) disclose))
      (compileResolve_eval? refs (source seed).registry (source seed).revelations
        (source seed).state (execution seed).application.config.store (checkpoint seed).agrees
        binding disclose), PMF.pure_map, PMF.mem_support_pure_iff] at member
    have nextCheckpoint := (checkpoint seed).reveal published binding event eventRank ready
      outputEq (fun ref => refsBefore ref index) disclose (decodedAction disclose)
    change SourceCheckpoint setup _ _ (rank + 1)
      ((execution seed).application.config.complete event ready _ _) at nextCheckpoint
    rw [← member] at nextCheckpoint
    refine ⟨disclose, nextCheckpoint, ?_⟩
    simp only [decode, decodeSourcePrefix?_reveal]
    exact congrArg (Option.map Sum.inr)
      (nextCheckpoint.decode next (fun tail => embedding.ref tail.succ))
  have embedInjective : Function.Injective embed := fun left right same =>
    ProtocolState.entry_injective next (Sum.inr_injective (Option.some.inj same))
  obtain ⟨kernel, _, nextNoise, law⟩ := exists_observed_choice_factorization prior
    source (fun seed => (runtime setup).bindingTraffic leaks who (execution seed))
    (fun config => config.view who) noise factor
    (fun seed => (application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed))
    ((runtime setup).bindingTraffic leaks who)
    (fun left leftSupport right rightSupport same => by
      have counts : horizon - (execution left).environmentRecall.length =
          horizon - (execution right).environmentRecall.length := by
        rw [show (execution left).environmentRecall = (execution right).environmentRecall from
          congrArg (fun value => value.2.2.1) same]
      obtain ⟨leftRank, leftRanked, leftSeen⟩ := roundsFrom_ranked setup leaks scheduler players
        _ (execution left) (boundaryAt left leftSupport).supported
      obtain ⟨rightRank, rightRanked, rightSeen⟩ := roundsFrom_ranked setup leaks scheduler
        players _ (execution right) (boundaryAt right rightSupport).supported
      have leftRankEq := isPrefix_unique leftRanked (boundaryAt left leftSupport).ordered
      have rightRankEq := isPrefix_unique rightRanked (boundaryAt right rightSupport).ordered
      subst leftRankEq
      unfold ReactiveApplication.runUntilHorizon
      rw [counts, runUntil_deviation_focal scheduler bound turns wholeProfile who deviation event
          (Or.inr owned) _ (execution left) (boundaryAt left leftSupport).ordered leftSeen,
        runUntil_deviation_focal scheduler bound turns wholeProfile who deviation event
          (Or.inr owned) _ (execution right) (boundaryAt right rightSupport).ordered
          (rightRankEq ▸ rightSeen)]
      exact focalPhase_traffic_congr scheduler who deviation (Or.inr owned) _ _ _
        (Or.inl ⟨(boundaryAt left leftSupport).ordered,
          (ready_iff_rank setup _ event.val (boundaryAt left leftSupport).ordered event).mpr rfl⟩)
        (Or.inl ⟨(boundaryAt right rightSupport).ordered,
          (ready_iff_rank setup _ event.val (boundaryAt right rightSupport).ordered event).mpr
            rfl⟩) same)
    (revealSuccessor published binding) (fun config => config.view who) decode embed
    (fun seed supported final reached => by
      obtain ⟨disclose, _, decoded⟩ := successor seed supported final reached
      exact ⟨disclose, decoded⟩)
    (fun left leftSupport leftFinal leftReached right rightSupport rightFinal rightReached
        leftChoice rightChoice leftDecoded rightDecoded same => by
      obtain ⟨leftActual, leftCheckpoint, leftEq⟩ := successor left leftSupport leftFinal
        leftReached
      obtain ⟨rightActual, rightCheckpoint, rightEq⟩ := successor right rightSupport rightFinal
        rightReached
      have leftConfig := embedInjective (leftDecoded.symm.trans leftEq)
      have rightConfig := embedInjective (rightDecoded.symm.trans rightEq)
      rw [leftConfig, rightConfig]
      exact Vegas.source_view_eq_of_observe_eq setup leaks _ who _ _ leftFinal rightFinal
        leftCheckpoint.agrees rightCheckpoint.agrees leftCheckpoint.history
        rightCheckpoint.history (observe_eq_of_bindingTraffic who same))
    (fun left leftChoice right rightChoice same =>
      reveal_owner_view_reflects published binding left right leftChoice rightChoice same)
    (revealKernel profile)
  exact ⟨kernel, nextNoise, law⟩

end Own

section Chance

omit [IExpr.ResultTypes L] in
/-- A player's view after public chance determines its view before and the
sampled value. -/
theorem sample_view_reflects {Γ : SourceCtx Player L} {payload : L.Ty} (who : Player)
    (name : VarId) (left right : Config Player L Γ) (first second : L.Val payload)
    (same : (sampleSuccessor name left first).view who =
      (sampleSuccessor name right second).view who) :
    left.view who = right.view who ∧ first = second := by
  constructor
  · have earlier := congrArg (DecisionView.back false) same
    simpa only [back_sample_view] using earlier
  · have cell := congrArg (fun view : DecisionView who ((name, .publicData payload) :: Γ) =>
      view.1.cells.get .here) same
    simpa only [Config.view, sampleSuccessor, sourceObserve, Env.get, Env.cons] using cell

/-- **Public chance against one deviator.** In the phase of a public chance
event, the decoded source state follows the source sampling law, and the
deviator's traffic again factors through its new view. -/
theorem asyncDeviation_sample_factorization
    {Seed : Type} {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (turns : Nat) (wholeProfile : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup leaks).Policy)
    {Γ : SourceCtx Player L} {openNames : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (distribution : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) openNames)
    (profile : BehavioralProfile (.sample name fresh distribution next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.sample name fresh distribution next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.sample name fresh distribution next) profile refs (source seed).revelations
        (source seed).registry embedding refsBefore rank)
    (checkpoint : ∀ seed, SourceCheckpoint setup (source seed) refs rank
      (execution seed).application.config)
    (boundary : ∀ seed ∈ prior.support, CompletionBoundary setup leaks scheduler
      (deviatedTurnProfile bound turns (firstTurnTiming setup turns) wholeProfile who deviation)
      rank (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (noise : DecisionView who Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view who)).map fun extra => (config, extra)) :
    let index : Fin (eventCount (.sample name fresh distribution next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let players := deviatedTurnProfile bound turns (firstTurnTiming setup turns) wholeProfile who
      deviation
    ∃ nextNoise : DecisionView who ((name, .publicData payload) :: Γ) → PMF _,
      (prior.bind fun seed =>
        ((application setup leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            (decodeSourcePrefix? (.sample name fresh distribution next) refs
              (source seed).registry (source seed).revelations embedding.ref 1
              final.application.config.store (decodeHistory setup.program
                (final.application.config.history.map
                  (setup.eventGraph.fromModeCompletion .sequential))),
              (runtime setup).bindingTraffic leaks who final)) =
      ((prior.map source).bind fun config =>
        (L.evalDist distribution (sourcePublicEnv config.state)).map
          (sampleSuccessor name config)).bind fun config =>
          (nextNoise (config.view who)).map fun extra =>
            ((some (Sum.inr (ProtocolState.entry next config)) :
              Option (ProtocolState (.sample name fresh distribution next))), extra) := by
  intro index event players
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have chance : (graph setup).actor? event = none := by
    change (toEventGraph setup.program).actor? event = none
    simpa [event, index, eventOwner?, eventCount] using
      (aligned prior.support_nonempty.choose).actorEq index
  have outputEq : (graph setup).outputLayout event = .publicData payload := by
    change outputLayout setup.program event = _
    simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq (seed : Seed) : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload (compilePublicDist refs distribution) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using (aligned seed).graphSuffix.nodeEq index
  have decodedAction : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) = none := by
    have lookup := (aligned prior.support_nonempty.choose).actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
    simpa [event, index, outputEq, decodeEventAction] using lookup
  let decodeConfig := fun (seed : Seed) (config : (graph setup).Config) =>
    decodeSourcePrefix? (.sample name fresh distribution next) refs (source seed).registry
      (source seed).revelations embedding.ref 1 config.store
      (decodeHistory setup.program (config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)))
  let decode := fun (seed : Seed) (final : (application setup leaks).Execution) =>
    decodeConfig seed final.application.config
  let embed := fun config : Config Player L ((name, .publicData payload) :: Γ) =>
    (some (Sum.inr (ProtocolState.entry next config)) :
      Option (ProtocolState (.sample name fresh distribution next)))
  have embedInjective : Function.Injective embed := fun left right same =>
    ProtocolState.entry_injective next (Sum.inr_injective (Option.some.inj same))
  have boundaryAt (seed : Seed) (supported : seed ∈ prior.support) :
      CompletionBoundary setup leaks scheduler players event.val (execution seed) := by
    rw [eventRank]
    exact boundary seed supported
  have readyAt (seed : Seed) (supported : seed ∈ prior.support) :
      (execution seed).application.config.cut.Ready event :=
    (ready_iff_rank setup _ event.val (boundaryAt seed supported).ordered event).mpr rfl
  -- Every completed configuration decodes to the sampled source successor.
  have completedDecode (seed : Seed) (supported : seed ∈ prior.support)
      (value : L.Val payload) :
      decodeConfig seed ((execution seed).application.config.complete event
          (readyAt seed supported)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)) =
        embed (sampleSuccessor name (source seed) value) ∧
      SourceCheckpoint setup (sampleSuccessor name (source seed) value)
        (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1)
        ((execution seed).application.config.complete event (readyAt seed supported)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)) := by
    have nextCheckpoint := (checkpoint seed).sample name event eventRank (readyAt seed supported)
      outputEq (fun ref => refsBefore ref index) decodedAction value
    refine ⟨?_, nextCheckpoint⟩
    simp only [decodeConfig, decodeSourcePrefix?_sample]
    exact congrArg (Option.map Sum.inr)
      (nextCheckpoint.decode next (fun tail => embedding.ref tail.succ))
  -- The configuration law of the phase is the source sampling law.
  have phaseConfig (seed : Seed) (supported : seed ∈ prior.support) :
      ((application setup leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map (fun final => final.application.config) =
        (L.evalDist distribution (sourcePublicEnv (source seed).state)).map fun value =>
          (execution seed).application.config.complete event (readyAt seed supported)
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm) value) := by
    rw [← sample_step _ event (readyAt seed supported) outputEq refs distribution (codeEq seed)
      (source seed).state (checkpoint seed).agrees]
    exact sample_runUntil scheduler players event chance _ event.val
      (boundaryAt seed supported).ordered (readyAt seed supported) _ _ (execution seed) rfl
      (fun stopped reached => completionRun_completes contract.completes event (execution seed)
        (boundaryAt seed supported) (bounded seed supported) stopped reached)
  have successor (seed : Seed) (supported : seed ∈ prior.support)
      (final : (application setup leaks).Execution)
      (reached : final ∈ ((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).support) :
      ∃ value : L.Val payload,
        SourceCheckpoint setup (sampleSuccessor name (source seed) value)
          (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1)
          final.application.config ∧
        decode seed final = embed (sampleSuccessor name (source seed) value) := by
    have member : final.application.config ∈ (((application setup leaks).runUntilHorizon
        scheduler players (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).map (fun final => final.application.config)).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨final, reached, rfl⟩
    rw [phaseConfig seed supported, PMF.support_map] at member
    obtain ⟨value, _, configEq⟩ := member
    dsimp only at configEq
    obtain ⟨decoded, nextCheckpoint⟩ := completedDecode seed supported value
    rw [configEq] at nextCheckpoint
    refine ⟨value, nextCheckpoint, ?_⟩
    change decodeConfig seed final.application.config = _
    rw [← configEq]
    exact decoded
  have : Nonempty (L.Val payload) := ⟨L.someValue payload⟩
  obtain ⟨kernel, _, nextNoise, law⟩ := exists_observed_choice_factorization prior
    source (fun seed => (runtime setup).bindingTraffic leaks who (execution seed))
    (fun config => config.view who) noise factor
    (fun seed => (application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed))
    ((runtime setup).bindingTraffic leaks who)
    (fun left leftSupport right rightSupport same => by
      have counts : horizon - (execution left).environmentRecall.length =
          horizon - (execution right).environmentRecall.length := by
        rw [show (execution left).environmentRecall = (execution right).environmentRecall from
          congrArg (fun value => value.2.2.1) same]
      obtain ⟨leftRank, leftRanked, leftSeen⟩ := roundsFrom_ranked setup leaks scheduler players
        _ (execution left) (boundaryAt left leftSupport).supported
      obtain ⟨rightRank, rightRanked, rightSeen⟩ := roundsFrom_ranked setup leaks scheduler
        players _ (execution right) (boundaryAt right rightSupport).supported
      have leftRankEq := isPrefix_unique leftRanked (boundaryAt left leftSupport).ordered
      have rightRankEq := isPrefix_unique rightRanked (boundaryAt right rightSupport).ordered
      subst leftRankEq
      unfold ReactiveApplication.runUntilHorizon
      rw [counts, runUntil_deviation_focal scheduler bound turns wholeProfile who deviation event
          (Or.inl chance) _ (execution left) (boundaryAt left leftSupport).ordered leftSeen,
        runUntil_deviation_focal scheduler bound turns wholeProfile who deviation event
          (Or.inl chance) _ (execution right) (boundaryAt right rightSupport).ordered
          (rightRankEq ▸ rightSeen)]
      exact focalPhase_traffic_congr scheduler who deviation (Or.inl chance) _ _ _
        (Or.inl ⟨(boundaryAt left leftSupport).ordered, readyAt left leftSupport⟩)
        (Or.inl ⟨(boundaryAt right rightSupport).ordered, readyAt right rightSupport⟩) same)
    (sampleSuccessor name) (fun config => config.view who) decode embed
    (fun seed supported final reached => by
      obtain ⟨value, _, decoded⟩ := successor seed supported final reached
      exact ⟨value, decoded⟩)
    (fun left leftSupport leftFinal leftReached right rightSupport rightFinal rightReached
        leftChoice rightChoice leftDecoded rightDecoded same => by
      obtain ⟨leftActual, leftCheckpoint, leftEq⟩ := successor left leftSupport leftFinal
        leftReached
      obtain ⟨rightActual, rightCheckpoint, rightEq⟩ := successor right rightSupport rightFinal
        rightReached
      have leftConfig := embedInjective (leftDecoded.symm.trans leftEq)
      have rightConfig := embedInjective (rightDecoded.symm.trans rightEq)
      rw [leftConfig, rightConfig]
      exact Vegas.source_view_eq_of_observe_eq setup leaks _ who _ _ leftFinal rightFinal
        leftCheckpoint.agrees rightCheckpoint.agrees leftCheckpoint.history
        rightCheckpoint.history (observe_eq_of_bindingTraffic who same))
    (fun left leftChoice right rightChoice same =>
      sample_view_reflects who name left right leftChoice rightChoice same)
    (fun _ => PMF.pure (L.someValue payload))
  -- The choice kernel has the source sampling marginal.
  have expand (choice : Config Player L Γ → PMF (L.Val payload)) :
      ((prior.map source).bind fun config =>
        (choice config).map (sampleSuccessor name config)).map embed =
      (prior.map source).bind fun config =>
        (choice config).map fun value => embed (sampleSuccessor name config value) := by
    rw [PMF.map_bind]
    congr 1
    funext config
    rw [PMF.map_comp]
    rfl
  have nativeMarginal : (prior.bind fun seed =>
      ((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).map (decode seed)) =
      (prior.map source).bind fun config =>
        (L.evalDist distribution (sourcePublicEnv config.state)).map fun value =>
          embed (sampleSuccessor name config value) := by
    rw [PMF.bind_map]
    apply bind_congr_on_support _
    intro seed supported
    have through : ((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).map (decode seed) =
        (((application setup leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map (fun final => final.application.config)).map
            (decodeConfig seed) := by
      rw [PMF.map_comp]
      rfl
    rw [through, phaseConfig seed supported, PMF.map_comp]
    apply map_congr_on_support _
    intro value _
    exact (completedDecode seed supported value).1
  have lawMarginal : (prior.bind fun seed =>
      ((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).map (decode seed)) =
      (prior.map source).bind fun config =>
        (kernel (config.view who)).map fun value => embed (sampleSuccessor name config value) := by
    have projected := congrArg (PMF.map Prod.fst) law
    simp only [PMF.map_comp, Function.comp_def, PMF.map_bind, pmf_map_fun_const,
      pmf_bind_pure_eq_map] at projected
    exact projected
  refine ⟨nextNoise, law.trans ?_⟩
  congr 1
  apply pmf_map_injective embedInjective
  rw [expand, expand]
  exact lawMarginal.symm.trans nativeMarginal

end Chance

section Foreign

/-- At a completion boundary of the deviated first-turn profile, another
owner of the ready event has submitted only at its turns, has used only its
counted slots, has no turn there yet and no submission for it. -/
theorem foreign_boundary_facts {scheduler : (application setup leaks).Scheduler}
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {wholeProfile : BehavioralProfile setup.program} {who : Player}
    {deviation : (application setup leaks).Policy} {event : (graph setup).EventId}
    {owner : Player} (foreign : owner ≠ who) (start : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      (deviatedTurnProfile bound turns (firstTurnTiming setup turns) wholeProfile who deviation)
      event.val start) :
    OwnSubmissionsAtTurn setup leaks start owner ∧ CanonicalSlotsUsed setup leaks start owner ∧
      ownerTurns owner event start = 0 ∧
      (runtime setup).eventRecorded leaks (start.recall owner) event = false := by
  obtain ⟨own, slots⟩ := canonicalSlots_roundsFrom scheduler
    (deviatedTurnProfile bound turns (firstTurnTiming setup turns) wholeProfile who deviation)
    owner (bound := bound) (firstTurnTiming setup turns) wholeProfile
    (by simp only [deviatedTurnProfile, Function.update_of_ne foreign]) _ start
    boundary.supported
  have untouched := boundary.untouched event rfl
  refine ⟨own, slots, ?_, ?_⟩
  · unfold ownerTurns
    rw [List.countP_eq_zero]
    intro entry member turn
    exact untouched owner entry member
      (PublicView.ownTurn?_spec _ owner event (of_decide_eq_true turn)).1
  · apply Bool.eq_false_of_not_eq_true
    intro recorded
    obtain ⟨entry, member, submitted⟩ := List.any_eq_true.mp recorded
    exact untouched owner entry member
      (PublicView.ownTurn?_spec _ owner event
        (own entry member event (of_decide_eq_true submitted))).1

/-- **Another player's binding against one deviator.** In the phase of
another player's binding, that player's choice follows its source decision
kernel, and the deviator's traffic again factors through its new source view:
the commitment's public envelope does not depend on the bound value. -/
theorem asyncDeviation_binding_factorization
    {Seed : Type} {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (wholeProfile : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup leaks).Policy)
    {Γ : SourceCtx Player L} {openNames : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (foreign : owner ≠ who)
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile refs (source seed).revelations
        (source seed).registry embedding refsBefore rank)
    (checkpoint : ∀ seed, SourceCheckpoint setup (source seed) refs rank
      (execution seed).application.config)
    (boundary : ∀ seed ∈ prior.support, CompletionBoundary setup leaks scheduler
      (deviatedTurnProfile bound turns (firstTurnTiming setup turns) wholeProfile who deviation)
      rank (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (noise : DecisionView who Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view who)).map fun extra => (config, extra)) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let players := deviatedTurnProfile bound turns (firstTurnTiming setup turns) wholeProfile who
      deviation
    ∃ nextNoise : DecisionView who ((name, .commitment owner payload) :: Γ) → PMF _,
      (prior.bind fun seed =>
        ((application setup leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            (decodeSourcePrefix? (.commit name owner fresh guard next) refs
              (source seed).registry (source seed).revelations embedding.ref 1
              final.application.config.store (decodeHistory setup.program
                (final.application.config.history.map
                  (setup.eventGraph.fromModeCompletion .sequential))),
              (runtime setup).bindingTraffic leaks who final)) =
      ((prior.map source).bind fun config =>
        (commitKernel profile (config.view owner)).map (commitSuccessor name guard config)).bind
          fun config => (nextNoise (config.view who)).map fun extra =>
            ((some (Sum.inr (ProtocolState.entry next config)) :
              Option (ProtocolState (.commit name owner fresh guard next))), extra) := by
  intro index event players
  let app := application setup leaks
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using
      (aligned prior.support_nonempty.choose).actorEq index
  have outputEq : (graph setup).outputLayout event = .binding owner payload := by
    change outputLayout setup.program event = _
    simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using
      (aligned prior.support_nonempty.choose).graphSuffix.nodeEq index
  have node : nodeView (graph setup) event = .bind owner payload outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_bind _ _
  have decodedAction (choice : PublicationResult (L.Val payload)) :
      decodeEventAction setup.program event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
          some (.commit owner name payload choice) := by
    have lookup := (aligned prior.support_nonempty.choose).actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
    simpa [event, index, outputEq, decodeEventAction] using lookup
  let decode := fun (seed : Seed) (final : app.Execution) =>
    decodeSourcePrefix? (.commit name owner fresh guard next) refs (source seed).registry
      (source seed).revelations embedding.ref 1 final.application.config.store
      (decodeHistory setup.program (final.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)))
  let embed := fun config : Config Player L ((name, .commitment owner payload) :: Γ) =>
    (some (Sum.inr (ProtocolState.entry next config)) :
      Option (ProtocolState (.commit name owner fresh guard next)))
  let action := fun choice : PublicationResult (L.Val payload) =>
    cast (congrArg EventGraph.EventField.Action outputEq.symm) choice
  let decided := fun (seed : Seed) (choice : PublicationResult (L.Val payload)) =>
    app.runUntilHorizon scheduler
      (Function.update (focalPlayers setup leaks who deviation) owner
        (decidedTurnPolicy setup leaks bound owner event (action choice)))
      (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
  have boundaryAt (seed : Seed) (supported : seed ∈ prior.support) :
      CompletionBoundary setup leaks scheduler players event.val (execution seed) := by
    rw [eventRank]
    exact boundary seed supported
  have readyAt (seed : Seed) (supported : seed ∈ prior.support) :
      (execution seed).application.config.cut.Ready event :=
    (ready_iff_rank setup _ event.val (boundaryAt seed supported).ordered event).mpr rfl
  -- The phase is the source kernel's mixture of decided runs.
  have phaseLaw (seed : Seed) (supported : seed ∈ prior.support) :
      app.runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed) =
        (commitKernel profile ((source seed).view owner)).bind (decided seed) := by
    unfold ReactiveApplication.runUntilHorizon
    rw [runUntil_deviation_decided scheduler bound turns wholeProfile who deviation event owner
      owned foreign (execution seed) (boundaryAt seed supported)
      ((commitKernel profile ((source seed).view owner)).map action) (fun current same => by
        have law := sourceServiceCanonicalPolicy_commit setup leaks fresh guard next wholeProfile
          profile refs (source seed) embedding refsBefore rank (aligned seed) current
          (by rw [same]; exact (checkpoint seed).agrees)
          (by rw [same]; exact (checkpoint seed).history)
          (by rw [same]; exact readyAt seed supported)
        rw [law, PMF.map_comp]
        rfl), PMF.bind_map]
    rfl
  -- A decided run completes the event with its action.
  have decidedDecode (seed : Seed) (supported : seed ∈ prior.support)
      (choice : PublicationResult (L.Val payload)) (final : app.Execution)
      (reached : final ∈ (decided seed choice).support) :
      decode seed final = embed (commitSuccessor name guard (source seed) choice) := by
    obtain ⟨own, slots, _, _⟩ := foreign_boundary_facts foreign (execution seed)
      (boundaryAt seed supported)
    have member := decided_completion_of_follows contract timely event (execution seed)
      (boundaryAt seed supported) (bounded seed supported) (readyAt seed supported) owned own
      (action choice) (by unfold EffectiveAction; rw [node]; trivial)
      (players := Function.update (focalPlayers setup leaks who deviation) owner
        (decidedTurnPolicy setup leaks bound owner event (action choice)))
      (by simp only [Function.update_self]) final reached
    rw [commit_step _ event (readyAt seed supported) outputEq codeEq choice,
      PMF.mem_support_pure_iff] at member
    have nextCheckpoint := (checkpoint seed).commit name guard event eventRank
      (readyAt seed supported) outputEq (fun ref => refsBefore ref index) choice
      (decodedAction choice)
    change SourceCheckpoint setup _ _ (rank + 1)
      ((execution seed).application.config.complete event (readyAt seed supported) _ _)
      at nextCheckpoint
    rw [← member] at nextCheckpoint
    simp only [decode, decodeSourcePrefix?_commit]
    exact congrArg (Option.map Sum.inr)
      (nextCheckpoint.decode next (fun tail => embedding.ref tail.succ))
  obtain ⟨nextNoise, nextFactor⟩ := exists_updated_observation_kernel_of_readout prior source
    (fun seed => (runtime setup).bindingTraffic leaks who (execution seed))
    (fun config => config.view who) noise factor
    (fun config => commitKernel profile (config.view owner)) (commitSuccessor name guard)
    (fun config => config.view who)
    (fun seed choice => (decided seed choice).map ((runtime setup).bindingTraffic leaks who))
    (fun left _ leftChoice _ right _ rightChoice _ same => by
      have earlier := congrArg (DecisionView.back (decide (owner = who))) same
      simpa only [back_commit_view] using earlier)
    (fun left leftSupport leftChoice _ right rightSupport rightChoice _ _ same => by
      obtain ⟨leftOwn, leftSlots, leftTurns, leftRecorded⟩ := foreign_boundary_facts foreign
        (execution left) (boundaryAt left leftSupport)
      obtain ⟨rightOwn, rightSlots, rightTurns, rightRecorded⟩ := foreign_boundary_facts foreign
        (execution right) (boundaryAt right rightSupport)
      have counts : horizon - (execution left).environmentRecall.length =
          horizon - (execution right).environmentRecall.length := by
        rw [show (execution left).environmentRecall = (execution right).environmentRecall from
          congrArg (fun value => value.2.2.1) same]
      have congruent := decidedBinding_readout_congr contract timely who deviation foreign
        outputEq codeEq node (execution left) (execution right) (readyAt left leftSupport)
        (readyAt right rightSupport) ((boundaryAt left leftSupport).untouched event rfl)
        ((boundaryAt right rightSupport).untouched event rfl) (action leftChoice)
        (action rightChoice) _ (execution left) (execution right)
        (DecidedRun.initial delay bound (execution left) (boundaryAt left leftSupport)
          (bounded left leftSupport) owner leftOwn leftSlots (action leftChoice))
        (by
          rw [counts]
          exact DecidedRun.initial delay bound (execution right) (boundaryAt right rightSupport)
            (bounded right rightSupport) owner rightOwn rightSlots (action rightChoice))
        (Prod.ext same (Prod.ext (leftTurns.trans rightTurns.symm)
          (leftRecorded.trans rightRecorded.symm)))
      have projected := congrArg (PMF.map Prod.fst) congruent
      simp only [PMF.map_comp] at projected
      change PMF.map (Prod.fst ∘ foreignReadout (leaks := leaks) who owner event)
          (app.runUntil scheduler _ _ (horizon - (execution left).environmentRecall.length)
            (execution left)) =
        PMF.map (Prod.fst ∘ foreignReadout (leaks := leaks) who owner event)
          (app.runUntil scheduler _ _ (horizon - (execution right).environmentRecall.length)
            (execution right))
      rw [← counts]
      exact projected)
  refine ⟨nextNoise, ?_⟩
  have nativeEq : (prior.bind fun seed =>
      (app.runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).map fun final => (decode seed final,
          (runtime setup).bindingTraffic leaks who final)) =
      (prior.bind fun seed => (commitKernel profile ((source seed).view owner)).bind fun choice =>
        ((decided seed choice).map ((runtime setup).bindingTraffic leaks who)).map fun extra =>
          (commitSuccessor name guard (source seed) choice, extra)).map
        fun pair => (embed pair.1, pair.2) := by
    rw [PMF.map_bind]
    apply bind_congr_on_support _
    intro seed supported
    rw [phaseLaw seed supported, PMF.map_bind, PMF.map_bind]
    apply bind_congr_on_support _
    intro choice _
    rw [PMF.map_comp, PMF.map_comp]
    apply map_congr_on_support _
    intro final reached
    exact Prod.ext (decidedDecode seed supported choice final reached) rfl
  change (prior.bind fun seed =>
      (app.runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).map fun final => (decode seed final,
          (runtime setup).bindingTraffic leaks who final)) = _
  rw [nativeEq, nextFactor, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  rfl

omit [IExpr.ResultTypes L] in
/-- Every player's view after a disclosure determines its published result. -/
theorem reveal_result_reflects {Γ : SourceCtx Player L} {name : VarId} {owner : Player}
    {payload : L.Ty} (who : Player) (published : VarId)
    (selected : HasVar Γ name (.commitment owner payload))
    (left right : Config Player L Γ) (first second : Bool)
    (same : (revealSuccessor published selected left first).view who =
      (revealSuccessor published selected right second).view who) :
    disclosureResult published selected left first =
      disclosureResult published selected right second := by
  have cell := congrArg (fun view : DecisionView who ((published, .publication payload) :: Γ) =>
    view.1.cells.get .here) same
  simpa only [Config.view, sourceObserve, Env.get, disclosureResult] using cell

/-- **Another player's disclosure against one deviator.** In the phase of
another player's guarded disclosure, that player's choice follows its source
decision kernel, and the deviator's traffic again factors through its new source
view: an effective disclosure publishes exactly the value its opening carries. -/
theorem asyncDeviation_reveal_factorization
    {Seed : Type} {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (wholeProfile : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup leaks).Policy)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty} (foreign : owner ≠ who)
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
    (execution : Seed → (application setup leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next) profile
      refs (source seed).revelations (source seed).registry embedding refsBefore rank)
    (checkpoint : ∀ seed, SourceCheckpoint setup (source seed) refs rank
      (execution seed).application.config)
    (boundary : ∀ seed ∈ prior.support, CompletionBoundary setup leaks scheduler
      (deviatedTurnProfile bound turns (firstTurnTiming setup turns) wholeProfile who deviation)
      rank (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (effective : ∀ seed ∈ prior.support, (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next)
        (source seed).registry (source seed).revelations)
    (noise : DecisionView who Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view who)).map fun extra => (config, extra)) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let players := deviatedTurnProfile bound turns (firstTurnTiming setup turns) wholeProfile who
      deviation
    ∃ nextNoise : DecisionView who ((published, .publication payload) :: Γ) → PMF _,
      (prior.bind fun seed =>
        ((application setup leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            (decodeSourcePrefix? (.reveal published owner name fresh binding unresolved next)
              refs (source seed).registry (source seed).revelations embedding.ref 1
              final.application.config.store (decodeHistory setup.program
                (final.application.config.history.map
                  (setup.eventGraph.fromModeCompletion .sequential))),
              (runtime setup).bindingTraffic leaks who final)) =
      ((prior.map source).bind fun config =>
        (revealKernel profile (config.view owner)).map
          (revealSuccessor published binding config)).bind fun config =>
          (nextNoise (config.view who)).map fun extra =>
            ((some (Sum.inr (ProtocolState.entry next config)) :
              Option (ProtocolState (.reveal published owner name fresh binding unresolved
                next))), extra) := by
  intro index event players
  let app := application setup leaks
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using
      (aligned prior.support_nonempty.choose).actorEq index
  have outputEq : (graph setup).outputLayout event = .publication payload := by
    change outputLayout setup.program event = _
    simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq (seed : Seed) :
      cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
          (compileChecks (published := published) refs (source seed).registry
            (source seed).revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using (aligned seed).graphSuffix.nodeEq index
  have node (seed : Seed) : nodeView (graph setup) event =
      .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs (source seed).registry
          (source seed).revelations binding) outputEq (codeEq seed) :=
    EventGraphRuntime.nodeView_eq_resolve _ _
  have checksEq (left right : Seed) :
      compileChecks (published := published) refs (source left).registry
          (source left).revelations binding =
        compileChecks (published := published) refs (source right).registry
          (source right).revelations binding := by
    have codes := (codeEq left).symm.trans (codeEq right)
    injection codes
  have decodedAction (disclose : Bool) : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
        some (.reveal owner name disclose) := by
    have lookup := (aligned prior.support_nonempty.choose).actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    simpa [event, index, outputEq, decodeEventAction] using lookup
  let decode := fun (seed : Seed) (final : app.Execution) =>
    decodeSourcePrefix? (.reveal published owner name fresh binding unresolved next) refs
      (source seed).registry (source seed).revelations embedding.ref 1
      final.application.config.store
      (decodeHistory setup.program (final.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)))
  let embed := fun config : Config Player L ((published, .publication payload) :: Γ) =>
    (some (Sum.inr (ProtocolState.entry next config)) :
      Option (ProtocolState (.reveal published owner name fresh binding unresolved next)))
  let action := fun disclose : Bool =>
    cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose
  let decided := fun (seed : Seed) (disclose : Bool) =>
    app.runUntilHorizon scheduler
      (Function.update (focalPlayers setup leaks who deviation) owner
        (decidedTurnPolicy setup leaks bound owner event (action disclose)))
      (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
  have boundaryAt (seed : Seed) (supported : seed ∈ prior.support) :
      CompletionBoundary setup leaks scheduler players event.val (execution seed) := by
    rw [eventRank]
    exact boundary seed supported
  have readyAt (seed : Seed) (supported : seed ∈ prior.support) :
      (execution seed).application.config.cut.Ready event :=
    (ready_iff_rank setup _ event.val (boundaryAt seed supported).ordered event).mpr rfl
  have resolvedAt (seed : Seed) (disclose : Bool) :
      EventGraph.EventCode.resolveOutput? (refs.get binding)
          (compileChecks (published := published) refs (source seed).registry
            (source seed).revelations binding) disclose
          (execution seed).application.config.store =
        some (disclosureResult published binding (source seed) disclose) := by
    have resolved := compiled_disclosure_result (graph := graph setup) published binding
      (source seed) refs
      (execution seed).application.config.store (checkpoint seed).agrees disclose
    rwa [EventGraph.EventCode.resolveOutput?_playerStore] at resolved
  have effectiveAt (seed : Seed) (supported : seed ∈ prior.support) (disclose : Bool)
      (chosen : disclose ∈ (revealKernel profile ((source seed).view owner)).support) :
      EffectiveAction (execution seed).application.config event (action disclose) := by
    unfold EffectiveAction
    rw [node seed]
    intro isTrue
    simp only [action, cast_cast, cast_eq] at isTrue
    subst isTrue
    rcases effective_reveal_supported fresh binding unresolved next profile (source seed)
        (effective seed supported) true chosen with impossible | ⟨value, _, result⟩
    · cases impossible
    · exact ⟨value, by rw [resolvedAt seed true, result]⟩
  -- The phase is the source kernel's mixture of decided runs.
  have phaseLaw (seed : Seed) (supported : seed ∈ prior.support) :
      app.runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed) =
        (revealKernel profile ((source seed).view owner)).bind (decided seed) := by
    unfold ReactiveApplication.runUntilHorizon
    rw [runUntil_deviation_decided scheduler bound turns wholeProfile who deviation event owner
      owned foreign (execution seed) (boundaryAt seed supported)
      ((revealKernel profile ((source seed).view owner)).map action) (fun current same => by
        have law := sourceServiceCanonicalPolicy_reveal setup leaks fresh binding unresolved next
          wholeProfile profile refs (source seed) embedding refsBefore rank (aligned seed) current
          (by rw [same]; exact (checkpoint seed).agrees)
          (by rw [same]; exact (checkpoint seed).history)
          (by rw [same]; exact readyAt seed supported)
        rw [law, PMF.map_comp]
        rfl), PMF.bind_map]
    rfl
  -- A decided run completes the event with its action.
  have decidedDecode (seed : Seed) (supported : seed ∈ prior.support) (disclose : Bool)
      (chosen : disclose ∈ (revealKernel profile ((source seed).view owner)).support)
      (final : app.Execution) (reached : final ∈ (decided seed disclose).support) :
      decode seed final = embed (revealSuccessor published binding (source seed) disclose) := by
    obtain ⟨own, slots, _, _⟩ := foreign_boundary_facts foreign (execution seed)
      (boundaryAt seed supported)
    have member := decided_completion_of_follows contract timely event (execution seed)
      (boundaryAt seed supported) (bounded seed supported) (readyAt seed supported) owned own
      (action disclose) (effectiveAt seed supported disclose chosen)
      (players := Function.update (focalPlayers setup leaks who deviation) owner
        (decidedTurnPolicy setup leaks bound owner event (action disclose)))
      (by simp only [Function.update_self]) final reached
    rw [(execution seed).application.config.step_eq_map_of_code _ (readyAt seed supported)
      outputEq _ (codeEq seed) disclose
      (PMF.pure (disclosureResult published binding (source seed) disclose))
      (compileResolve_eval? refs (source seed).registry (source seed).revelations
        (source seed).state (execution seed).application.config.store (checkpoint seed).agrees
        binding disclose), PMF.pure_map, PMF.mem_support_pure_iff] at member
    have nextCheckpoint := (checkpoint seed).reveal published binding event eventRank
      (readyAt seed supported) outputEq (fun ref => refsBefore ref index) disclose
      (decodedAction disclose)
    change SourceCheckpoint setup _ _ (rank + 1)
      ((execution seed).application.config.complete event (readyAt seed supported) _ _)
      at nextCheckpoint
    rw [← member] at nextCheckpoint
    simp only [decode, decodeSourcePrefix?_reveal]
    exact congrArg (Option.map Sum.inr)
      (nextCheckpoint.decode next (fun tail => embedding.ref tail.succ))
  obtain ⟨nextNoise, nextFactor⟩ := exists_updated_observation_kernel_of_readout prior source
    (fun seed => (runtime setup).bindingTraffic leaks who (execution seed))
    (fun config => config.view who) noise factor
    (fun config => revealKernel profile (config.view owner)) (revealSuccessor published binding)
    (fun config => config.view who)
    (fun seed disclose => (decided seed disclose).map ((runtime setup).bindingTraffic leaks who))
    (fun left _ leftChoice _ right _ rightChoice _ same =>
      reveal_view_reflects who published binding left right leftChoice rightChoice same)
    (fun left leftSupport leftChoice leftChosen right rightSupport rightChoice rightChosen views
        same => by
      have results := reveal_result_reflects who published binding (source left) (source right)
        leftChoice rightChoice views
      obtain ⟨leftOwn, leftSlots, leftTurns, leftRecorded⟩ := foreign_boundary_facts foreign
        (execution left) (boundaryAt left leftSupport)
      obtain ⟨rightOwn, rightSlots, rightTurns, rightRecorded⟩ := foreign_boundary_facts foreign
        (execution right) (boundaryAt right rightSupport)
      have counts : horizon - (execution left).environmentRecall.length =
          horizon - (execution right).environmentRecall.length := by
        rw [show (execution left).environmentRecall = (execution right).environmentRecall from
          congrArg (fun value => value.2.2.1) same]
      -- Both disclose alike, and a disclosure publishes the same value on both sides.
      have agree : leftChoice = rightChoice ∧ (leftChoice = true → ∃ value : L.Val payload,
          EventGraph.EventCode.resolveOutput? (refs.get binding)
            (compileChecks (published := published) refs (source left).registry
              (source left).revelations binding) true
            (execution left).application.config.store = some (.success value) ∧
          EventGraph.EventCode.resolveOutput? (refs.get binding)
            (compileChecks (published := published) refs (source left).registry
              (source left).revelations binding) true
            (execution right).application.config.store = some (.success value)) := by
        rcases effective_reveal_supported fresh binding unresolved next profile (source left)
            (effective left leftSupport) leftChoice leftChosen with leftFalse |
            ⟨leftValue, leftTrue, leftResult⟩ <;>
          rcases effective_reveal_supported fresh binding unresolved next profile
            (source right) (effective right rightSupport) rightChoice rightChosen with
            rightFalse | ⟨rightValue, rightTrue, rightResult⟩
        · subst leftFalse rightFalse
          exact ⟨rfl, fun impossible => by cases impossible⟩
        · subst leftFalse rightTrue
          rw [disclosureResult_false, rightResult] at results
          cases results
        · subst leftTrue rightFalse
          rw [disclosureResult_false, leftResult] at results
          cases results
        · subst leftTrue rightTrue
          rw [leftResult, rightResult] at results
          cases results
          refine ⟨rfl, fun _ => ⟨leftValue, ?_, ?_⟩⟩
          · rw [resolvedAt left true, leftResult]
          · rw [checksEq left right, resolvedAt right true, rightResult]
      obtain ⟨choices, published⟩ := agree
      subst choices
      have congruent := decidedReveal_readout_congr contract timely who deviation foreign
        (node left) (execution left) (execution right) (readyAt left leftSupport)
        (readyAt right rightSupport) ((boundaryAt left leftSupport).untouched event rfl)
        ((boundaryAt right rightSupport).untouched event rfl) leftChoice published
        _ (execution left) (execution right)
        (DecidedRun.initial delay bound (execution left) (boundaryAt left leftSupport)
          (bounded left leftSupport) owner leftOwn leftSlots (action leftChoice))
        (by
          rw [counts]
          exact DecidedRun.initial delay bound (execution right) (boundaryAt right rightSupport)
            (bounded right rightSupport) owner rightOwn rightSlots (action leftChoice))
        (Prod.ext same (Prod.ext (leftTurns.trans rightTurns.symm)
          (leftRecorded.trans rightRecorded.symm)))
      have projected := congrArg (PMF.map Prod.fst) congruent
      simp only [PMF.map_comp] at projected
      change PMF.map (Prod.fst ∘ foreignReadout (leaks := leaks) who owner event)
          (app.runUntil scheduler _ _ (horizon - (execution left).environmentRecall.length)
            (execution left)) =
        PMF.map (Prod.fst ∘ foreignReadout (leaks := leaks) who owner event)
          (app.runUntil scheduler _ _ (horizon - (execution right).environmentRecall.length)
            (execution right))
      rw [← counts]
      exact projected)
  refine ⟨nextNoise, ?_⟩
  have nativeEq : (prior.bind fun seed =>
      (app.runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).map fun final => (decode seed final,
          (runtime setup).bindingTraffic leaks who final)) =
      (prior.bind fun seed => (revealKernel profile ((source seed).view owner)).bind
        fun disclose => ((decided seed disclose).map
          ((runtime setup).bindingTraffic leaks who)).map fun extra =>
            (revealSuccessor published binding (source seed) disclose, extra)).map
        fun pair => (embed pair.1, pair.2) := by
    rw [PMF.map_bind]
    apply bind_congr_on_support _
    intro seed supported
    rw [phaseLaw seed supported, PMF.map_bind, PMF.map_bind]
    apply bind_congr_on_support _
    intro disclose chosen
    rw [PMF.map_comp, PMF.map_comp]
    apply map_congr_on_support _
    intro final reached
    exact Prod.ext (decidedDecode seed supported disclose chosen final reached) rfl
  change (prior.bind fun seed =>
      (app.runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).map fun final => (decode seed final,
          (runtime setup).bindingTraffic leaks who final)) = _
  rw [nativeEq, nextFactor, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  rfl

end Foreign

end Vegas
