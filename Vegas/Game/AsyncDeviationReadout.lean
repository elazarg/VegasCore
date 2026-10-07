/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncDeviationLaw
import Vegas.Game.SourceServiceDeviationReadout

/-! # Typed outcome of one deviation under an arbitrary scheduler

On a barrier-ordered graph, against the first-turn clients of a source profile,
under a scheduler satisfying the asynchronous contract, every native policy of
one player has the typed terminal-state law of the source run in which that
player follows one source behavioral policy (`Vegas.asyncDeviation_readout_law`). The policy may
bind failure, which the source represents as an unopenable commitment; the
forfeiture interface admits every such policy.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace SourceProgram

/-- An interface that admits forfeiture at every commitment admits every
policy. -/
theorem BehavioralPolicy.admitted_of_forfeiture {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (admission : CommitmentInterface program) →
    (∀ site, admission site = .forfeiture) → (policy : BehavioralPolicy who program) →
    policy.Admitted program admission
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, all, policy =>
      BehavioralPolicy.admitted_of_forfeiture next admission all policy
  | _, _, .commit _ _ _ _ next, admission, all, policy =>
      ⟨fun _ _ choice _ => by
        cases choice with
        | success value => exact CommitmentAdmission.admits_success _ value
        | failure => exact (CommitmentAdmission.admits_failure _).mpr (all none),
        BehavioralPolicy.admitted_of_forfeiture next (fun site => admission (some site))
          (fun site => all (some site)) policy.2⟩
  | _, _, .reveal _ _ _ _ _ _ next, admission, all, policy =>
      BehavioralPolicy.admitted_of_forfeiture next admission all policy.2

/-- The forfeiture interface admits every policy. -/
theorem BehavioralPolicy.admitted_forfeiture {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (policy : BehavioralPolicy who program) :
    policy.Admitted program (CommitmentInterface.forfeiture program) :=
  BehavioralPolicy.admitted_of_forfeiture program _ (fun _ => rfl) policy

end SourceProgram

section Clients

variable {setup : Setup (Player := Player) (L := L)}

/-- The turn-counted clients of a source profile follow the profile with
ineffective disclosure intentions replaced by withholding. -/
abbrev sourceServiceClientProfile (setup : Setup (Player := Player) (L := L))
    (original : BehavioralProfile setup.program) : BehavioralProfile setup.program :=
  normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context) original

/-- The clients' profile has only effective disclosures. -/
theorem sourceServiceClientProfile_effective (original : BehavioralProfile setup.program)
    (who : Player) :
    (sourceServiceClientProfile setup original who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context) :=
  (original who).normalizeDisclosureFrom_effective setup.program []
    (Revelations.initial setup.context) (fun view => PMF.pure view.2)

/-- The clients' profile has the original profile's source law. -/
theorem sourceServiceClientProfile_run [Finite Player]
    (original : BehavioralProfile setup.program) :
    setup.run (sourceServiceClientProfile setup original) = setup.run original := by
  unfold Setup.run
  apply bind_congr_on_support _
  intro initial _
  exact normalizeDisclosureProfile_runFrom setup.program original (setup.initialConfig initial)

end Clients

section Phases

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- Running to the horizon is running a list of phases, then on to the
horizon. -/
theorem runToHorizon_eq_deviationPhases_bind
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (horizon : Nat) :
    ∀ (ends : List Nat) (execution : (serviceApplication setup mode deadline leaks).Execution),
      (serviceApplication setup mode deadline leaks).runToHorizon scheduler players horizon
          execution =
        (deviationPhases scheduler players horizon ends execution).bind
          ((serviceApplication setup mode deadline leaks).runToHorizon scheduler players horizon)
  | [], execution => by simp only [deviationPhases, PMF.pure_bind]
  | high :: rest, execution => by
      rw [(serviceApplication setup mode deadline leaks).runToHorizon_eq_runUntilHorizon_bind
        scheduler players (BlockDone high) horizon execution]
      simp only [deviationPhases, PMF.bind_bind]
      apply bind_congr_on_support _
      intro middle _
      exact runToHorizon_eq_deviationPhases_bind scheduler players horizon rest middle

/-- **The phases of a program end at the end of the graph.** On a
barrier-ordered graph, under a scheduler that completes play, the phases of a
compiled residual program, from a completion boundary at its rank within the
horizon, stop at completion boundaries of the whole graph within the horizon. -/
theorem PhaseEnds.boundary (ordered : (serviceGraph setup mode).BarrierOrdered) {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (complete : CompletesPlay (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy)
    (wholeProfile : BehavioralProfile setup.program) {Γ : SourceCtx Player L}
    {names : Finset VarId} {program : SourceProgram Player L Γ names} {offset : Nat}
    {ends : List Nat} (phases : PhaseEnds program offset ends) :
    ∀ (profile : BehavioralProfile program) (refs : ContextRefs (graphLayout setup.program) Γ)
      (revelations : Revelations Γ) (registry : Registry Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding),
      CompiledPolicySuffix setup.program wholeProfile program profile refs revelations registry
        embedding refsBefore offset →
      ∀ execution : (serviceApplication setup mode deadline leaks).Execution,
      CompletionBoundary setup leaks scheduler players offset execution →
      execution.environmentRecall.length ≤ horizon →
      ∀ final ∈ (deviationPhases scheduler players horizon ends execution).support,
        CompletionBoundary setup leaks scheduler players (eventCount setup.program) final ∧
          final.environmentRecall.length ≤ horizon := by
  induction phases with
  | ret payoffs offset =>
      intro profile refs revelations registry embedding refsBefore aligned execution boundary
        bounded final reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      have counted := aligned.graphSuffix.countEq
      simp only [eventCount, Nat.add_zero] at counted
      rw [← counted]
      exact ⟨boundary, bounded⟩
  | @sample Γ names name payload fresh distribution next offset rest _ ih =>
      intro profile refs revelations registry embedding refsBefore aligned execution boundary
        bounded final reached
      let index : Fin (eventCount (.sample name fresh distribution next)) :=
        ⟨0, by simp [eventCount]⟩
      let event : (serviceGraph setup mode).EventId := embedding.event index
      have eventRank : event.val = offset := by
        simpa only [event, index, Fin.val_zero, Nat.add_zero] using
          aligned.graphSuffix.rankEq index
      have outputEq : (serviceGraph setup mode).outputLayout event = .publicData payload := by
        change outputLayout setup.program event = _
        simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
      have sealed : BlockSealed setup mode offset (offset + 1) := by
        have alone := sealed_of_alone (event := event) fun cut other ready otherReady =>
          ordered.ready_public_unique cut (by rw [outputEq]; trivial) ready otherReady
        rwa [eventRank] at alone
      have counted := aligned.graphSuffix.countEq
      simp only [eventCount] at counted
      simp only [deviationPhases] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have done := blockRun_completes complete (offset + 1) execution boundary bounded middle
        moved
      obtain ⟨middleBounded, middleBoundary⟩ := blockRun_boundary (Nat.le_succ _) sealed
        (by change offset + 1 ≤ eventCount setup.program; omega) execution boundary bounded
        middle moved done
      exact ih _ _ _ _ _ _ (aligned.sampleTail setup.program wholeProfile (_openNames := names)
        fresh distribution next profile refs revelations registry embedding refsBefore offset)
        middle middleBoundary middleBounded final later
  | @reveal Γ names published name owner payload fresh binding unresolved next offset rest _
      ih =>
      intro profile refs revelations registry embedding refsBefore aligned execution boundary
        bounded final reached
      let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      let event : (serviceGraph setup mode).EventId := embedding.event index
      have eventRank : event.val = offset := by
        simpa only [event, index, Fin.val_zero, Nat.add_zero] using
          aligned.graphSuffix.rankEq index
      have outputEq : (serviceGraph setup mode).outputLayout event = .publication payload := by
        change outputLayout setup.program event = _
        simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
      have sealed : BlockSealed setup mode offset (offset + 1) := by
        have alone := sealed_of_alone (event := event) fun cut other ready otherReady =>
          ordered.ready_public_unique cut (by rw [outputEq]; trivial) ready otherReady
        rwa [eventRank] at alone
      have counted := aligned.graphSuffix.countEq
      simp only [eventCount] at counted
      simp only [deviationPhases] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have done := blockRun_completes complete (offset + 1) execution boundary bounded middle
        moved
      obtain ⟨middleBounded, middleBoundary⟩ := blockRun_boundary (Nat.le_succ _) sealed
        (by change offset + 1 ≤ eventCount setup.program; omega) execution boundary bounded
        middle moved done
      exact ih _ _ _ _ _ _ (aligned.revealTail (whole := setup.program)
        (wholeProfile := wholeProfile) fresh binding unresolved next profile refs revelations
        registry embedding refsBefore offset) middle middleBoundary middleBounded final later
  | @block Γ names program offset rest count prefixed _ maximal _ ih =>
      intro profile refs revelations registry embedding refsBefore aligned execution boundary
        bounded final reached
      have tailAligned := CompiledPolicySuffix.commitTailMany wholeProfile count program prefixed
        profile refs revelations registry embedding refsBefore offset aligned
      have wall : BlockEnd setup mode (offset + count) :=
        CompiledSuffix.blockEnd maximal tailAligned.graphSuffix
      simp only [deviationPhases] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have done := blockRun_completes complete (offset + count) execution boundary bounded middle
        moved
      obtain ⟨middleBounded, middleBoundary⟩ := blockRun_boundary (Nat.le_add_right _ _)
        (BlockEnd.sealed ordered wall) wall.1 execution boundary bounded middle moved done
      exact ih _ _ _ _ _ _ tailAligned middle middleBoundary middleBounded final later

end Phases

variable [Fintype Player]

/-- **One deviation, initialized, phase by phase.** On a barrier-ordered graph,
the phases of the whole program, from the initial law, have the state law of a
source deviation jointly with the deviator's traffic, which depends on the
source state only through the deviator's source observation. -/
theorem asyncDeviation_initialized_factorization
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (profile : BehavioralProfile setup.program)
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (effective : ∀ player, (profile player).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    {ends : List Nat} (phases : PhaseEnds setup.program 0 ends) :
    let players := deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) profile who
      deviation
    ∃ policy : BehavioralPolicy who setup.program,
      ∃ noise : setup.ProtocolView who → PMF _,
        (((serviceInitialLaw setup mode).bind fun state =>
          deviationPhases scheduler players horizon ends
            (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks)
              state)).map fun final =>
            (serviceSourcePrefix? setup mode (eventCount setup.program)
              final.application.config,
              (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
          (setup.initialLaw.bind fun initial =>
            ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program
              (Function.update profile who policy)))^[eventCount setup.program]
              (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
                some).bind fun state =>
              (noise (setup.protocolObserve who state)).map fun extra => (state, extra) := by
  intro players
  let app := serviceApplication setup mode deadline leaks
  let Seed := {initial // initial ∈ setup.initialLaw.support}
  let prior : PMF Seed := pmfToSubtype setup.initialLaw (fun _ member => member)
  let source := fun seed : Seed => setup.initialConfig seed.val
  let execution := fun seed : Seed => ReactiveApplication.Execution.initial app
    (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
      (setup.eventInputs seed.val))
  obtain ⟨initialNoise, initialFactor⟩ := source_initial_memory_factorization setup
    (deadline := deadline) leaks who
  have factor : prior.map (fun seed => (source seed,
      (serviceRuntime setup mode deadline).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind fun config =>
        (initialNoise (config.view who)).map fun extra => (config, extra) := by
    have projected := congrArg (PMF.map fun pair => (pair.1.1, pair.2)) initialFactor
    dsimp only [prior, source, execution]
    rw [map_pmfToSubtype setup.initialLaw (fun _ member => member)
      (fun initial => (setup.initialConfig initial,
        (serviceRuntime setup mode deadline).bindingTraffic leaks who
          (ReactiveApplication.Execution.initial app
            (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
              (setup.eventInputs initial))))),
      map_pmfToSubtype setup.initialLaw (fun _ member => member) setup.initialConfig]
    simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def]
      using projected
  have initialBoundary (seed : Seed) : CompletionBoundary setup leaks scheduler players 0
      (execution seed) := by
    refine ⟨?_, EventOrder.Cut.empty_isPrefix _, ?_⟩
    · change execution seed ∈ (app.roundsFrom (serviceInitialLaw setup mode) scheduler
        players 0).support
      unfold ReactiveApplication.roundsFrom
      simp only [ReactiveApplication.runRounds, serviceInitialLaw]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨_, (PMF.mem_support_map_iff _ _ _).mpr
        ⟨seed.val, seed.property, rfl⟩, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
    · intro event _ observer entry member
      cases member
  obtain ⟨policy, noise, law⟩ := asyncDeviation_deviationLaw setup leaks ordered contract
    timely turns profile who deviation phases profile
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program) (initialRefsBefore setup.program) prior source execution
      (fun _ => CompiledPolicySuffix.whole setup.program profile)
      (fun seed => SourceCheckpoint.initial setup seed.val)
      (fun seed _ => initialBoundary seed) (fun _ _ => Nat.zero_le _)
      (fun _ player => effective player) initialNoise factor
  refine ⟨policy, noise, ?_⟩
  let combined := fun initial : State L setup.context =>
    (deviationPhases scheduler players horizon ends
      (ReactiveApplication.Execution.initial app
        (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
          (setup.eventInputs initial)))).map
      fun final => (serviceSourcePrefix? setup mode (eventCount setup.program)
        final.application.config,
        (serviceRuntime setup mode deadline).bindingTraffic leaks who final)
  let sourcePrefix := fun initial : State L setup.context =>
    ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program
      (Function.update profile who policy)))^[eventCount setup.program]
      (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map some
  have nativeLaw : prior.bind (fun seed => combined seed.val) =
      setup.initialLaw.bind combined := by
    refine (PMF.bind_map prior Subtype.val combined).symm.trans ?_
    exact congrArg (fun law => law.bind combined) (map_val_pmfToSubtype _ _)
  have sourceLaw : prior.bind (fun seed => sourcePrefix seed.val) =
      setup.initialLaw.bind sourcePrefix := by
    refine (PMF.bind_map prior Subtype.val sourcePrefix).symm.trans ?_
    exact congrArg (fun law => law.bind sourcePrefix) (map_val_pmfToSubtype _ _)
  change (prior.bind fun seed => combined seed.val) =
    (prior.bind fun seed => sourcePrefix seed.val).bind fun state =>
      (noise (setup.protocolObserve who state)).map fun extra => (state, extra) at law
  rw [nativeLaw, sourceLaw] at law
  rw [serviceInitialLaw, PMF.bind_map, PMF.map_bind]
  exact law

omit [Fintype Player] in
/-- **One deviation has the typed outcome law of a source deviation.** On a
barrier-ordered graph, against the first-turn clients of a source profile,
under a scheduler satisfying the asynchronous contract with timely delays,
every native policy of one player has exactly the typed terminal-state law of
the source run in which that player follows one source behavioral policy,
possibly binding failure, and every other player keeps its source policy. -/
theorem asyncDeviation_readout_law [Finite Player]
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (original : BehavioralProfile setup.program)
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy) :
    ∃ policy : BehavioralPolicy who setup.program,
      ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler (deviatedTurnProfile bound turns (firstTurnTiming setup turns mode)
          (sourceServiceClientProfile setup original) who deviation) horizon).map
          (fun execution => serviceSourceReadout setup mode deadline leaks
            ((serviceApplication setup mode deadline leaks).finished execution)) =
        (setup.run (Function.update original who policy)).map some := by
  classical
  have := Fintype.ofFinite Player
  let app := serviceApplication setup mode deadline leaks
  let normalized := sourceServiceClientProfile setup original
  let players := deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) normalized
    who deviation
  obtain ⟨ends, phases⟩ := PhaseEnds.exists (eventCount setup.program) setup.program rfl 0
  obtain ⟨policy, noise, joint⟩ := asyncDeviation_initialized_factorization setup leaks ordered
    contract timely turns normalized who deviation
    (fun player => sourceServiceClientProfile_effective original player) phases
  refine ⟨policy, ?_⟩
  -- The run to the horizon passes through every phase and then keeps the readout.
  have physical : (app.roundsFrom (serviceInitialLaw setup mode) scheduler players horizon).map
      (fun execution => serviceSourceReadout setup mode deadline leaks (app.finished execution)) =
      ((serviceInitialLaw setup mode).bind fun state => deviationPhases scheduler players
        horizon ends (ReactiveApplication.Execution.initial app state)).map
          (fun final => serviceSourceReadout setup mode deadline leaks (app.finished final)) := by
    unfold ReactiveApplication.roundsFrom
    rw [PMF.map_bind, PMF.map_bind]
    apply bind_congr_on_support _
    intro state stateSupport
    have toHorizon : app.runRounds scheduler players horizon
        (ReactiveApplication.Execution.initial app state) =
        app.runToHorizon scheduler players horizon
          (ReactiveApplication.Execution.initial app state) := rfl
    rw [toHorizon, runToHorizon_eq_deviationPhases_bind scheduler players horizon ends,
      PMF.map_bind]
    rw [← PMF.bind_pure_comp]
    apply bind_congr_on_support _
    intro final reached
    have initialBoundary : CompletionBoundary setup leaks scheduler players 0
        (ReactiveApplication.Execution.initial app state) := by
      refine ⟨?_, ?_, ?_⟩
      · change ReactiveApplication.Execution.initial app state ∈
          (app.roundsFrom (serviceInitialLaw setup mode) scheduler players 0).support
        unfold ReactiveApplication.roundsFrom
        exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨state, stateSupport,
          (PMF.mem_support_pure_iff _ _).mpr rfl⟩
      · obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ stateSupport
        exact EventOrder.Cut.empty_isPrefix _
      · intro event _ observer entry member
        cases member
    obtain ⟨finalBoundary, _⟩ := PhaseEnds.boundary ordered contract.completes players normalized
      phases normalized _ _ _ (outputEmbedding setup.program) (initialRefsBefore setup.program)
      (CompiledPolicySuffix.whole setup.program normalized) _ initialBoundary (Nat.zero_le _)
      final reached
    have terminal : final.application.config.cut.IsPrefix
        (serviceGraph setup mode).order.eventCount := finalBoundary.ordered
    unfold ReactiveApplication.runToHorizon
    rw [map_congr_on_support _
      (g := fun _ => serviceSourceReadout setup mode deadline leaks (app.finished final))
      (fun next moved => by
        have same := runRounds_config_terminal scheduler players _ final next terminal
          moved
        change serviceSourceReadout setup mode deadline leaks (some ⟨0, none, next⟩) =
          serviceSourceReadout setup mode deadline leaks (some ⟨0, none, final⟩)
        simp only [serviceSourceReadout, Option.bind_some, same]), pmf_map_fun_const]
    rfl
  rw [physical]
  have projected := congrArg (PMF.map (fun pair => setup.protocolReadout pair.1)) joint
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind, pmf_map_fun_const,
    pmf_bind_pure_eq_map] at projected
  simp only [serviceSourcePrefix?_terminal_readout] at projected
  have admitted (player : Player) :
      (Function.update normalized who policy player).Admitted setup.program
        (CommitmentInterface.forfeiture setup.program) :=
    BehavioralPolicy.admitted_forfeiture setup.program _
  have encodedState := setup.encoded_prefix_state (CommitmentInterface.forfeiture setup.program)
    (Function.update normalized who policy) admitted (eventCount setup.program)
  have sourceLaw := setup.protocol_runBehavioral_eq (CommitmentInterface.forfeiture setup.program)
    (Function.update normalized who policy) admitted
  rw [InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom] at sourceLaw
  have encodedReadout := congrArg (PMF.map setup.protocolReadout) encodedState
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind] at encodedReadout
  have terminal := projected.trans (encodedReadout.symm.trans (by
    simpa only [eventCount_eq_instructionCount, InformationModel.runBehavioral] using sourceLaw))
  rw [run_update_normalizeDisclosureProfile setup original who policy] at terminal
  have readoutEq (final : app.Execution) :
      serviceSourceReadout setup mode deadline leaks (app.finished final) =
        decodeState? (terminalRefs setup.program) final.application.config.store :=
    serviceSourceReadout_eq_decode setup leaks ⟨0, none, final⟩
  simp only [readoutEq, PMF.map_bind]
  exact terminal

end Vegas
