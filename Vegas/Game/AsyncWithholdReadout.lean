/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncWithholdLaw
import Vegas.Game.ServiceWithheldForfeit
import Vegas.Game.AsyncDeviationReadout

/-! # Typed outcome of one deviation up to withholding

On a reveal-relaxed graph, against the first-turn clients of a source profile
that opens effectively, under a scheduler satisfying the asynchronous contract,
one player follows an arbitrary native policy. Along the runs on which it does
not withhold one of its effective disclosures, the typed outcome has at most
the law of the source run in which that player follows one source behavioral
policy; along the others, the typed outcome records a failed reveal of that
player (`Vegas.asyncDeviation_withheld_readout`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

open Classical in
/-- **One deviation up to withholding has a source outcome law.** On a
reveal-relaxed graph, under a scheduler satisfying the asynchronous contract
with timely delays, against the first-turn clients of a source profile that
opens effectively, every native policy of one player has a source policy such
that the typed outcome along the runs on which the player does not withhold
has at most the law of the source run in which that player follows the policy;
and on every run on which it withholds, the typed outcome records a failed
reveal of that player. -/
theorem asyncDeviation_withheld_readout [Finite Player]
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (profile : BehavioralProfile setup.program)
    (opens : ∀ player, (profile player).OpensEffectively setup.program []
      (Revelations.initial setup.context))
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy) :
    ∃ policy : BehavioralPolicy who setup.program,
      (∀ outcome,
        (((serviceApplication setup mode deadline leaks).roundsFrom
          (serviceInitialLaw setup mode) scheduler (deviatedTurnProfile bound turns
            (firstTurnTiming setup turns mode) profile who deviation) horizon).map
          fun execution => if DeviatorWithheld who execution.application.config then none
            else some (serviceSourceReadout setup mode deadline leaks
              ((serviceApplication setup mode deadline leaks).finished execution)))
          (some outcome) ≤
        ((setup.run (Function.update profile who policy)).map some) outcome) ∧
      ∀ execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom
          (serviceInitialLaw setup mode) scheduler (deviatedTurnProfile bound turns
            (firstTurnTiming setup turns mode) profile who deviation) horizon).support,
        DeviatorWithheld who execution.application.config →
        ∃ terminal, serviceSourceReadout setup mode deadline leaks
            ((serviceApplication setup mode deadline leaks).finished execution) = some terminal ∧
          0 < failedReveals setup.program who (publicOutcome setup.program terminal) := by
  have := Fintype.ofFinite Player
  let app := serviceApplication setup mode deadline leaks
  let players := deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) profile
    who deviation
  obtain ⟨ends, phases⟩ := ConcurrentPhaseEnds.exists (eventCount setup.program) setup.program
    rfl 0
  let start := fun state : EventGraphRuntime.State (serviceGraph setup mode) =>
    ReactiveApplication.Execution.initial app state
  -- Every initial execution is a completion boundary of rank zero.
  have initialBoundary (state : EventGraphRuntime.State (serviceGraph setup mode))
      (stateSupport : state ∈ (serviceInitialLaw setup mode).support) :
      CompletionBoundary setup leaks scheduler players 0 (start state) := by
    refine ⟨?_, ?_, ?_⟩
    · change start state ∈ (app.roundsFrom (serviceInitialLaw setup mode) scheduler
        players 0).support
      unfold ReactiveApplication.roundsFrom
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨state, stateSupport,
        (PMF.mem_support_pure_iff _ _).mpr rfl⟩
    · obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ stateSupport
      exact EventOrder.Cut.empty_isPrefix _
    · intro event _ observer entry member
      cases member
  -- After the phases the configuration is complete, and later rounds keep it.
  have finalFacts (state : EventGraphRuntime.State (serviceGraph setup mode))
      (stateSupport : state ∈ (serviceInitialLaw setup mode).support) (final : app.Execution)
      (reached : final ∈ (deviationPhases scheduler players horizon ends (start state)).support) :
      final.application.config.cut.IsPrefix (serviceGraph setup mode).order.eventCount ∧
        ConfigReaches setup (start state).application.config final.application.config ∧
        ∀ next ∈ (app.runToHorizon scheduler players horizon final).support,
          next.application.config = final.application.config := by
    obtain ⟨finalBoundary, _⟩ := ConcurrentPhaseEnds.boundary relaxed contract.completes players
      profile phases profile _ _ _ (outputEmbedding setup.program)
      (initialRefsBefore setup.program) (CompiledPolicySuffix.whole setup.program profile) _
      (initialBoundary state stateSupport) (Nat.zero_le _) final reached
    refine ⟨finalBoundary.ordered, deviationPhases_configReaches scheduler players horizon ends
      _ final reached, fun next moved => ?_⟩
    unfold ReactiveApplication.runToHorizon at moved
    exact runRounds_config_terminal scheduler players _ final next finalBoundary.ordered moved
  -- Nothing is completed at the start.
  have fresh (state : EventGraphRuntime.State (serviceGraph setup mode))
      (stateSupport : state ∈ (serviceInitialLaw setup mode).support) :
      ∀ event, (serviceGraph setup mode).actor? event = some who →
        event ∉ (start state).application.config.cut.completed := by
    intro event _ done
    have empty := (initialBoundary state stateSupport).ordered
    exact Nat.not_lt_zero _ ((empty.2 event).mp done)
  -- Every run decomposes through the phases.
  have supportFacts : ∀ execution ∈ (app.roundsFrom (serviceInitialLaw setup mode) scheduler
      players horizon).support, ∃ state ∈ (serviceInitialLaw setup mode).support,
      ∃ final ∈ (deviationPhases scheduler players horizon ends (start state)).support,
        execution.application.config = final.application.config := by
    intro execution member
    unfold ReactiveApplication.roundsFrom at member
    obtain ⟨state, stateSupport, moved⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    have toHorizon : app.runRounds scheduler players horizon (start state) =
        app.runToHorizon scheduler players horizon (start state) := rfl
    change execution ∈ (app.runRounds scheduler players horizon (start state)).support at moved
    rw [toHorizon, runToHorizon_eq_deviationPhases_bind scheduler players horizon ends] at moved
    obtain ⟨final, reached, later⟩ := (PMF.mem_support_bind_iff _ _ _).mp moved
    exact ⟨state, stateSupport, final, reached,
      (finalFacts state stateSupport final reached).2.2 execution later⟩
  -- The deviation law up to withholding from the initial law.
  let Seed := {initial // initial ∈ setup.initialLaw.support}
  let prior : PMF Seed := pmfToSubtype setup.initialLaw (fun _ member => member)
  let source := fun seed : Seed => setup.initialConfig seed.val
  let initialState := fun seed : Seed =>
    EventGraphRuntime.State.initial (graph := serviceGraph setup mode) (setup.eventInputs seed.val)
  let execution := fun seed : Seed => start (initialState seed)
  have seedSupport (seed : Seed) : initialState seed ∈ (serviceInitialLaw setup mode).support := by
    unfold serviceInitialLaw
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨seed.val, seed.property, rfl⟩
  obtain ⟨initialNoise, initialFactor⟩ := source_initial_memory_factorization setup
    (deadline := deadline) leaks who
  have factor : prior.map (fun seed => (source seed,
      (serviceRuntime setup mode deadline).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind fun config =>
        (initialNoise (config.view who)).map fun extra => (config, extra) := by
    have projected := congrArg (PMF.map fun pair => (pair.1.1, pair.2)) initialFactor
    dsimp only [prior, source, execution, start, initialState]
    rw [map_pmfToSubtype setup.initialLaw (fun _ member => member)
      (fun initial => (setup.initialConfig initial,
        (serviceRuntime setup mode deadline).bindingTraffic leaks who
          (ReactiveApplication.Execution.initial app
            (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
              (setup.eventInputs initial))))),
      map_pmfToSubtype setup.initialLaw (fun _ member => member) setup.initialConfig]
    simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def]
      using projected
  obtain ⟨policy, noise, bound⟩ := asyncDeviation_withholdLaw setup leaks relaxed contract
    timely turns profile who deviation phases profile
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program) (initialRefsBefore setup.program) prior source execution
    (fun _ => CompiledPolicySuffix.whole setup.program profile)
    (fun seed => SourceCheckpoint.initial setup seed.val)
    (fun seed _ => initialBoundary _ (seedSupport seed)) (fun _ _ => Nat.zero_le _)
    (fun _ player => opens player)
    (fun seed _ => not_deviatorWithheld_of_fresh _ (fresh _ (seedSupport seed)))
    initialNoise factor
  refine ⟨policy, fun outcome => ?_, fun execution member withheld => ?_⟩
  · let gate := fun final : app.Execution =>
      if DeviatorWithheld who final.application.config then none
      else some (serviceSourceReadout setup mode deadline leaks (app.finished final))
    have readoutEq (final : app.Execution) :
        serviceSourceReadout setup mode deadline leaks (app.finished final) =
          decodeState? (terminalRefs setup.program) final.application.config.store :=
      serviceSourceReadout_eq_decode setup leaks ⟨0, none, final⟩
    -- The run to the horizon keeps the configuration after the phases.
    have physical : (app.roundsFrom (serviceInitialLaw setup mode) scheduler players
        horizon).map gate = ((serviceInitialLaw setup mode).bind fun state =>
          deviationPhases scheduler players horizon ends (start state)).map gate := by
      unfold ReactiveApplication.roundsFrom
      rw [PMF.map_bind, PMF.map_bind]
      apply bind_congr_on_support _
      intro state stateSupport
      have toHorizon : app.runRounds scheduler players horizon (start state) =
          app.runToHorizon scheduler players horizon (start state) := rfl
      change (app.runRounds scheduler players horizon (start state)).map gate = _
      rw [toHorizon, runToHorizon_eq_deviationPhases_bind scheduler players horizon ends,
        PMF.map_bind, ← PMF.bind_pure_comp]
      apply bind_congr_on_support _
      intro final reached
      have keep := (finalFacts state stateSupport final reached).2.2
      rw [map_congr_on_support _ (g := fun _ => gate final) (fun next moved => by
        simp only [gate, readoutEq, keep next moved]), pmf_map_fun_const]
      rfl
    have toPrior : ((serviceInitialLaw setup mode).bind fun state =>
        deviationPhases scheduler players horizon ends (start state)) =
        prior.bind fun seed => deviationPhases scheduler players horizon ends (execution seed) := by
      unfold serviceInitialLaw
      rw [PMF.bind_map]
      conv_lhs => rw [← map_val_pmfToSubtype setup.initialLaw (fun _ member => member)]
      rw [PMF.bind_map]
      rfl
    have gateEq (seed : Seed) (final : app.Execution) :
        gate final = (withheldGate setup leaks who setup.program
          (ContextRefs.initial setup.context (outputLayout setup.program))
          (source seed).registry (source seed).revelations (outputEmbedding setup.program)
          final).map (fun pair => setup.protocolReadout pair.1) := by
      unfold withheldGate
      simp only [gate]
      split_ifs
      · rfl
      · rw [Option.map_some, readoutEq]
        exact congrArg some
          (serviceSourcePrefix?_terminal_readout setup mode final.application.config).symm
    have nativeEq : (app.roundsFrom (serviceInitialLaw setup mode) scheduler players
        horizon).map gate = (prior.bind fun seed =>
          (deviationPhases scheduler players horizon ends (execution seed)).map
            (withheldGate setup leaks who setup.program
              (ContextRefs.initial setup.context (outputLayout setup.program))
              (source seed).registry (source seed).revelations
              (outputEmbedding setup.program))).map
            (Option.map (fun pair => setup.protocolReadout pair.1)) := by
      rw [physical, toPrior, PMF.map_bind, PMF.map_bind]
      apply bind_congr_on_support _
      intro seed _
      rw [PMF.map_comp]
      apply map_congr_on_support _
      intro final _
      exact gateEq seed final
    change ((app.roundsFrom (serviceInitialLaw setup mode) scheduler players horizon).map gate)
      (some outcome) ≤ _
    rw [nativeEq]
    refine (map_some_apply_le bound (fun pair => setup.protocolReadout pair.1) outcome).trans
      (le_of_eq ?_)
    congr 1
    have admitted (player : Player) :
        (Function.update profile who policy player).Admitted setup.program
          (CommitmentInterface.forfeiture setup.program) :=
      BehavioralPolicy.admitted_forfeiture setup.program _
    have encodedState := setup.encoded_prefix_state
      (CommitmentInterface.forfeiture setup.program) (Function.update profile who policy) admitted
      (eventCount setup.program)
    have sourceLaw := setup.protocol_runBehavioral_eq
      (CommitmentInterface.forfeiture setup.program) (Function.update profile who policy) admitted
    rw [InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom] at sourceLaw
    have encodedReadout := congrArg (PMF.map setup.protocolReadout) encodedState
    simp only [PMF.map_comp, Function.comp_def, PMF.map_bind] at encodedReadout
    have stateLaw := encodedReadout.symm.trans (by
      simpa only [eventCount_eq_instructionCount, InformationModel.runBehavioral] using sourceLaw)
    rw [← stateLaw]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_fun_const]
    rw [PMF.bind_bind]
    conv_rhs => rw [← map_val_pmfToSubtype setup.initialLaw (fun _ member => member)]
    rw [PMF.bind_map]
    apply bind_congr_on_support _
    intro seed _
    rw [PMF.bind_map]
    exact PMF.bind_pure_comp _ _
  · obtain ⟨state, stateSupport, final, reached, same⟩ := supportFacts execution member
    obtain ⟨complete, reach, _⟩ := finalFacts state stateSupport final reached
    rw [same] at withheld
    obtain ⟨terminal, decoded, failed⟩ := DeviatorWithheld.failedReveals_pos reach
      (fresh state stateSupport) complete withheld
    refine ⟨terminal, ?_, failed⟩
    have readoutEq : serviceSourceReadout setup mode deadline leaks (app.finished execution) =
        decodeState? (terminalRefs setup.program) execution.application.config.store :=
      serviceSourceReadout_eq_decode setup leaks ⟨0, none, execution⟩
    rw [readoutEq, same]
    exact decoded

end Vegas
