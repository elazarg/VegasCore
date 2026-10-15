/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFrontierPotential
import Interaction.ReactiveImplementationProfile
import Interaction.ReactiveRawRoundTrace
import Vegas.Pending.ReactiveAsyncContract

/-! # Actual posterior frontier conservation and terminal typed-store laws -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private theorem environment_frontier_exists (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks control.execution memories frontier)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (control.execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (control.execution.recall owner)).support)
    (expiry : ∀ event,
      .application (.expire event) ∈ (scheduler control.execution.environmentRecall
        (control.execution.observeEnvironment (runtime.reactiveApplication leaks))).support →
      ∀ next, next ∈ (control.execution.environmentStep
        (runtime.reactiveApplication leaks) (.application (.expire event))).support →
      runtime.ReactiveFrontier leaks next memories frontier)
    (command : (runtime.reactiveApplication leaks).Command)
    (selected : command ∈ (scheduler control.execution.environmentRecall
      (control.execution.observeEnvironment (runtime.reactiveApplication leaks))).support)
    (next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep
      (runtime.reactiveApplication leaks) command).support) :
    ∃ nextFrontier, runtime.ReactiveFrontier leaks next memories nextFrontier := by
  cases command with
  | wait =>
      exact related.passive_command_frontier_exists runtime leaks control.execution memories
        frontier .wait (Or.inl rfl) next reached
  | activate owner =>
      exact related.passive_command_frontier_exists runtime leaks control.execution memories
        frontier (.activate owner) (Or.inr (Or.inl ⟨owner, rfl⟩)) next reached
  | «include» id =>
      exact related.include_command_frontier_exists runtime leaks ordered inputs horizon scheduler
        control trace memories frontier profile consistent supported id next reached
  | application applicationCommand =>
      cases applicationCommand with
      | advanceClock =>
          exact related.passive_command_frontier_exists runtime leaks control.execution memories
            frontier (.application .advanceClock) (Or.inr (Or.inr rfl)) next reached
      | executeSample event =>
          exact related.sample_command_frontier_exists runtime leaks profile control.execution
            memories frontier consistent supported event next reached
      | expire event => exact ⟨frontier, expiry event selected next reached⟩

private theorem environment_potential_harmonic (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (independent : graph.ReadyIndependent profile)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks control.execution memories frontier)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (control.execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (control.execution.recall owner)).support)
    (expiry : ∀ event,
      .application (.expire event) ∈ (scheduler control.execution.environmentRecall
        (control.execution.observeEnvironment (runtime.reactiveApplication leaks))).support →
      ∀ next, next ∈ (control.execution.environmentStep
        (runtime.reactiveApplication leaks) (.application (.expire event))).support →
      runtime.ReactiveFrontier leaks next memories frontier)
    (command : (runtime.reactiveApplication leaks).Command)
    (selected : command ∈ (scheduler control.execution.environmentRecall
      (control.execution.observeEnvironment (runtime.reactiveApplication leaks))).support) :
    (control.execution.environmentStep (runtime.reactiveApplication leaks) command).bind
      (fun next => runtime.reactiveFrontierPotential leaks profile next memories) =
        runtime.reactiveFrontierPotential leaks profile control.execution memories := by
  have stable := runtime.entryEventStable_history leaks (inputs.map State.initial) horizon
    scheduler trace
  cases command with
  | wait =>
      exact related.passive_command_harmonic runtime leaks profile control.execution stable
        memories frontier consistent supported .wait (Or.inl rfl)
  | activate owner =>
      exact related.passive_command_harmonic runtime leaks profile control.execution stable
        memories frontier consistent supported (.activate owner) (Or.inr (Or.inl ⟨owner, rfl⟩))
  | «include» id =>
      exact related.include_command_harmonic runtime leaks ordered inputs horizon scheduler control
        trace stable memories frontier profile consistent supported id
  | application applicationCommand =>
      cases applicationCommand with
      | advanceClock =>
          exact related.passive_command_harmonic runtime leaks profile control.execution stable
            memories frontier consistent supported (.application .advanceClock)
              (Or.inr (Or.inr rfl))
      | executeSample event =>
          exact related.sample_command_harmonic runtime leaks profile independent control.execution
            stable memories frontier consistent supported event
      | expire event =>
          calc
            _ = (control.execution.environmentStep (runtime.reactiveApplication leaks)
                (.application (.expire event))).bind
                  (fun _ => graph.canonicalContinuation profile frontier) := by
              apply bind_congr_on_support
              intro next reached
              have recallEq := (runtime.reactiveApplication leaks).environmentStep_recall
                control.execution next (.application (.expire event)) reached
              have stableNext := (runtime.entryEventStable_serviceInvariant leaks
                (fun _ _ => PMF.pure (.application (.expire event)))).environment
                  control.execution next (.application (.expire event)) stable (by simp) reached
              exact (expiry event selected next reached).potential_eq runtime leaks profile next
                stableNext
                memories frontier (by simpa only [recallEq] using consistent)
                  (by simpa only [recallEq] using supported)
            _ = graph.canonicalContinuation profile frontier := PMF.bind_const _ _
            _ = _ := (related.potential_eq runtime leaks profile control.execution stable memories
              frontier consistent supported).symm

theorem round_posterior_frontier_exists_of_expiry (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (remaining : Nat)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (frontiers : ∀ memories : Player → List (Option graph.Completion),
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
        ∃ frontier, runtime.ReactiveFrontier leaks execution memories frontier)
    (expiry : ∀ memories frontier,
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
      runtime.ReactiveFrontier leaks execution memories frontier → ∀ event,
      .application (.expire event) ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment (runtime.reactiveApplication leaks))).support → ∀ next,
        next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
          (.application (.expire event))).support →
        runtime.ReactiveFrontier leaks next memories frontier)
    (next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈ ((runtime.reactiveApplication leaks).round scheduler
      (fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner))
        execution).support)
    (memories : Player → List (Option graph.Completion))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (next.recall owner)).support) :
    ∃ frontier, runtime.ReactiveFrontier leaks next memories frontier := by
  let app := runtime.reactiveApplication leaks
  let players := fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)
  change next ∈ (app.round scheduler players execution).support at reached
  rw [ReactiveApplication.round, PMF.support_bind] at reached
  obtain ⟨command, chosen, dispatched⟩ := Set.mem_iUnion₂.mp reached
  rw [ReactiveApplication.dispatch, PMF.support_bind] at dispatched
  obtain ⟨current, moved, resumed⟩ := Set.mem_iUnion₂.mp dispatched
  have recallEq := app.environmentStep_recall execution current command moved
  have currentConsistent : ∀ owner, (players owner).Consistent (current.recall owner) := by
    simpa only [recallEq] using consistent
  have currentFrontiers : ∀ saved : Player → List (Option graph.Completion),
      (∀ owner, saved owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (current.recall owner)).support) →
        ∃ frontier, runtime.ReactiveFrontier leaks current saved frontier := by
    intro saved retained
    have prior : ∀ owner, saved owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support := by simpa only [recallEq] using retained
    obtain ⟨frontier, related⟩ := frontiers saved prior
    exact environment_frontier_exists runtime leaks ordered profile inputs horizon scheduler
      ⟨remaining + 1, none, execution⟩ trace saved frontier related consistent prior
        (expiry saved frontier prior related) command chosen current moved
  cases actorEq : command.actor? app with
  | none =>
      simp only [ReactiveApplication.resume, actorEq, PMF.mem_support_pure_iff] at resumed
      subst next
      exact currentFrontiers memories supported
  | some who =>
      simp only [ReactiveApplication.resume, actorEq, ReactiveApplication.invoke, PMF.support_map,
        Set.mem_image] at resumed
      obtain ⟨action, positive, rfl⟩ := resumed
      obtain ⟨currentTrace⟩ :=
        app.raw_trace_environment (inputs.map State.initial) horizon scheduler
        remaining execution current command trace chosen moved
      obtain ⟨quiet, sent⟩ := runtime.reactiveEmission_history leaks
        (inputs.map State.initial) horizon scheduler ⟨remaining, some who, current⟩
          (by simpa only [actorEq] using currentTrace) who
      exact respond_policy_frontier_exists runtime leaks profile current currentConsistent
        currentFrontiers who quiet sent action positive memories supported

variable [Fintype Player]

theorem round_posterior_potential_of_expiry (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (independent : graph.ReadyIndependent profile)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (remaining : Nat)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (frontiers : ∀ memories : Player → List (Option graph.Completion),
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
        ∃ frontier, runtime.ReactiveFrontier leaks execution memories frontier)
    (expiry : ∀ memories frontier,
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
      runtime.ReactiveFrontier leaks execution memories frontier → ∀ event,
      .application (.expire event) ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment (runtime.reactiveApplication leaks))).support → ∀ next,
        next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
          (.application (.expire event))).support →
        runtime.ReactiveFrontier leaks next memories frontier) :
    ((runtime.reactiveApplication leaks).round scheduler
      (fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)) execution).bind
        (fun next => (independentProduct (fun owner =>
          (runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
            (next.recall owner))).bind
              (runtime.reactiveFrontierPotential leaks profile next)) =
      (independentProduct (fun owner =>
        (runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner))).bind
            (runtime.reactiveFrontierPotential leaks profile execution) := by
  let app := runtime.reactiveApplication leaks
  let implementations := fun owner => runtime.prescribedReactiveImplementation leaks owner
    (profile owner)
  change (app.round scheduler (fun owner => (implementations owner).policy) execution).bind
    (fun next => (independentProduct (fun owner =>
      (implementations owner).posterior (next.recall owner))).bind
        (runtime.reactiveFrontierPotential leaks profile next)) =
      (independentProduct (fun owner =>
        (implementations owner).posterior (execution.recall owner))).bind
          (runtime.reactiveFrontierPotential leaks profile execution)
  rw [← ReactiveApplication.round_disintegrate_profile implementations execution scheduler
    (runtime.reactiveFrontierPotential leaks profile)]
  apply bind_congr_on_support
  intro memories jointSupported
  have supported := (independentProduct_support_iff _ memories).mp jointSupported
  obtain ⟨frontier, related⟩ := frontiers memories supported
  calc
    _ = (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind
        (fun command => (execution.environmentStep app command).bind
          (fun next => runtime.reactiveFrontierPotential leaks profile next memories)) := by
      apply bind_congr_on_support
      intro command chosen
      apply bind_congr_on_support
      intro next reached
      obtain ⟨nextFrontier, nextRelated⟩ :=
        environment_frontier_exists runtime leaks ordered profile
        inputs horizon scheduler ⟨remaining + 1, none, execution⟩ trace memories frontier related
          consistent supported (expiry memories frontier supported related) command chosen next
            reached
      have recallEq := app.environmentStep_recall execution next command reached
      obtain ⟨nextTrace⟩ := app.raw_trace_environment (inputs.map State.initial) horizon scheduler
        remaining execution next command trace chosen reached
      have stableNext := runtime.entryEventStable_history leaks (inputs.map State.initial) horizon
        scheduler nextTrace
      cases actorEq : command.actor? app with
      | none => rfl
      | some who =>
          obtain ⟨quiet, sent⟩ := runtime.reactiveEmission_history leaks
            (inputs.map State.initial) horizon scheduler ⟨remaining, some who, next⟩
            (by simpa only [actorEq] using nextTrace) who
          simpa only [implementations, prescribedReactiveImplementation, PMF.bind_map,
            Function.comp_def] using
            nextRelated.response_harmonic runtime leaks ordered profile independent next
              stableNext memories
              nextFrontier (by simpa only [recallEq] using consistent)
                (by simpa only [recallEq] using supported) who quiet sent
    _ = (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind
        (fun _ => runtime.reactiveFrontierPotential leaks profile execution memories) := by
      apply bind_congr_on_support
      intro command chosen
      exact environment_potential_harmonic runtime leaks ordered profile independent
        inputs horizon scheduler
        ⟨remaining + 1, none, execution⟩ trace memories frontier related consistent supported
          (expiry memories frontier supported related) command chosen
    _ = _ := PMF.bind_const _ _

theorem runRounds_posterior_potential_of_expiry (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (independent : graph.ReadyIndependent profile)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (safe : (runtime.reactiveApplication leaks).Execution → Prop)
    (invariant : (runtime.reactiveApplication leaks).PolicyInvariant
      (fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)) safe)
    (expiry : ∀ remaining execution,
      Nonempty (((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩)) → safe execution →
      (∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner)) → ∀ memories frontier,
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
      runtime.ReactiveFrontier leaks execution memories frontier → ∀ event,
      .application (.expire event) ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment (runtime.reactiveApplication leaks))).support → ∀ next,
        next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
          (.application (.expire event))).support →
        runtime.ReactiveFrontier leaks next memories frontier)
    (count remaining : Nat) (execution : (runtime.reactiveApplication leaks).Execution)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some ⟨remaining + count, none, execution⟩))
    (valid : safe execution)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (frontiers : ∀ memories : Player → List (Option graph.Completion),
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
        ∃ frontier, runtime.ReactiveFrontier leaks execution memories frontier) :
    (((runtime.reactiveApplication leaks).runRounds scheduler
      (fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)) count
        execution).bind (fun next => (independentProduct (fun owner =>
          (runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
            (next.recall owner))).bind
              (runtime.reactiveFrontierPotential leaks profile next)) =
      (independentProduct (fun owner =>
        (runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner))).bind
            (runtime.reactiveFrontierPotential leaks profile execution)) ∧
      ∀ next ∈ ((runtime.reactiveApplication leaks).runRounds scheduler
          (fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)) count
            execution).support,
        ∀ memories : Player → List (Option graph.Completion),
          (∀ owner, memories owner ∈
            ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
              (next.recall owner)).support) →
          ∃ frontier, runtime.ReactiveFrontier leaks next memories frontier := by
  let app := runtime.reactiveApplication leaks
  let players := fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)
  induction count generalizing execution with
  | zero =>
      refine ⟨by simp only [ReactiveApplication.runRounds, PMF.pure_bind], ?_⟩
      intro next reached memories supported
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact frontiers memories supported
  | succ count ih =>
      have traceBefore : (app.protocol (inputs.map State.initial) horizon scheduler).Trace
          (some ⟨remaining + count + 1, none, execution⟩) := by
        simpa only [Nat.add_assoc] using trace
      have oneSupported {next : app.Execution}
          (reached : next ∈ (app.round scheduler players execution).support) :
          next ∈ (app.runRounds scheduler players 1 execution).support := by
        simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using reached
      have after {next : app.Execution}
          (reached : next ∈ (app.round scheduler players execution).support) :
          Nonempty ((app.protocol (inputs.map State.initial) horizon scheduler).Trace
            (some ⟨remaining + count, none, next⟩)) ∧ safe next ∧
          (∀ owner, (players owner).Consistent (next.recall owner)) ∧
          (∀ memories : Player → List (Option graph.Completion),
            (∀ owner, memories owner ∈
              ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
                (next.recall owner)).support) →
              ∃ frontier, runtime.ReactiveFrontier leaks next memories frontier) := by
        refine ⟨app.raw_trace_round (inputs.map State.initial) horizon scheduler players
          (remaining + count) execution next traceBefore reached,
          invariant.runRounds scheduler 1 execution next valid (oneSupported reached),
          (ReactiveApplication.consistentRecall_policyInvariant players).runRounds scheduler 1
            execution next consistent (oneSupported reached), ?_⟩
        intro memories supported
        exact round_posterior_frontier_exists_of_expiry runtime leaks ordered profile inputs
          horizon scheduler (remaining + count) execution traceBefore consistent frontiers
            (expiry (remaining + count) execution ⟨traceBefore⟩ valid consistent)
              next reached memories supported
      constructor
      · rw [ReactiveApplication.runRounds, PMF.bind_bind]
        calc
          _ = (app.round scheduler players execution).bind
              (fun next => (independentProduct (fun owner =>
                (runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
                  (next.recall owner))).bind
                    (runtime.reactiveFrontierPotential leaks profile next)) := by
            apply bind_congr_on_support
            intro next reached
            obtain ⟨⟨nextTrace⟩, nextSafe, nextConsistent, nextFrontiers⟩ := after reached
            exact (ih next nextTrace nextSafe nextConsistent nextFrontiers).1
          _ = _ := round_posterior_potential_of_expiry runtime leaks ordered profile independent
            inputs horizon
            scheduler (remaining + count) execution traceBefore consistent frontiers
              (expiry (remaining + count) execution ⟨traceBefore⟩ valid consistent)
      · intro next reached memories supported
        rw [ReactiveApplication.runRounds, PMF.support_bind] at reached
        obtain ⟨middle, first, later⟩ := Set.mem_iUnion₂.mp reached
        obtain ⟨⟨middleTrace⟩, middleSafe, middleConsistent, middleFrontiers⟩ := after first
        exact (ih middle middleTrace middleSafe middleConsistent middleFrontiers).2
          next later memories supported

theorem runRounds_terminal_store_of_expiry (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (independent : graph.ReadyIndependent profile)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (safe : (runtime.reactiveApplication leaks).Execution → Prop)
    (invariant : (runtime.reactiveApplication leaks).PolicyInvariant
      (fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)) safe)
    (expiry : ∀ remaining execution,
      Nonempty (((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩)) → safe execution →
      (∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner)) → ∀ memories frontier,
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
      runtime.ReactiveFrontier leaks execution memories frontier → ∀ event,
      .application (.expire event) ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment (runtime.reactiveApplication leaks))).support → ∀ next,
        next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
          (.application (.expire event))).support →
        runtime.ReactiveFrontier leaks next memories frontier)
    (completes : ∀ control,
      ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
        horizon scheduler).Trace (some control) →
      (∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (control.execution.recall owner)) →
      (runtime.reactiveApplication leaks).terminal (some control) →
        control.execution.application.config.cut.Terminal)
    (count : Nat) (execution : (runtime.reactiveApplication leaks).Execution)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some ⟨count, none, execution⟩))
    (valid : safe execution)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (frontiers : ∀ memories : Player → List (Option graph.Completion),
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
        ∃ frontier, runtime.ReactiveFrontier leaks execution memories frontier) :
    ((runtime.reactiveApplication leaks).runRounds scheduler
      (fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner))
        count execution).map
        (fun next => next.application.config.store) =
      ((independentProduct (fun owner =>
        (runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner))).bind
            (runtime.reactiveFrontierPotential leaks profile execution)).map
              (fun key => key.2.1) := by
  let app := runtime.reactiveApplication leaks
  let players := fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)
  have initializedTrace : (app.protocol (inputs.map State.initial) horizon scheduler).Trace
      (some ⟨0 + count, none, execution⟩) := by simpa only [Nat.zero_add] using trace
  obtain ⟨conserved, retained⟩ := runRounds_posterior_potential_of_expiry runtime leaks ordered
    profile independent
        inputs horizon scheduler safe invariant expiry count 0 execution initializedTrace
      valid consistent frontiers
  rw [← conserved, PMF.map_bind]
  change (app.runRounds scheduler players count execution).map
    (fun next => next.application.config.store) = _
  rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support
  intro next reached
  obtain ⟨nextTrace⟩ := app.raw_trace_runRounds (inputs.map State.initial) horizon scheduler players
    0 count execution next initializedTrace reached
  have stable := runtime.entryEventStable_history leaks (inputs.map State.initial) horizon
    scheduler nextTrace
  have nextConsistent := (ReactiveApplication.consistentRecall_policyInvariant players).runRounds
    scheduler count execution next consistent reached
  have terminal := completes ⟨0, none, next⟩ nextTrace nextConsistent ⟨rfl, rfl⟩
  symm
  rw [PMF.map_bind]
  calc
    _ = (independentProduct (fun owner =>
        (runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (next.recall owner))).bind (fun _ => PMF.pure next.application.config.store) := by
      apply bind_congr_on_support
      intro memories supported
      have coordinates := (independentProduct_support_iff _ memories).mp supported
      obtain ⟨frontier, related⟩ := retained next reached memories coordinates
      exact related.terminal_potential runtime leaks profile next stable memories frontier
        nextConsistent coordinates terminal
    _ = _ := PMF.bind_const _ _

theorem initial_posterior_potential (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile) (inputs : graph.Inputs) :
    (independentProduct (fun owner =>
      (runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        ((ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks)
          (State.initial inputs)).recall owner))).bind
            (runtime.reactiveFrontierPotential leaks profile
              (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks)
                (State.initial inputs))) =
      graph.canonicalContinuation profile (Config.initial inputs) := by
  let execution := ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks)
    (State.initial inputs)
  change (independentProduct
    (fun _ : Player => PMF.pure ([] : List (Option graph.Completion)))).bind
    (runtime.reactiveFrontierPotential leaks profile execution) = _
  rw [independentProduct_pure, PMF.pure_bind]
  have related := runtime.reactiveFrontier_initial leaks inputs
  have stable : runtime.EntryEventStable leaks execution := by
    intro owner entry member
    exact (List.not_mem_nil member).elim
  have consistent : ∀ owner,
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner) := fun _ => ReactiveApplication.Policy.Consistent.nil
  have supported : ∀ owner, ([] : List (Option graph.Completion)) ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support := by
    intro owner
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  exact related.potential_eq runtime leaks profile execution stable (fun _ => [])
    (Config.initial inputs) consistent supported

omit [Fintype Player] in
theorem initial_terminal_store_of_expiry [Finite Player] (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (independent : graph.ReadyIndependent profile)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (safe : (runtime.reactiveApplication leaks).Execution → Prop)
    (invariant : (runtime.reactiveApplication leaks).PolicyInvariant
      (fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)) safe)
    (expiry : ∀ remaining execution,
      Nonempty (((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩)) → safe execution →
      (∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner)) → ∀ memories frontier,
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
      runtime.ReactiveFrontier leaks execution memories frontier → ∀ event,
      .application (.expire event) ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment (runtime.reactiveApplication leaks))).support → ∀ next,
        next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
          (.application (.expire event))).support →
        runtime.ReactiveFrontier leaks next memories frontier)
    (completes : ∀ control,
      ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
        horizon scheduler).Trace (some control) →
      (∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (control.execution.recall owner)) →
      (runtime.reactiveApplication leaks).terminal (some control) →
        control.execution.application.config.cut.Terminal)
    (initial : graph.Inputs) (supportedInitial : initial ∈ inputs.support)
    (initialSafe : safe (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks)
      (State.initial initial))) :
    ((runtime.reactiveApplication leaks).runRounds scheduler
      (fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)) horizon
        (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks)
          (State.initial initial))).map (fun next => next.application.config.store) =
      (graph.canonicalContinuation profile (Config.initial initial)).map
        (fun key => key.2.1) := by
  let _ := Fintype.ofFinite Player
  let app := runtime.reactiveApplication leaks
  let players := fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)
  let execution := ReactiveApplication.Execution.initial app (State.initial initial)
  have supportedState : State.initial initial ∈ (inputs.map State.initial).support := by
    rw [PMF.support_map]
    exact ⟨initial, supportedInitial, rfl⟩
  obtain ⟨initialTrace⟩ := app.raw_trace_roundsFrom (inputs.map State.initial) horizon scheduler
    players 0 (Nat.zero_le horizon) execution (by
      rw [ReactiveApplication.roundsFrom, PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨State.initial initial, supportedState, ?_⟩
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have consistent : ∀ owner, (players owner).Consistent (execution.recall owner) :=
    fun _ => ReactiveApplication.Policy.Consistent.nil
  have frontiers : ∀ memories : Player → List (Option graph.Completion),
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
        ∃ frontier, runtime.ReactiveFrontier leaks execution memories frontier := by
    intro memories supported
    have empty : memories = fun _ => [] := by
      funext owner
      exact (PMF.mem_support_pure_iff _ _).mp (supported owner)
    rw [empty]
    exact ⟨Config.initial initial, runtime.reactiveFrontier_initial leaks initial⟩
  rw [runRounds_terminal_store_of_expiry runtime leaks ordered profile independent
        inputs horizon scheduler
    safe invariant expiry completes horizon execution
      (by simpa only [Nat.sub_zero] using initialTrace)
        initialSafe consistent frontiers,
    initial_posterior_potential runtime leaks profile initial]

end Vegas.EventGraphRuntime
