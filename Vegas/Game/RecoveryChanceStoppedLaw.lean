/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySuccessorBoundary
import Interaction.ReactiveResponseStopped
import Interaction.ReactiveLocalContinuation

/-! # Finite stopped chance phases of the recovery comparison model -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem chance_environment_configLaw
    (players : Player → (application setup leaks).Policy)
    (execution : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (actorless : (graph setup).actor? event = none)
    (alone : ∀ cut : (graph setup).order.Cut, ∀ other,
      cut.Ready event → cut.Ready other → other = event)
    (action : (graph setup).Action event) :
    (execution.environmentStep (application setup leaks) command).map
        (fun next => next.application.config) = PMF.pure execution.application.config ∨
      (execution.environmentStep (application setup leaks) command).map
        (fun next => next.application.config) =
          execution.application.config.step event ready action :=
    by
  have resumeConfig : ∀ (actor : Option Player) (middle : (application setup leaks).Execution),
      ((application setup leaks).resume players actor middle).map
        (fun next => next.application.config) = PMF.pure middle.application.config := by
    intro actor middle
    cases actor with
    | none => simp only [ReactiveApplication.resume, PMF.pure_map]
    | some who =>
        unfold ReactiveApplication.resume ReactiveApplication.invoke
        rw [PMF.map_comp]
        simp only [Function.comp_def]
        have unchanged : (fun response =>
            (middle.respond (application setup leaks) who response).application.config) =
            fun _ => middle.application.config := funext fun response =>
          ((runtime setup).reactive_respond_application leaks middle who response).1
        rw [unchanged]
        exact PMF.map_const _ _
  have dispatchConfig : ((application setup leaks).dispatch players command execution).map
      (fun next => next.application.config) =
      (execution.environmentStep (application setup leaks) command).map
        (fun next => next.application.config) := by
    unfold ReactiveApplication.dispatch
    rw [PMF.map_bind]
    calc _ = (execution.environmentStep (application setup leaks) command).bind
          (fun middle => PMF.pure middle.application.config) :=
          bind_congr_on_support _ fun middle _ => resumeConfig _ middle
      _ = _ := PMF.bind_pure_comp _ _
  have law := sample_command_law players execution command event ready actorless alone action
  rwa [dispatchConfig] at law

private theorem chance_control_harmonic [Fintype Player]
    (bounds : MessageBounds (graph setup)) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (players : ∀ who,
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    {control : (application setup leaks).Control} (current : history.state = some control)
    (event : (graph setup).EventId) (ready : control.execution.application.config.cut.Ready event)
    (actorless : (graph setup).actor? event = none)
    (alone : ∀ cut : (graph setup).order.Cut, ∀ other,
      cut.Ready event → cut.Ready other → other = event)
    (action : (graph setup).Action event)
    (continuation : Option (graph setup).Config → PMF (Option (graph setup).Config))
    (unchanged : continuation (some control.execution.application.config) =
      (control.execution.application.config.step event ready action).map some)
    (completed : ∀ next ∈ (control.execution.application.config.step event ready action).support,
      continuation (some next) = PMF.pure (some next)) :
    ((((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).runBehavioralFrom
      players 1 history).map (fun next =>
        next.state.map (fun state => state.execution.application.config))).bind continuation) =
      (control.execution.application.config.step event ready action).map some := by
  classical
  let app := application setup leaks
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let policies := menu.decodeProfile (initialLaw setup) horizon scheduler players
  have environment (command : app.Command) :
      (control.execution.environmentStep app command).bind
        (fun next => continuation (some next.application.config)) =
          (control.execution.application.config.step event ready action).map some := by
    calc _ = ((control.execution.environmentStep app command).map
          (fun next => next.application.config)).bind (fun config => continuation (some config)) :=
          (PMF.bind_map ..).symm
      _ = _ := by
        rcases chance_environment_configLaw policies control.execution command event ready
          actorless alone action with stays | samples
        · rw [stays, PMF.pure_bind, unchanged]
        · rw [samples]
          exact (bind_congr_on_support _ completed).trans (PMF.bind_pure_comp _ _)
  have evaluated := congrArg
    (fun law : PMF app.ProtocolState => (law.map
      (fun state => state.map (fun next => next.execution.application.config))).bind continuation)
    (menu.run_map_controlSteps (initialLaw setup) horizon scheduler players 1 history)
  simp only [PMF.map_comp, Function.comp_def, Function.iterate_one, PMF.pure_bind,
    PMF.bind_map] at evaluated
  simp only [PMF.bind_map, Function.comp_def]
  refine evaluated.trans ?_
  rw [current]
  rcases control with ⟨remaining, actor, execution⟩
  cases actor with
  | none =>
      cases remaining with
      | zero =>
          simpa only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
            ReactiveApplication.transition, PMF.pure_bind, Option.map_some] using unchanged
      | succ remaining =>
          simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
            ReactiveApplication.transition, PMF.bind_bind, PMF.bind_map]
          exact (bind_congr_on_support _ (fun command _ => environment command)).trans
            (PMF.bind_const _ _)
  | some who =>
      simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
        ReactiveApplication.transition, ↓reduceIte, Option.getD_some, PMF.bind_bind,
        PMF.pure_bind, Option.map_some]
      calc _ = (policies who (execution.recall who) (execution.observe app who)).bind
            (fun _ => (execution.application.config.step event ready action).map some) :=
            bind_congr_on_support _ fun response _ => by
              rw [((runtime setup).reactive_respond_application leaks execution who response).1]
              exact unchanged
        _ = _ := PMF.bind_const _ _

section FiniteChance

variable [Fintype Player] {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)

local notation "scheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))

include initialized nativeLaw completes in
/-- The finite one-packet stopped chance phase has the graph sampling law on
configurations, including the actual first public-exclusion stopping rule. -/
theorem recovery_chance_stopped_configLaw
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (actorless : (graph setup).actor? event = none)
    (action : (graph setup).Action event)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank control.execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    ((N).runBehavioralUntil certificate players
      (fun stop => LateStopped setup leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) start).map
        (fun final => final.state.map (fun next => next.execution.application.config)) =
      (control.execution.application.config.step event ready action).map some := by
  classical
  let base := control.execution.application.config
  let law := base.step event ready action
  let project : (application setup leaks).ProtocolState → Option (graph setup).Config :=
    fun state => state.map (fun next => next.execution.application.config)
  let potential : Option (graph setup).Config → PMF (Option (graph setup).Config) :=
    fun config => if config = some base then law.map some else PMF.pure config
  let stopped : (E).History → Prop := fun stop =>
    LateStopped setup leaks bounds horizon scheduler rank stop ∨ ¬ Clear stop.state
  let reach : (E).History → Prop := fun history =>
    ∃ next : (application setup leaks).Control, history.state = some next ∧
      (next.execution.application.config = base ∨ next.execution.application.config ∈ law.support)
  have law_completed : ∀ config ∈ law.support, event ∈ config.cut.completed := by
    intro config supported
    rw [base.step_cut event ready action config supported, EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  have law_changed : ∀ config ∈ law.support, config ≠ base := by
    intro config supported equal
    have member := law_completed config supported
    rw [equal] at member
    exact ready.1 member
  have law_potential : ∀ config ∈ law.support,
      potential (some config) = PMF.pure (some config) := by
    intro config supported
    exact ite_eq_right (fun equal => law_changed config supported (Option.some.inj equal))
  have initialDecoded : decodedPoint setup base = some point :=
    (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have no_pending_halt : ∀ (history : (E).History) (next : (application setup leaks).Control),
      history.state = some next → next.execution.application.config = base →
      stopped history ∨ (E).terminal history.state → False := by
    intro history next state equal halted
    have nextTrace := (menu).toRawTrace (initialLaw setup) horizon scheduler
      (state ▸ history.trace)
    have nextDecoded : decodedPoint setup next.execution.application.config = some point := by
      rw [equal]
      exact initialDecoded
    have clear := publicExclusionRecord_of_decodedIntended nextTrace nextDecoded intended
    rcases halted with (prefixed | failure) | ended
    · obtain ⟨other, otherState, nextPrefix⟩ := prefixed
      rw [state, Option.some.injEq] at otherState
      subst otherState
      rw [equal] at nextPrefix
      have := isPrefix_unique ordered nextPrefix
      omega
    · exact failure (by simpa only [state, ReactiveApplication.stateInvariant] using clear)
    · rw [state] at ended
      rw [← nativeLaw] at nextTrace
      have terminal := Recovery.CompletesPlay.clear_native (runtime setup) leaks initialized
        completes next nextTrace clear ended
      have member : event ∈ next.execution.application.config.cut.completed := by
        rw [terminal]
        exact Finset.mem_univ _
      rw [equal] at member
      exact ready.1 member
  have rows : ∀ (history : (E).History) (next : (application setup leaks).Control),
      history.state = some next → next.execution.application.config = base →
      (((N).runBehavioralFrom players 1 history).map (fun later => project later.state)).bind
        potential = law.map some := by
    intro history next state equal
    have nextReady : next.execution.application.config.cut.Ready event := by
      rw [equal]
      exact ready
    have alone : ∀ cut : (graph setup).order.Cut, ∀ other,
        cut.Ready event → cut.Ready other → other = event :=
      fun cut other first second => setup.eventGraph.sequentialize_ready_unique cut second first
    have stepEq : next.execution.application.config.step event nextReady action = law := by
      simp only [equal]
      rfl
    have row := chance_control_harmonic bounds horizon scheduler players history state event
      nextReady actorless alone action potential
      (by rw [stepEq, equal]; exact ite_eq_left rfl)
      (by rw [stepEq]; exact law_potential)
    exact row.trans (congrArg (PMF.map some) stepEq)
  have result : ∀ history : (E).History, reach history →
      ((N).runBehavioralUntil certificate players stopped history).map
        (fun final => project final.state) = potential (project history.state) := by
    intro history
    induction history using certificate.induction with
    | _ history ih =>
      rintro ⟨next, state, reachable⟩
      by_cases halt : stopped history
      · rw [(N).runBehavioralUntil_of_stopped certificate players halt, PMF.pure_map]
        have changed : project history.state ≠ some base := by
          rw [state]
          intro same
          exact no_pending_halt history next state (Option.some.inj same) (Or.inl halt)
        exact (ite_eq_right changed).symm
      by_cases ended : (E).terminal history.state
      · rw [(N).runBehavioralUntil_of_terminal certificate players ended, PMF.pure_map]
        have changed : project history.state ≠ some base := by
          rw [state]
          intro same
          exact no_pending_halt history next state (Option.some.inj same) (Or.inr ended)
        exact (ite_eq_right changed).symm
      have equal : next.execution.application.config = base := by
        rcases reachable with equal | sampled
        · exact equal
        · exact (halt (Or.inl ⟨next, state,
            isPrefix_succ_of_mem_step ordered ready sampled⟩)).elim
      have row := rows history next state equal
      have preserved : ∀ later ∈ ((N).runBehavioralFrom players 1 history).support,
          reach later := by
        intro later member
        obtain ⟨found, foundOrdered, seen⟩ := pendingAt_history
          ((menu).toRawTrace (initialLaw setup) horizon scheduler (state ▸ history.trace))
        have currentOrdered : next.execution.application.config.cut.IsPrefix rank := by
          rw [equal]
          exact ordered
        have sameRank := isPrefix_unique foundOrdered currentOrdered
        subst sameRank
        obtain ⟨joint, realized⟩ := onePacket_step_transition bounds players ended member
        rw [state] at realized
        rcases next with ⟨remaining, actor, execution⟩
        obtain ⟨after, afterState, _⟩ := pendingTransition ⟨currentOrdered, seen⟩ joint realized
        refine ⟨after, afterState, ?_⟩
        by_cases equalAfter : after.execution.application.config = base
        · exact Or.inl equalAfter
        · right
          have mapped : project later.state ∈
              (((N).runBehavioralFrom players 1 history).map
                (fun later => project later.state)).support :=
            (PMF.mem_support_map_iff ..).mpr ⟨later, member, rfl⟩
          have included : project later.state ∈
              ((((N).runBehavioralFrom players 1 history).map
                (fun later => project later.state)).bind potential).support := by
            apply (PMF.mem_support_bind_iff ..).mpr
            refine ⟨project later.state, mapped, ?_⟩
            rw [show potential (project later.state) = PMF.pure (project later.state) from
              ite_eq_right (by simpa only [project, afterState, Option.map_some, Option.some.injEq]
                using equalAfter)]
            exact (PMF.mem_support_pure_iff ..).mpr rfl
          rw [row, PMF.mem_support_map_iff] at included
          obtain ⟨config, supported, configEq⟩ := included
          have same : config = after.execution.application.config := by
            simpa only [project, afterState, Option.map_some, Option.some.injEq] using configEq
          exact same ▸ supported
      rw [(N).runBehavioralUntil_of_running certificate players halt ended, PMF.map_bind]
      calc _ = ((N).runBehavioralFrom players 1 history).bind
            (fun later => potential (project later.state)) :=
            bind_congr_on_support _ fun later member => ih later
              ((N).mem_support_runBehavioralFrom_one players ended member).1
              (preserved later member)
        _ = law.map some := by
            simpa only [PMF.bind_map, Function.comp_def] using row
        _ = potential (project history.state) := by
            rw [state]
            exact (ite_eq_left (by
              simpa only [project, Option.map_some] using congrArg some equal)).symm
  have initial := result start ⟨control, current, Or.inl rfl⟩
  simpa only [project, current, Option.map_some, potential, base, law, ite_eq_left rfl]
    using initial

include initialized nativeLaw completes in
/-- The finite chance phase preserves the exact source continuation law. Its
policies and scheduler are the actual comparison policies and recovery scheduler. -/
theorem recovery_chance_stopped_sourceContinuation
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (event : (graph setup).EventId)
    (actorless : (graph setup).actor? event = none)
    (profile : BehavioralProfile setup.program)
    (residual : SourceResidual setup profile rank control.execution.application.config)
    (atRank : event.val = rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank control.execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    ((N).runBehavioralUntil certificate players
      (fun stop => LateStopped setup leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) start).bind
        (fun final => (setup.continuationLaw profile
          (nativeDecodedState setup leaks final.state)).map some) =
      sourceContinuation setup profile rank control.execution.application.config := by
  classical
  let config := control.execution.application.config
  let ready := (ready_iff_rank setup config rank residual.checkpoint.ordered event).mpr atRank
  let action := ((graph setup).nodes event).actionOfActorNone actorless
  let phase := (N).runBehavioralUntil certificate players
    (fun stop => LateStopped setup leaks bounds horizon scheduler rank stop ∨ ¬ Clear stop.state)
    start
  let continuation : Option (graph setup).Config →
      PMF (Option (State L setup.program.terminalCtx)) := fun next =>
    match next with
    | none => (setup.continuationLaw profile none).map some
    | some next => sourceContinuation setup profile (rank + 1) next
  have configLaw := recovery_chance_stopped_configLaw initialized nativeLaw completes certificate
    players start current residual.checkpoint.ordered event ready actorless action decoded intended
  have factored : phase.bind (fun final => (setup.continuationLaw profile
        (nativeDecodedState setup leaks final.state)).map some) =
      (config.step event ready action).bind (sourceContinuation setup profile (rank + 1)) := by
    calc _ = (phase.map (fun final => final.state.map
          (fun next => next.execution.application.config))).bind continuation := by
          rw [PMF.bind_map]
          apply bind_congr_on_support _
          intro final member
          have mapped : final.state.map (fun next => next.execution.application.config) ∈
              (phase.map (fun final => final.state.map
                (fun next => next.execution.application.config))).support :=
            (PMF.mem_support_map_iff ..).mpr ⟨final, member, rfl⟩
          rw [configLaw, PMF.mem_support_map_iff] at mapped
          obtain ⟨next, sampled, same⟩ := mapped
          cases state : final.state with
          | none => simp only [state, Option.map_none] at same; cases same
          | some ending =>
              have nextEq : next = ending.execution.application.config := by
                simpa only [state, Option.map_some, Option.some.injEq] using same
              have nextPrefix := isPrefix_succ_of_mem_step residual.checkpoint.ordered ready
                (nextEq ▸ sampled)
              simp only [Function.comp_def, state, Option.map_some, continuation,
                nativeDecodedState]
              change (setup.continuationLaw profile
                  (decodedPoint setup ending.execution.application.config)).map some =
                sourceContinuation setup profile (rank + 1) ending.execution.application.config
              rw [decodedPoint_eq_of_isPrefix nextPrefix]
              rfl
      _ = _ := by rw [configLaw, PMF.bind_map]; rfl
  obtain ⟨law, sourceLaw, _policy, _effective, _disclosing⟩ :=
    SourceResidual.head_law leaks residual event atRank ready
  have fixed : law.bind (fun choice =>
      (config.step event ready choice).bind (sourceContinuation setup profile (rank + 1))) =
      (config.step event ready action).bind (sourceContinuation setup profile (rank + 1)) := by
    have same : (fun choice => (config.step event ready choice).bind
        (sourceContinuation setup profile (rank + 1))) =
        (fun _ => (config.step event ready action).bind
          (sourceContinuation setup profile (rank + 1))) := by
      funext choice
      rw [((graph setup).nodes event).action_eq_of_actor_none actorless choice action]
    rw [same, PMF.bind_const]
  exact factored.trans (sourceLaw.trans fixed).symm

end FiniteChance

end Vegas
