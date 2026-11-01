/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSuccessorBoundary
import Vegas.Pending.EventCommandFrame
import Vegas.Pending.ReactiveGraphSteps

/-! # Finite stopped chance phases of the native counted model -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem prefix_after_completion {before after : (graph setup).Config} {rank : Nat}
    (ordered : before.cut.IsPrefix rank) {event : (graph setup).EventId}
    (ready : before.cut.Ready event) {action : (graph setup).Action event}
    (stepped : after ∈ (before.step event ready action).support) :
    after.cut.IsPrefix (rank + 1) := by
  have actual : before.cut.IsPrefix event.val :=
    ⟨event.isLt.le, fun query =>
      setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready _ ready⟩
  rw [before.step_cut event ready action after stepped]
  exact ordered.complete_at event ready (actual.unique ordered)

private theorem chance_environment_configLaw
    (execution : (application setup runtime leaks).Execution)
    (command : (application setup runtime leaks).Command)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (actorless : (graph setup).actor? event = none)
    (action : (graph setup).Action event)
    (clear : execution.application.config.defaulted = ∅) :
    (execution.environmentStep (application setup runtime leaks) command).map
        (fun next => next.application.config) = PMF.pure execution.application.config ∨
      (execution.environmentStep (application setup runtime leaks) command).map
        (fun next => next.application.config) =
          execution.application.config.step event ready action := by
  let app := application setup runtime leaks
  have sole (other : (graph setup).EventId)
      (otherReady : execution.application.config.cut.Ready other) : other = event :=
    setup.eventGraph.sequentialize_ready_unique _ otherReady ready
  have stays : (∀ next ∈ (execution.environmentStep app command).support,
      next.application.config = execution.application.config) →
      (execution.environmentStep app command).map (fun next => next.application.config) =
        PMF.pure execution.application.config := by
    intro all
    rw [map_congr_on_support _ (g := fun _ => execution.application.config) all]
    exact PMF.map_const _ _
  cases command with
  | activate who =>
      left
      apply stays
      intro next member
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ member
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | wait =>
      left
      apply stays
      intro next member
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at member
      subst next
      rfl
  | «include» id =>
      left
      apply stays
      intro next member
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at member
      subst next
      cases found : execution.network.lookup id with
      | none =>
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found]
      | some message =>
          have rejected : app.handle execution.application message = none := by
            apply reactiveHandle_none
            cases handled : handle runtime execution.application ⟨message.id, message.payload.call⟩
              with
            | none => rfl
            | some next =>
                obtain ⟨query, named, queryReady, _, _⟩ :=
                  handle_config_mem_step runtime execution.application next _ handled
                have equal := sole query queryReady
                subst query
                have sender := handle_sender_actor runtime execution.application next _ handled
                  event named
                rw [actorless] at sender
                cases sender
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found, rejected, Option.getD_none]
  | application operation =>
      have nativeLaw : (environmentStep runtime execution.application operation).map
          EventGraphRuntime.State.config = PMF.pure execution.application.config ∨
        (environmentStep runtime execution.application operation).map
          EventGraphRuntime.State.config =
            execution.application.config.step event ready action := by
        cases node : nodeView (graph setup) event with
        | bind owner payload outputEq codeEq =>
            have actor := nodeView_bind_actor outputEq codeEq
            rw [actorless] at actor
            cases actor
        | resolve owner payload binding checks outputEq codeEq =>
            have actor := nodeView_resolve_actor outputEq codeEq
            rw [actorless] at actor
            cases actor
        | sample payload law outputEq codeEq =>
            cases operation with
            | advanceClock => exact Or.inl (by simp only [environmentStep, PMF.pure_map])
            | executeSample other =>
                by_cases otherReady : execution.application.config.cut.Ready other
                · have equal := sole other otherReady
                  subst other
                  right
                  rw [environmentStep_executeSample_eq runtime execution.application event ready
                    payload law outputEq codeEq node, PMF.map_comp]
                  change (execution.application.config.step event ready _).map id = _
                  rw [PMF.map_id, ((graph setup).nodes event).action_eq_of_actor_none actorless
                    (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) action]
                · left
                  rw [environmentStep_executeSample_of_not_ready runtime execution.application
                    other otherReady, PMF.pure_map]
            | expire other =>
                left
                have pure : environmentStep runtime execution.application (.expire other) =
                    PMF.pure execution.application := by
                  by_cases otherReady : execution.application.config.cut.Ready other
                  · have equal := sole other otherReady
                    subst other
                    cases activated : execution.application.activatedAt event with
                    | none =>
                        exact environmentStep_expire_of_not_activated runtime
                          execution.application event ready activated
                    | some entered =>
                        by_cases due : runtime.deadline event ≤
                            execution.application.clock - entered
                        · exact environmentStep_expire_sample_eq runtime execution.application
                            event ready entered activated due payload law outputEq codeEq node
                        · exact environmentStep_expire_of_not_due runtime execution.application
                            event ready entered activated due
                  · exact environmentStep_expire_of_not_ready runtime execution.application other
                      otherReady
                rw [pure, PMF.pure_map]
      have drains (native : EventGraphRuntime.State (graph setup))
          (member : native ∈ (environmentStep runtime execution.application operation).support) :
          native.drain.config = native.config := by
        have mapped : native.config ∈ ((environmentStep runtime execution.application
            operation).map EventGraphRuntime.State.config).support :=
          (PMF.mem_support_map_iff _ _ _).mpr ⟨native, member, rfl⟩
        have empty : native.config.defaulted = ∅ := by
          rcases nativeLaw with stayed | sampled
          · rw [stayed, PMF.mem_support_pure_iff] at mapped
            rw [mapped]
            exact clear
          · rw [sampled] at mapped
            exact (execution.application.config.step_defaulted_of_actor_none native.config event
              ready action mapped actorless).trans clear
        exact congrArg EventGraphRuntime.State.config (native.drain_eq_of_empty empty)
      have equal : (execution.environmentStep app (.application operation)).map
          (fun next => next.application.config) =
          (environmentStep runtime execution.application operation).map
            EventGraphRuntime.State.config := by
        unfold ReactiveApplication.Execution.environmentStep
        rw [PMF.map_comp, PMF.map_comp]
        change ((environmentStep runtime execution.application operation).map
          EventGraphRuntime.State.drain).map EventGraphRuntime.State.config = _
        rw [PMF.map_comp]
        exact map_congr_on_support _ drains
      rw [equal]
      exact nativeLaw

private theorem chance_control_harmonic [Fintype Player]
    (bounds : MessageBounds (graph setup)) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    (players : ∀ who,
      (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
        scheduler).BehavioralPolicy who)
    (history : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    {control : (application setup runtime leaks).Control} (current : history.state = some control)
    (event : (graph setup).EventId) (ready : control.execution.application.config.cut.Ready event)
    (actorless : (graph setup).actor? event = none)
    (clear : control.execution.application.config.defaulted = ∅)
    (action : (graph setup).Action event)
    (continuation : Option (graph setup).Config → PMF (Option (graph setup).Config))
    (unchanged : continuation (some control.execution.application.config) =
      (control.execution.application.config.step event ready action).map some)
    (completed : ∀ next ∈ (control.execution.application.config.step event ready action).support,
      continuation (some next) = PMF.pure (some next)) :
    ((((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).runBehavioralFrom
      players 1 history).map (fun next =>
        next.state.map (fun state => state.execution.application.config))).bind continuation) =
      (control.execution.application.config.step event ready action).map some := by
  classical
  let app := application setup runtime leaks
  let menu := bounds.onePacketMenu runtime leaks
  let policies := menu.decodeProfile (initialLaw setup) horizon scheduler players
  have environment (command : app.Command) :
      (control.execution.environmentStep app command).bind
        (fun next => continuation (some next.application.config)) =
          (control.execution.application.config.step event ready action).map some := by
    calc _ = ((control.execution.environmentStep app command).map
          (fun next => next.application.config)).bind (fun config => continuation (some config)) :=
          (PMF.bind_map ..).symm
      _ = _ := by
        rcases chance_environment_configLaw (runtime := runtime) control.execution
          command event ready actorless action clear with stays | samples
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
              rw [(runtime.reactive_respond_application leaks execution who response).1]
              exact unchanged
        _ = _ := PMF.bind_const _ _

section FiniteChance

variable [Fintype Player] {bounds : MessageBounds (graph setup)}
  {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  (completes : ∀ control : (application setup runtime leaks).Control,
    ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control) →
    control.execution.application.config.defaulted = ∅ →
    (application setup runtime leaks).terminal (some control) →
    control.execution.application.config.cut.Terminal)

local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

include completes in
/-- The finite one-packet stopped chance phase has the graph sampling law on
configurations, including the actual first public-exclusion stopping rule. -/
theorem counted_chance_stopped_configLaw
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup runtime leaks).Control}
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
      (fun stop => LateStopped setup runtime leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) start).map
        (fun final => final.state.map (fun next => next.execution.application.config)) =
      (control.execution.application.config.step event ready action).map some := by
  classical
  have atRank := (ready_iff_rank setup _ rank ordered event).mp ready
  let base := control.execution.application.config
  let law := base.step event ready action
  let project : (application setup runtime leaks).ProtocolState → Option (graph setup).Config :=
    fun state => state.map (fun next => next.execution.application.config)
  let potential : Option (graph setup).Config → PMF (Option (graph setup).Config) :=
    fun config => if config = some base then law.map some else PMF.pure config
  let stopped : (E).History → Prop := fun stop =>
    LateStopped setup runtime leaks bounds horizon scheduler rank stop ∨ ¬ Clear stop.state
  let reach : (E).History → Prop := fun history =>
    ∃ next : (application setup runtime leaks).Control, history.state = some next ∧
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
  have no_pending_halt : ∀ (history : (E).History) (next : (application setup runtime
    leaks).Control),
      history.state = some next → next.execution.application.config = base →
      stopped history ∨ (E).terminal history.state → False := by
    intro history next state equal halted
    have nextTrace := (menu).toRawTrace (initialLaw setup) horizon scheduler
      (state ▸ history.trace)
    have nextDecoded : decodedPoint setup next.execution.application.config = some point := by
      rw [equal]
      exact initialDecoded
    have clear := defaulted_eq_empty_of_decodedIntended nextDecoded
      intended
    rcases halted with (prefixed | failure) | ended
    · obtain ⟨other, otherState, query, completed, queryRank⟩ := prefixed
      rw [state, Option.some.injEq] at otherState
      subst otherState
      rw [equal] at completed
      have := (ordered.2 query).mp completed
      omega
    · exact failure (by simpa only [state, ReactiveApplication.stateInvariant] using clear)
    · rw [state] at ended
      have terminal := completes next (state ▸ history.trace) clear ended
      have member : event ∈ next.execution.application.config.cut.completed := by
        rw [terminal]
        exact Finset.mem_univ _
      rw [equal] at member
      exact ready.1 member
  have rows : ∀ (history : (E).History) (next : (application setup runtime leaks).Control),
      history.state = some next → next.execution.application.config = base →
      (((N).runBehavioralFrom players 1 history).map (fun later => project later.state)).bind
        potential = law.map some := by
    intro history next state equal
    have nextReady : next.execution.application.config.cut.Ready event := by
      rw [equal]
      exact ready
    have stepEq : next.execution.application.config.step event nextReady action = law := by
      simp only [equal]
      rfl
    have row := chance_control_harmonic (runtime := runtime) bounds horizon scheduler players
      history state event
      nextReady actorless (by
        rw [equal]
        exact defaulted_eq_empty_of_decodedIntended initialDecoded intended) action potential
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
        · exact (halt (Or.inl ⟨next, state, event,
            law_completed _ sampled, atRank⟩)).elim
      have row := rows history next state equal
      have preserved : ∀ later ∈ ((N).runBehavioralFrom players 1 history).support,
          reach later := by
        intro later member
        obtain ⟨⟨joint, _legal, realized⟩, _⟩ :=
          (N).mem_support_runBehavioralFrom_one players ended member
        change later.state ∈ ((application setup runtime leaks).transition (initialLaw setup)
          horizon scheduler history.state joint).support at realized
        rw [state] at realized
        obtain ⟨after, afterState, _recallPrefix⟩ :=
          (application setup runtime leaks).transition_recall_prefix (initialLaw setup) horizon
            scheduler next later.state joint realized
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

include completes in
/-- The finite chance phase preserves the exact source continuation law. Its
policies and scheduler are the actual comparison policies and native scheduler. -/
theorem counted_chance_stopped_sourceContinuation
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup runtime leaks).Control}
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
      (fun stop => LateStopped setup runtime leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) start).bind
        (fun final => (setup.continuationLaw profile
          (nativeDecodedState setup runtime leaks final.state)).map some) =
      sourceContinuation setup profile rank control.execution.application.config := by
  classical
  let config := control.execution.application.config
  let ready := (ready_iff_rank setup config rank residual.checkpoint.ordered event).mpr atRank
  let action := ((graph setup).nodes event).actionOfActorNone actorless
  let phase := (N).runBehavioralUntil certificate players
    (fun stop => LateStopped setup runtime leaks bounds horizon scheduler rank stop ∨ ¬ Clear
      stop.state)
    start
  let continuation : Option (graph setup).Config →
      PMF (Option (Config Player L setup.program.terminalCtx)) := fun next =>
    match next with
    | none => (setup.continuationLaw profile none).map some
    | some next => sourceContinuation setup profile (rank + 1) next
  have configLaw := counted_chance_stopped_configLaw (runtime := runtime) completes certificate
    players start current residual.checkpoint.ordered event ready actorless action decoded intended
  have factored : phase.bind (fun final => (setup.continuationLaw profile
        (nativeDecodedState setup runtime leaks final.state)).map some) =
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
              have nextPrefix := prefix_after_completion residual.checkpoint.ordered ready
                (nextEq ▸ sampled)
              simp only [Function.comp_def, state, Option.map_some, continuation,
                nativeDecodedState ]
              change (setup.continuationLaw profile
                  (decodedPoint setup ending.execution.application.config)).map some =
                sourceContinuation setup profile (rank + 1) ending.execution.application.config
              rw [decodedPoint_eq_of_isPrefix nextPrefix]
              rfl
      _ = _ := by rw [configLaw, PMF.bind_map]; rfl
  obtain ⟨law, sourceLaw, _policy, _effective⟩ :=
    SourceResidual.head_law runtime leaks residual event atRank ready
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
