module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveOwnerWindow
public import Vegas.Pending.ReactiveSampleLikelihood
public import Vegas.Pending.ReactiveGraphSteps
public import Vegas.Pending.ReactiveOpeningLikelihood
public import Vegas.Pending.ActivationRecall
public import Vegas.Pending.TurnClient
public import Interaction.ReactiveMixtureRounds

@[expose] public section

/-! # One deviating player's traffic, round by round, in every dependency choice

One player follows an arbitrary native policy while the scheduler satisfies the
asynchronous contract. This module collects the facts that read the deviator's
traffic round by round, for every dependency choice and deadline:

* equal deviator traffic gives equal deviator and scheduler observations, and
  is kept by recording the same command, by a packet the handler treats alike
  for the deviator, and by every application command
  (`Vegas.application_environmentStep_traffic_congr`): clocks and expiry read
  the public view, and public chance reads public data;
* while every ready event belongs to the deviator or to chance, a packet of any
  other player is rejected (`Vegas.handle_foreign_sender_none`);
* in the phase of an event ready alone that belongs to the deviator or to
  chance, the deviator's traffic at the end of the phase has a law that
  depends on the execution only through its traffic at the start
  (`Vegas.focalPhase_traffic_congr`).
-/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

section Steps

omit [DecidableEq Player] in
/-- Equal public views have equal completed cuts. -/
theorem cut_eq_of_publicView_eq {left right : EventGraphRuntime.State graph}
    (same : left.publicView = right.publicView) : left.config.cut = right.config.cut := by
  apply EventGraph.cut_eq_of_completionOrder_eq
  exact congrArg
      (fun view : PublicView graph => view.observation.completionOrder) same

end Steps

section Focal

variable (timeouts leaks)

/-- The players of a phase whose ready event belongs to `who` or to chance:
`who` follows `deviation` and every other player is silent. -/
abbrev focalPlayers (who : Player)
    (deviation : ((reactiveApplication timeouts) leaks).Policy) : Player →
    ((reactiveApplication timeouts) leaks).Policy := Function.update
    (fun _ => ((reactiveApplication timeouts) leaks).silentPolicy) who deviation

variable {timeouts leaks}

/-- Equal deviator traffic gives equal deviator observations. -/
theorem observe_eq_of_bindingTraffic (who : Player)
    {left right : ((reactiveApplication timeouts) leaks).Execution}
    (same : (bindingTraffic timeouts) leaks who left =
      (bindingTraffic timeouts) leaks who right) :
    left.observe ((reactiveApplication timeouts) leaks) who = right.observe
        ((reactiveApplication timeouts) leaks) who := by
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) same
  change ReactiveApplication.PlayerView.mk _ _ _ = _
  rw [networks]
  exact congrArg₂ (fun view evidence =>
    (⟨right.network.observe who, view, evidence⟩ :
        ((reactiveApplication timeouts) leaks).PlayerView))
    views receipts

/-- Equal deviator traffic gives equal scheduler observations. -/
theorem observeEnvironment_eq_of_bindingTraffic (who : Player)
    {left right : ((reactiveApplication timeouts) leaks).Execution}
    (same : (bindingTraffic timeouts) leaks who left =
      (bindingTraffic timeouts) leaks who right) :
    left.observeEnvironment ((reactiveApplication timeouts) leaks) =
      right.observeEnvironment ((reactiveApplication timeouts) leaks) := by
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) same
  change ReactiveApplication.EnvironmentView.mk left.network.publicView
    left.application.publicView left.receipts = _
  rw [networks, publics, receipts]
  rfl

/-- Replacing the environment recall by the same list keeps equal deviator
traffic. -/
theorem bindingTraffic_with_environmentRecall (who : Player)
    {left right : ((reactiveApplication timeouts) leaks).Execution}
    (same : (bindingTraffic timeouts) leaks who left =
      (bindingTraffic timeouts) leaks who right)
    (entries : List ((reactiveApplication timeouts) leaks).EnvironmentEntry) :
    (bindingTraffic timeouts) leaks who
    { left with environmentRecall := entries } =
      (bindingTraffic timeouts) leaks who
      { right with environmentRecall := entries } := by
  dsimp only [EventGraphRuntime.bindingTraffic] at same ⊢
  exact congrArg (fun read => (read.1, read.2.1, entries, read.2.2.2)) same

/-- Recording the same command keeps equal deviator traffic. -/
theorem bindingTraffic_record (who : Player)
    {left right : ((reactiveApplication timeouts) leaks).Execution}
    (same : (bindingTraffic timeouts) leaks who left =
      (bindingTraffic timeouts) leaks who right)
    (command : ((reactiveApplication timeouts) leaks).Command) :
    (bindingTraffic timeouts) leaks who
        { left with environmentRecall := left.environmentRecall ++
          [⟨left.observeEnvironment ((reactiveApplication timeouts) leaks), command⟩] } =
      (bindingTraffic timeouts) leaks who
        { right with environmentRecall := right.environmentRecall ++
          [⟨right.observeEnvironment ((reactiveApplication timeouts) leaks),
              command⟩] } := by
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  rw [environments, observeEnvironment_eq_of_bindingTraffic who same]
  exact bindingTraffic_with_environmentRecall who same _

/-- An application command with no primary state change performs automatic
completion and records the command's original environment observation. -/
theorem environmentStep_application_of_pure
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (command : EnvironmentCommand graph)
    (unchanged : environmentStep timeouts execution.application
        command = PMF.pure execution.application) : execution.environmentStep
    ((reactiveApplication timeouts) leaks) (.application command) = PMF.pure
    { execution with
        application := execution.application.drain
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment ((reactiveApplication timeouts) leaks),
            .application command⟩] } := by
  change (((environmentStep timeouts execution.application command).map
      State.drain).map fun state => { execution with application := state }).map _ = _
  rw [unchanged, PMF.pure_map, PMF.pure_map, PMF.pure_map]

/-- While every ready event belongs to `who` or to chance, a packet authored by
any other player is rejected. -/
theorem handle_foreign_sender_none {who : Player}
    (state : EventGraphRuntime.State graph)
    (focal : ∀ event, state.config.cut.Ready event →
      graph.actor? event = none ∨
        graph.actor? event = some who)
    (message : Message Player (Payload graph)) (other : message.sender ≠ who) :
    handle timeouts state message = none := by
  cases accepted : handle timeouts state message with
  | none => rfl
  | some next =>
      exfalso
      obtain ⟨named, namedEq, namedReady, _, _⟩ :=
        handle_config_mem_step timeouts _ _ _ accepted
      have sender := handle_sender_actor timeouts _ _ _ accepted named
        namedEq
      rcases focal named namedReady with none | owned
      · rw [none] at sender
        cases sender
      · exact other (Option.some.inj (sender.symm.trans owned))

/-- Including a pending packet keeps equal deviator traffic when the handler
treats that packet alike for the deviator on both sides. -/
theorem include_bindingTraffic_of_handled {who : Player}
    {left right : ((reactiveApplication timeouts) leaks).Execution}
    (same : (bindingTraffic timeouts) leaks who left =
      (bindingTraffic timeouts) leaks who right)
    (id : MessageId Player)
    (handled : ∀ message, left.network.lookup id = some message →
      Option.map (fun state => state.playerView who)
          (handle timeouts left.application
              ⟨message.id, message.payload.call⟩) =
        Option.map (fun state => state.playerView who)
          (handle timeouts right.application
              ⟨message.id, message.payload.call⟩)) :
    (bindingTraffic timeouts) leaks who
        (left.includePending ((reactiveApplication timeouts) leaks) id) =
      (bindingTraffic timeouts) leaks who
        (right.includePending ((reactiveApplication timeouts) leaks) id) := by
  have networks : left.network = right.network := congrArg Prod.fst same
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) same
  cases found : left.network.lookup id with
  | none =>
      have rightFound : right.network.lookup id = none := networks ▸ found
      have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
      have environments : left.environmentRecall = right.environmentRecall :=
        congrArg (fun value => value.2.2.1) same
      have recalled : left.logs who = right.logs who :=
        congrArg (fun value => value.2.2.2.1) same
      have publics : left.application.publicView = right.application.publicView :=
        congrArg (fun value => value.2.2.2.2.2) same
      simp only [EventGraphRuntime.bindingTraffic, ReactiveApplication.Execution.includePending,
        MessageNetwork.includePending, found, rightFound]
      exact Prod.ext (by rw [networks]) (Prod.ext receipts
        (Prod.ext environments (Prod.ext recalled (Prod.ext views publics))))
  | some message =>
      apply bindingTraffic_include_of_handler timeouts leaks left right
          who same id message found
      simp only [reactiveApplication_handle]
      split
      · have beforeDrain := handled message found
        cases first : handle timeouts left.application
            ⟨message.id, message.payload.call⟩ with
        | none =>
            cases second : handle timeouts right.application
                ⟨message.id, message.payload.call⟩ with
            | none => rfl
            | some state => simp only [first, second, Option.map_none, Option.map_some,
                reduceCtorEq] at beforeDrain
        | some state =>
            cases second : handle timeouts right.application
                ⟨message.id, message.payload.call⟩ with
            | none => simp only [first, second, Option.map_none, Option.map_some,
                reduceCtorEq] at beforeDrain
            | some next =>
                have views : state.playerView who = next.playerView who := by
                  simpa only [first, second, Option.map_some, Option.some.injEq] using beforeDrain
                exact congrArg some (State.drain_playerView_congr state next who views)
      · rfl

/-- Including any pending packet keeps equal deviator traffic when every ready
event belongs to the deviator or to chance. -/
theorem focal_include_bindingTraffic {who : Player}
    {left right : ((reactiveApplication timeouts) leaks).Execution}
    (leftFocal : ∀ event, left.application.config.cut.Ready event →
      graph.actor? event = none ∨
        graph.actor? event = some who)
    (rightFocal : ∀ event, right.application.config.cut.Ready event →
      graph.actor? event = none ∨
        graph.actor? event = some who)
    (same : (bindingTraffic timeouts) leaks who left =
      (bindingTraffic timeouts) leaks who right)
    (id : MessageId Player) :
    (bindingTraffic timeouts) leaks who
        (left.includePending ((reactiveApplication timeouts) leaks) id) =
      (bindingTraffic timeouts) leaks who
        (right.includePending ((reactiveApplication timeouts) leaks) id) := by
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) same
  apply include_bindingTraffic_of_handled same id
  intro message _
  by_cases sender : message.sender = who
  · exact handle_playerView_congr_of_sender timeouts left.application
      right.application who ⟨message.id, message.payload.call⟩ views sender
  · rw [handle_foreign_sender_none left.application leftFocal
        ⟨message.id, message.payload.call⟩ sender,
      handle_foreign_sender_none right.application rightFocal
        ⟨message.id, message.payload.call⟩ sender]

/-- An application command keeps equal deviator traffic: clocks and expiry
read the public view, and public chance reads public data. -/
theorem application_environmentStep_traffic_congr
    {who : Player} {left right : ((reactiveApplication timeouts) leaks).Execution}
    (same : (bindingTraffic timeouts) leaks who left =
      (bindingTraffic timeouts) leaks who right)
    (command : EnvironmentCommand graph) :
    (left.environmentStep ((reactiveApplication timeouts) leaks) (.application command)).map
        ((bindingTraffic timeouts) leaks who) =
      (right.environmentStep ((reactiveApplication timeouts) leaks)
          (.application command)).map
        ((bindingTraffic timeouts) leaks who) := by
  let app := (reactiveApplication timeouts) leaks
  have pureCase : environmentStep timeouts left.application command =
      PMF.pure left.application →
      environmentStep timeouts right.application command =
        PMF.pure right.application →
      (left.environmentStep app (.application command)).map
          ((bindingTraffic timeouts) leaks who) =
        (right.environmentStep app (.application command)).map
          ((bindingTraffic timeouts) leaks who) := by
    intro leftPure rightPure
    rw [environmentStep_application_of_pure left command leftPure,
      environmentStep_application_of_pure right command rightPure, PMF.pure_map,
      PMF.pure_map]
    exact congrArg PMF.pure
      (bindingTraffic_drain timeouts leaks _ _ who
        (bindingTraffic_record (leaks := leaks) who same _))
  cases command with
  | advanceClock =>
      exact bindingTraffic_maintenance timeouts leaks left right who
          same .advanceClock (fun _ impossible => by cases impossible)
  | expire other =>
      exact bindingTraffic_maintenance timeouts leaks left right who
          same (.expire other) (fun _ impossible => by cases impossible)
  | executeSample other =>
      have publics : left.application.publicView = right.application.publicView :=
        congrArg (fun value => value.2.2.2.2.2) same
      have cuts := cut_eq_of_publicView_eq publics
      by_cases otherReady : left.application.config.cut.Ready other
      · have rightReady : right.application.config.cut.Ready other := by
          rw [← cuts]
          exact otherReady
        cases node : nodeView graph other with
        | sample payload law outputEq codeEq =>
            exact bindingTraffic_sample timeouts leaks left right who
              same other otherReady rightReady payload law outputEq codeEq node
        | bind owner payload outputEq codeEq =>
            apply pureCase
            · apply environmentStep_executeSample_of_nonsample _ _ _ otherReady
              intro payload law outputEq codeEq viewEq
              rw [node] at viewEq
              cases viewEq
            · apply environmentStep_executeSample_of_nonsample _ _ _ rightReady
              intro payload law outputEq codeEq viewEq
              rw [node] at viewEq
              cases viewEq
        | resolve owner payload binding checks outputEq codeEq =>
            apply pureCase
            · apply environmentStep_executeSample_of_nonsample _ _ _ otherReady
              intro payload law outputEq codeEq viewEq
              rw [node] at viewEq
              cases viewEq
            · apply environmentStep_executeSample_of_nonsample _ _ _ rightReady
              intro payload law outputEq codeEq viewEq
              rw [node] at viewEq
              cases viewEq
      · have rightNot : ¬ right.application.config.cut.Ready other := by
          rw [← cuts]
          exact otherReady
        exact pureCase (environmentStep_executeSample_of_not_ready _ _ _ otherReady)
          (environmentStep_executeSample_of_not_ready _ _ _ rightNot)

/-- **One focal round.** While every ready event belongs to the deviator or to
chance, one round of the deviator against silence, under any scheduler, gives
equal deviator traffic laws from equal deviator traffic. -/
theorem focalRound_traffic_congr
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler) (who : Player)
    (deviation : ((reactiveApplication timeouts) leaks).Policy)
    {left right : ((reactiveApplication timeouts) leaks).Execution}
    (leftFocal : ∀ event, left.application.config.cut.Ready event → graph.actor?
        event = none ∨ graph.actor? event = some who)
    (rightFocal : ∀ event, right.application.config.cut.Ready event →
        graph.actor? event = none ∨ graph.actor? event =
        some who)
    (same : (bindingTraffic timeouts) leaks who left =
        (bindingTraffic timeouts) leaks who right) :
    (((reactiveApplication timeouts) leaks).round scheduler
        (focalPlayers timeouts leaks who deviation) left).map
    ((bindingTraffic timeouts) leaks who) =
    (((reactiveApplication timeouts) leaks).round scheduler
        (focalPlayers timeouts leaks who deviation)
        right).map ((bindingTraffic timeouts) leaks who) := by
  let app := (reactiveApplication timeouts) leaks
  let players := focalPlayers timeouts leaks who deviation
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have observed := observeEnvironment_eq_of_bindingTraffic who same
  have networks : left.network = right.network := congrArg Prod.fst same
  unfold ReactiveApplication.round
  rw [environments, observed, PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro command _
  unfold ReactiveApplication.dispatch
  cases command with
  | activate actor =>
      simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.invoke, ReactiveApplication.Execution.activation_samples,
        PMF.bind_map, PMF.map_bind, Function.comp_def]
      rw [networks]
      apply bind_congr_on_support _
      intro sample _
      let first := left.sampledActivation app actor sample
      let second := right.sampledActivation app actor sample
      have activated : (bindingTraffic timeouts) leaks who first =
          (bindingTraffic timeouts) leaks who second :=
        bindingTraffic_activation timeouts leaks left right who actor
            same sample
      change ((players actor (first.logs actor) (first.observe app actor)).map
          (first.respond app actor)).map _ =
        ((players actor (second.logs actor) (second.observe app actor)).map
          (second.respond app actor)).map _
      by_cases deviator : actor = who
      · subst actor
        have recalled : first.logs who = second.logs who :=
          congrArg (fun value => value.2.2.2.1) activated
        rw [recalled, observe_eq_of_bindingTraffic who activated, PMF.map_comp, PMF.map_comp]
        apply map_congr_on_support _
        intro response _
        exact bindingTraffic_owner_response timeouts leaks first second
            who activated response
      · simp only [players, focalPlayers, Function.update_of_ne deviator,
          ReactiveApplication.silentPolicy_apply, PMF.pure_map]
        exact congrArg PMF.pure
            (bindingTraffic_silent timeouts leaks first second who
              actor
                activated ⟨none⟩ rfl)
  | «include» id =>
      simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
      apply congrArg PMF.pure
      have included := focal_include_bindingTraffic (leaks := leaks) leftFocal rightFocal same id
      rw [environments, observed]
      exact bindingTraffic_with_environmentRecall who included _
  | application command =>
      change ((left.environmentStep app (.application command)).bind
          (app.resume players none)).map _ =
        ((right.environmentStep app (.application command)).bind
          (app.resume players none)).map _
      rw [show app.resume players none = PMF.pure from rfl, PMF.bind_pure, PMF.bind_pure]
      exact application_environmentStep_traffic_congr same command
  | wait =>
      simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
      exact congrArg PMF.pure (bindingTraffic_record (leaks := leaks) who same .wait)

/-- **The focal phase.** While an event ready alone belongs to the deviator or
to chance, the deviator against silence, under any scheduler, gives equal
deviator traffic laws at the end of a completion run from equal deviator
traffic. -/
theorem focalPhase_traffic_congr
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (who : Player) (deviation : ((reactiveApplication timeouts) leaks).Policy)
    {event : graph.EventId}
    (focal : graph.actor? event = none ∨
      graph.actor? event = some who)
    (alone : ∀ (cut : graph.order.Cut) other, cut.Ready event →
      cut.Ready other → other = event) :
    ∀ (count : Nat) (left right : ((reactiveApplication timeouts) leaks).Execution),
      (event ∉ left.application.config.cut.completed → left.application.config.cut.Ready event) →
      (event ∉ right.application.config.cut.completed → right.application.config.cut.Ready event) →
      (bindingTraffic timeouts) leaks who left =
        (bindingTraffic timeouts) leaks who right →
      (((reactiveApplication timeouts) leaks).runUntil scheduler
          (focalPlayers timeouts leaks who deviation)
          (fun final => event ∈ final.application.config.cut.completed) count left).map
      ((bindingTraffic timeouts) leaks who) =
      (((reactiveApplication timeouts) leaks).runUntil scheduler
          (focalPlayers timeouts leaks who deviation)
          (fun final => event ∈ final.application.config.cut.completed) count right).map
          ((bindingTraffic timeouts) leaks who) := by
  intro count
  induction count with
  | zero =>
      intro left right _ _ same
      simp only [ReactiveApplication.runUntil, PMF.pure_map]
      exact congrArg PMF.pure same
  | succ count ih =>
      intro left right leftOpen rightOpen same
      have publics : left.application.publicView = right.application.publicView :=
        congrArg (fun value => value.2.2.2.2.2) same
      have cuts := cut_eq_of_publicView_eq publics
      by_cases stopped : event ∈ left.application.config.cut.completed
      · have rightStopped : event ∈ right.application.config.cut.completed := by
          rw [← cuts]
          exact stopped
        rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ left stopped,
          ReactiveApplication.runUntil_of_stop _ _ _ _ _ right rightStopped,
          PMF.pure_map, PMF.pure_map]
        exact congrArg PMF.pure same
      · have rightRunning : event ∉ right.application.config.cut.completed := by
          rw [← cuts]
          exact stopped
        simp only [ReactiveApplication.runUntil, stopped, rightRunning, ↓reduceIte,
          PMF.map_bind]
        apply bind_eq_of_map_eq _ _ _ _
          (focalRound_traffic_congr scheduler who deviation
            (fun other ready => alone _ other (leftOpen stopped) ready ▸ focal)
            (fun other ready => alone _ other (rightOpen rightRunning) ready ▸ focal)
            same)
        intro next nextReached other otherReached equal
        have nextReady : event ∉ next.application.config.cut.completed →
            next.application.config.cut.Ready event := by
          intro unfinished
          have unchanged := EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
            (fun query ready => alone _ query (leftOpen stopped) ready) unfinished
            (reactive_round_graph_steps timeouts leaks scheduler
              (focalPlayers timeouts leaks who deviation) left next nextReached)
          rw [unchanged]
          exact leftOpen stopped
        have otherReady : event ∉ other.application.config.cut.completed →
            other.application.config.cut.Ready event := by
          intro unfinished
          have unchanged := EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
            (fun query ready => alone _ query (rightOpen rightRunning) ready) unfinished
            (reactive_round_graph_steps timeouts leaks scheduler
              (focalPlayers timeouts leaks who deviation) right other otherReached)
          rw [unchanged]
          exact rightOpen rightRunning
        exact ih next other nextReady otherReady equal

/-- At a solitary focal or chance event, turning clients of the other players
are silent until the event completes. -/
theorem runUntil_turnPolicy_focal
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (bound : graph.EventId → Nat) (turns : Nat)
    (timing : EventGraphRuntime.TurnTiming graph turns) (reference : graph.BehavioralProfile)
    (who : Player) (deviation : ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.EventId) (focal : graph.actor? event = none ∨ graph.actor? event = some who)
    (alone : graph.Solitary event) (count : Nat)
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (pending : event ∉ execution.application.config.cut.completed →
      execution.application.config.cut.Ready event) :
    ((reactiveApplication timeouts) leaks).runUntil scheduler
        (Function.update (turnPolicy timeouts leaks bound turns timing reference) who deviation)
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      ((reactiveApplication timeouts) leaks).runUntil scheduler
        (focalPlayers timeouts leaks who deviation)
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  let app := (reactiveApplication timeouts) leaks
  apply app.runUntil_congr_of_agree scheduler _ _ _
    (fun current => event ∉ current.application.config.cut.completed →
      current.application.config.cut.Ready event)
  · intro current currentReady running command _ middle moved player active
    by_cases same : player = who
    · subst player
      simp only [focalPlayers, Function.update_self]
    · simp only [focalPlayers, Function.update_of_ne same]
      have activation : command = .activate player := by
        cases command with
        | activate actor => cases active; rfl
        | «include» => cases active
        | application => cases active
        | wait => cases active
      subst command
      have unchanged := activation_application timeouts leaks current middle player moved
      have idle : (middle.observe app player).application.publicView.ownTurn? player = none := by
        change middle.application.publicView.ownTurn? player = none
        rw [unchanged]
        cases turn : current.application.publicView.ownTurn? player with
        | none => rfl
        | some other =>
            obtain ⟨otherReady, otherOwned⟩ := PublicView.ownTurn?_spec _ player other turn
            have equal := alone _ ((current.application.publicView_eventReady _).mp otherReady)
              (currentReady running)
            subst other
            rcases focal with ownerless | owned
            · rw [ownerless] at otherOwned
              cases otherOwned
            · exact (same (Option.some.inj (otherOwned.symm.trans owned))).elim
      simp only [EventGraphRuntime.turnPolicy, idle]
  · intro current currentReady running next reached nextPending
    have unique (other : graph.EventId) (ready : current.application.config.cut.Ready other) :
        other = event := alone _ ready (currentReady running)
    rw [reactive_round_config_eq_of_pending timeouts leaks scheduler _ event current next
      unique nextPending reached]
    exact currentReady running
  · exact pending

end Focal
end Vegas
