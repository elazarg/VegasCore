/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceReachedDecoding
import Vegas.Pending.ReactiveOwnerPhase
import Vegas.Pending.ReactiveSampleLikelihood

/-! # One deviating player's traffic, round by round, in every dependency mode

One player follows an arbitrary native policy while the scheduler satisfies the
asynchronous contract. This module collects the facts that read the deviator's
traffic round by round, for every dependency mode and deadline:

* equal deviator traffic gives equal deviator and scheduler observations, and
  is kept by recording the same command, by a packet the handler treats alike
  for the deviator, and by every application command
  (`Vegas.application_environmentStep_traffic_congr`): clocks and expiry read
  the public view, and public chance reads public data;
* while every ready event belongs to the deviator or to chance, a packet of any
  other player is rejected (`Vegas.handle_foreign_sender_none`);
* a completion run of an event ready alone ends with exactly one source step
  of it (`Vegas.runUntil_completion_step`);
* in the phase of an event ready alone that belongs to the deviator or to
  chance, the deviator's traffic at the end of the phase has a law that
  depends on the execution only through its traffic at the start
  (`Vegas.focalPhase_traffic_congr`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

section Steps

/-- Equal public views have equal completed cuts. -/
theorem cut_eq_of_publicView_eq {left right : EventGraphRuntime.State (serviceGraph setup mode)}
    (same : left.publicView = right.publicView) : left.config.cut = right.config.cut := by
  apply EventGraph.cut_eq_of_completionOrder_eq
  exact congrArg
      (fun view : PublicView (serviceGraph setup mode) => view.observation.completionOrder) same

variable (setup leaks)

/-- **A completion run makes one source step.** From an execution whose
configuration has `event` as its only ready event, any players under any
scheduler stop, once `event` has completed, at a configuration reached from the
starting one by one source step of `event`. -/
theorem runUntil_completion_step
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy)
    (event : (serviceGraph setup mode).EventId) (config : (serviceGraph setup mode).Config)
    (ready : config.cut.Ready event) (alone : ∀ other, config.cut.Ready other → other = event) : ∀
    (count : Nat) (execution stopped : (serviceApplication setup mode deadline leaks).Execution),
    execution.application.config = config → stopped ∈
    ((serviceApplication setup mode deadline leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).support →
    event ∈ stopped.application.config.cut.completed →
      ∃ action, stopped.application.config ∈ (config.step event ready action).support := by
  intro count
  induction count with
  | zero =>
      intro execution stopped same reached finished
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rw [same] at finished
      exact (ready.1 finished).elim
  | succ count ih =>
      intro execution stopped same reached finished
      subst same
      have running : event ∉ execution.application.config.cut.completed := ready.1
      simp only [ReactiveApplication.runUntil, running, ↓reduceIte] at reached
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      rcases round_configStep setup leaks scheduler players execution middle moved with
        unchanged | ⟨other, otherReady, action, member⟩
      · exact ih middle stopped unchanged rest finished
      · have otherIs : other = event := alone other otherReady
        subst otherIs
        have done : other ∈ middle.application.config.cut.completed := by
          rw [execution.application.config.step_cut other otherReady action _ member,
            EventOrder.Cut.mem_complete]
          exact Or.inl rfl
        rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ middle done] at rest
        cases (PMF.mem_support_pure_iff _ _).mp rest
        exact ⟨action, member⟩

end Steps

section Focal

variable (setup leaks)

/-- The players of a phase whose ready event belongs to `who` or to chance:
`who` follows `deviation` and every other player is silent. -/
abbrev focalPlayers (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy) : Player →
    (serviceApplication setup mode deadline leaks).Policy := Function.update
    (fun _ => (serviceApplication setup mode deadline leaks).silentPolicy) who deviation

variable {setup leaks}

/-- Equal deviator traffic gives equal deviator observations. -/
theorem observe_eq_of_bindingTraffic (who : Player)
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who right) :
    left.observe (serviceApplication setup mode deadline leaks) who = right.observe
        (serviceApplication setup mode deadline leaks) who := by
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) same
  change ReactiveApplication.PlayerView.mk _ _ _ = _
  rw [networks]
  exact congrArg₂ (fun view evidence =>
    (⟨right.network.observe who, view, evidence⟩ :
        (serviceApplication setup mode deadline leaks).PlayerView))
    views receipts

/-- Equal deviator traffic gives equal scheduler observations. -/
theorem observeEnvironment_eq_of_bindingTraffic (who : Player)
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who right) :
    left.observeEnvironment (serviceApplication setup mode deadline leaks) =
      right.observeEnvironment (serviceApplication setup mode deadline leaks) := by
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
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who right)
    (entries : List (serviceApplication setup mode deadline leaks).EnvironmentEntry) :
    (serviceRuntime setup mode deadline).bindingTraffic leaks who
    { left with environmentRecall := entries } =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who
      { right with environmentRecall := entries } := by
  dsimp only [EventGraphRuntime.bindingTraffic] at same ⊢
  exact congrArg (fun read => (read.1, read.2.1, entries, read.2.2.2)) same

/-- Recording the same command keeps equal deviator traffic. -/
theorem bindingTraffic_record (who : Player)
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who right)
    (command : (serviceApplication setup mode deadline leaks).Command) :
    (serviceRuntime setup mode deadline).bindingTraffic leaks who
        { left with environmentRecall := left.environmentRecall ++
          [⟨left.observeEnvironment (serviceApplication setup mode deadline leaks), command⟩] } =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who
        { right with environmentRecall := right.environmentRecall ++
          [⟨right.observeEnvironment (serviceApplication setup mode deadline leaks),
              command⟩] } := by
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  rw [environments, observeEnvironment_eq_of_bindingTraffic who same]
  exact bindingTraffic_with_environmentRecall who same _

/-- An application command that leaves the application state in place only
records itself. -/
theorem environmentStep_application_of_pure
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (command : EnvironmentCommand (serviceGraph setup mode))
    (unchanged : environmentStep (serviceRuntime setup mode deadline) execution.application
        command = PMF.pure execution.application) : execution.environmentStep
    (serviceApplication setup mode deadline leaks) (.application command) = PMF.pure
    { execution with environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment (serviceApplication setup mode deadline leaks), .application
            command⟩] } := by
  change ((environmentStep (serviceRuntime setup mode deadline) execution.application command).map
      fun state => { execution with application := state }).map _ = _
  rw [unchanged, PMF.pure_map, PMF.pure_map]

/-- While every ready event belongs to `who` or to chance, a packet authored by
any other player is rejected. -/
theorem handle_foreign_sender_none {who : Player}
    (state : EventGraphRuntime.State (serviceGraph setup mode))
    (focal : ∀ event, state.config.cut.Ready event →
      (serviceGraph setup mode).actor? event = none ∨
        (serviceGraph setup mode).actor? event = some who)
    (message : Message Player (Payload (serviceGraph setup mode))) (other : message.sender ≠ who) :
    handle (serviceRuntime setup mode deadline) state message = none := by
  cases accepted : handle (serviceRuntime setup mode deadline) state message with
  | none => rfl
  | some next =>
      exfalso
      obtain ⟨named, namedEq, namedReady, _, _⟩ :=
        handle_config_mem_step (serviceRuntime setup mode deadline) _ _ _ accepted
      have sender := handle_sender_actor (serviceRuntime setup mode deadline) _ _ _ accepted named
        namedEq
      rcases focal named namedReady with none | owned
      · rw [none] at sender
        cases sender
      · exact other (Option.some.inj (sender.symm.trans owned))

/-- Including a pending packet keeps equal deviator traffic when the handler
treats that packet alike for the deviator on both sides. -/
theorem include_bindingTraffic_of_handled {who : Player}
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who right)
    (id : MessageId Player)
    (handled : ∀ message, left.network.lookup id = some message →
      Option.map (fun state => state.playerView who)
          (handle (serviceRuntime setup mode deadline) left.application
              ⟨message.id, message.payload.call⟩) =
        Option.map (fun state => state.playerView who)
          (handle (serviceRuntime setup mode deadline) right.application
              ⟨message.id, message.payload.call⟩)) :
    (serviceRuntime setup mode deadline).bindingTraffic leaks who
        (left.includePending (serviceApplication setup mode deadline leaks) id) =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who
        (right.includePending (serviceApplication setup mode deadline leaks) id) := by
  have networks : left.network = right.network := congrArg Prod.fst same
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) same
  cases found : left.network.lookup id with
  | none =>
      have rightFound : right.network.lookup id = none := networks ▸ found
      have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
      have environments : left.environmentRecall = right.environmentRecall :=
        congrArg (fun value => value.2.2.1) same
      have recalled : left.recall who = right.recall who :=
        congrArg (fun value => value.2.2.2.1) same
      have publics : left.application.publicView = right.application.publicView :=
        congrArg (fun value => value.2.2.2.2.2) same
      simp only [EventGraphRuntime.bindingTraffic, ReactiveApplication.Execution.includePending,
        MessageNetwork.includePending, found, rightFound]
      exact Prod.ext (by rw [networks]) (Prod.ext receipts
        (Prod.ext environments (Prod.ext recalled (Prod.ext views publics))))
  | some message =>
      apply bindingTraffic_include_of_handler (serviceRuntime setup mode deadline) leaks left right
          who same id message found
      simp only [reactiveApplication_handle]
      split
      · exact handled message found
      · rfl

/-- Including any pending packet keeps equal deviator traffic when every ready
event belongs to the deviator or to chance. -/
theorem focal_include_bindingTraffic {who : Player}
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (leftFocal : ∀ event, left.application.config.cut.Ready event →
      (serviceGraph setup mode).actor? event = none ∨
        (serviceGraph setup mode).actor? event = some who)
    (rightFocal : ∀ event, right.application.config.cut.Ready event →
      (serviceGraph setup mode).actor? event = none ∨
        (serviceGraph setup mode).actor? event = some who)
    (same : (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who right)
    (id : MessageId Player) :
    (serviceRuntime setup mode deadline).bindingTraffic leaks who
        (left.includePending (serviceApplication setup mode deadline leaks) id) =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who
        (right.includePending (serviceApplication setup mode deadline leaks) id) := by
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) same
  apply include_bindingTraffic_of_handled same id
  intro message _
  by_cases sender : message.sender = who
  · exact handle_playerView_congr_of_sender (serviceRuntime setup mode deadline) left.application
      right.application who ⟨message.id, message.payload.call⟩ views sender
  · rw [handle_foreign_sender_none left.application leftFocal
        ⟨message.id, message.payload.call⟩ sender,
      handle_foreign_sender_none right.application rightFocal
        ⟨message.id, message.payload.call⟩ sender]

/-- An application command keeps equal deviator traffic: clocks and expiry
read the public view, and public chance reads public data. -/
theorem application_environmentStep_traffic_congr
    {who : Player} {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who right)
    (command : EnvironmentCommand (serviceGraph setup mode)) :
    (left.environmentStep (serviceApplication setup mode deadline leaks) (.application command)).map
        ((serviceRuntime setup mode deadline).bindingTraffic leaks who) =
      (right.environmentStep (serviceApplication setup mode deadline leaks)
          (.application command)).map
        ((serviceRuntime setup mode deadline).bindingTraffic leaks who) := by
  let app := serviceApplication setup mode deadline leaks
  have pureCase : environmentStep (serviceRuntime setup mode deadline) left.application command =
      PMF.pure left.application →
      environmentStep (serviceRuntime setup mode deadline) right.application command =
        PMF.pure right.application →
      (left.environmentStep app (.application command)).map
          ((serviceRuntime setup mode deadline).bindingTraffic leaks who) =
        (right.environmentStep app (.application command)).map
          ((serviceRuntime setup mode deadline).bindingTraffic leaks who) := by
    intro leftPure rightPure
    rw [environmentStep_application_of_pure left command leftPure,
      environmentStep_application_of_pure right command rightPure, PMF.pure_map,
      PMF.pure_map]
    exact congrArg PMF.pure (bindingTraffic_record (leaks := leaks) who same _)
  cases command with
  | advanceClock =>
      exact bindingTraffic_maintenance (serviceRuntime setup mode deadline) leaks left right who
          same .advanceClock (fun _ impossible => by cases impossible)
  | expire other =>
      exact bindingTraffic_maintenance (serviceRuntime setup mode deadline) leaks left right who
          same (.expire other) (fun _ impossible => by cases impossible)
  | executeSample other =>
      have publics : left.application.publicView = right.application.publicView :=
        congrArg (fun value => value.2.2.2.2.2) same
      have cuts := cut_eq_of_publicView_eq publics
      by_cases otherReady : left.application.config.cut.Ready other
      · have rightReady : right.application.config.cut.Ready other := by
          rw [← cuts]
          exact otherReady
        cases node : nodeView (serviceGraph setup mode) other with
        | sample payload law outputEq codeEq =>
            exact bindingTraffic_sample (serviceRuntime setup mode deadline) leaks left right who
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
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (leftFocal : ∀ event, left.application.config.cut.Ready event → (serviceGraph setup mode).actor?
        event = none ∨ (serviceGraph setup mode).actor? event = some who)
    (rightFocal : ∀ event, right.application.config.cut.Ready event →
        (serviceGraph setup mode).actor? event = none ∨ (serviceGraph setup mode).actor? event =
        some who)
    (same : (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
        (serviceRuntime setup mode deadline).bindingTraffic leaks who right) :
    ((serviceApplication setup mode deadline leaks).round scheduler
        (focalPlayers setup leaks who deviation) left).map
    ((serviceRuntime setup mode deadline).bindingTraffic leaks who) =
    ((serviceApplication setup mode deadline leaks).round scheduler
        (focalPlayers setup leaks who deviation)
        right).map ((serviceRuntime setup mode deadline).bindingTraffic leaks who) := by
  let app := serviceApplication setup mode deadline leaks
  let players := focalPlayers setup leaks who deviation
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
      have activated : (serviceRuntime setup mode deadline).bindingTraffic leaks who first =
          (serviceRuntime setup mode deadline).bindingTraffic leaks who second :=
        bindingTraffic_activation (serviceRuntime setup mode deadline) leaks left right who actor
            same sample
      change ((players actor (first.recall actor) (first.observe app actor)).map
          (first.respond app actor)).map _ =
        ((players actor (second.recall actor) (second.observe app actor)).map
          (second.respond app actor)).map _
      by_cases deviator : actor = who
      · subst actor
        have recalled : first.recall who = second.recall who :=
          congrArg (fun value => value.2.2.2.1) activated
        rw [recalled, observe_eq_of_bindingTraffic who activated, PMF.map_comp, PMF.map_comp]
        apply map_congr_on_support _
        intro response _
        exact bindingTraffic_owner_response (serviceRuntime setup mode deadline) leaks first second
            who activated response
      · simp only [players, focalPlayers, Function.update_of_ne deviator,
          ReactiveApplication.silentPolicy_apply, PMF.pure_map]
        exact congrArg PMF.pure
            (bindingTraffic_silent (serviceRuntime setup mode deadline) leaks first second who actor
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

/-- The phase invariant of a completion run: the ready event is pending at the
completed prefix below it, or it has completed. -/
def PhaseOpen (event : (serviceGraph setup mode).EventId)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop :=
    (execution.application.config.cut.IsPrefix event.val ∧ execution.application.config.cut.Ready
        event) ∨ execution.application.config.cut.IsPrefix (event.val + 1)

/-- A round of a running phase keeps the phase invariant, for an event that is
ready alone. -/
theorem PhaseOpen.round {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {event : (serviceGraph setup mode).EventId}
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (holds : PhaseOpen event execution)
    (running : event ∉ execution.application.config.cut.completed)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
        execution).support) :
    PhaseOpen event next := by
  have step := round_configStep setup leaks scheduler players execution next reached
  have current : execution.application.config.cut.IsPrefix event.val ∧
      execution.application.config.cut.Ready event := by
    rcases holds with current | advanced
    · exact current
    · exact (running ((advanced.2 event).mpr (Nat.lt_succ_self _))).elim
  rcases step with same | ⟨other, otherReady, action, member⟩
  · left
    rw [same]
    exact current
  · have otherIs : other = event := alone _ other current.2 otherReady
    subst otherIs
    right
    rw [execution.application.config.step_cut other otherReady action _ member]
    exact current.1.complete_at other otherReady rfl

/-- An open phase that has not stopped is at the completed prefix below its
ready event. -/
theorem PhaseOpen.running {event : (serviceGraph setup mode).EventId}
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (holds : PhaseOpen event execution)
    (running : event ∉ execution.application.config.cut.completed) :
    execution.application.config.cut.IsPrefix event.val ∧
      execution.application.config.cut.Ready event := by
  rcases holds with current | advanced
  · exact current
  · exact (running ((advanced.2 event).mpr (Nat.lt_succ_self _))).elim

/-- **The focal phase.** While an event ready alone belongs to the deviator or
to chance, the deviator against silence, under any scheduler, gives equal
deviator traffic laws at the end of a completion run from equal deviator
traffic. -/
theorem focalPhase_traffic_congr
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    {event : (serviceGraph setup mode).EventId}
    (focal : (serviceGraph setup mode).actor? event = none ∨
      (serviceGraph setup mode).actor? event = some who)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event) :
    ∀ (count : Nat) (left right : (serviceApplication setup mode deadline leaks).Execution),
      PhaseOpen event left → PhaseOpen event right →
      (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
        (serviceRuntime setup mode deadline).bindingTraffic leaks who right →
      ((serviceApplication setup mode deadline leaks).runUntil scheduler
          (focalPlayers setup leaks who deviation)
          (fun final => event ∈ final.application.config.cut.completed) count left).map
      ((serviceRuntime setup mode deadline).bindingTraffic leaks who) =
      ((serviceApplication setup mode deadline leaks).runUntil scheduler
          (focalPlayers setup leaks who deviation)
          (fun final => event ∈ final.application.config.cut.completed) count right).map
          ((serviceRuntime setup mode deadline).bindingTraffic leaks who) := by
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
            (fun other ready => alone _ other (leftOpen.running stopped).2 ready ▸ focal)
            (fun other ready => alone _ other (rightOpen.running rightRunning).2 ready ▸ focal)
            same)
        intro next nextReached other otherReached equal
        exact ih next other (leftOpen.round alone stopped nextReached)
          (rightOpen.round alone rightRunning otherReached) equal

end Focal
end Vegas
