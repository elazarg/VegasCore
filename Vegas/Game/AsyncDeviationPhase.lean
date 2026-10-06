/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDeviationCoupling
import Vegas.Pending.ReactiveOwnerPhase
import Vegas.Pending.ReactiveSampleLikelihood

/-! # One deviating player, phase by phase, under an arbitrary scheduler

Against the first-turn clients of a source profile, one player follows an
arbitrary native policy while the scheduler satisfies the asynchronous
contract. On the sequentialized graph exactly one event is ready between two
completions, and every other player is silent unless it owns that event.

This module collects the per-phase facts used to read the deviator's play as a
source deviation:

* a completion run from a completed prefix ends with exactly one source step of
  the ready event (`Vegas.runUntil_completion_step`);
* in a phase whose event belongs to the deviator or to chance, the deviator's
  traffic at the end of the phase has a law that depends on the execution only
  through its traffic at the start (`Vegas.focalPhase_traffic_congr`), for every
  scheduler: every packet of another player is rejected, the deviator's own
  packets are handled from its own view, and public chance reads public data.
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

/-- Equal public views have equal completed cuts. -/
theorem cut_eq_of_publicView_eq {left right : EventGraphRuntime.State (graph setup)}
    (same : left.publicView = right.publicView) : left.config.cut = right.config.cut := by
  apply EventGraph.cut_eq_of_completionOrder_eq
  exact congrArg (fun view : PublicView (graph setup) => view.observation.completionOrder) same

variable (setup leaks)

/-- **A completion run makes one source step.** From an execution whose
configuration is the completed prefix below the ready `event`, any players under
any scheduler stop, once `event` has completed, at a configuration reached from
the starting one by one source step of `event`. -/
theorem runUntil_completion_step (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (event : (graph setup).EventId)
    (config : (graph setup).Config) (ordered : config.cut.IsPrefix event.val)
    (ready : config.cut.Ready event) :
    ∀ (count : Nat) (execution stopped : (application setup leaks).Execution),
      execution.application.config = config →
      stopped ∈ ((application setup leaks).runUntil scheduler players
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
      · have otherIs : other = event :=
          Fin.ext (((ready_iff_rank setup _ event.val ordered other).mp otherReady).trans
            ((ready_iff_rank setup _ event.val ordered event).mp ready).symm)
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
abbrev focalPlayers (who : Player) (deviation : (application setup leaks).Policy) :
    Player → (application setup leaks).Policy :=
  Function.update (fun _ => (application setup leaks).silentPolicy) who deviation

variable {setup leaks}

/-- Equal deviator traffic gives equal deviator observations. -/
theorem observe_eq_of_bindingTraffic (who : Player)
    {left right : (application setup leaks).Execution}
    (same : (runtime setup).bindingTraffic leaks who left =
      (runtime setup).bindingTraffic leaks who right) :
    left.observe (application setup leaks) who = right.observe (application setup leaks) who := by
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) same
  change ReactiveApplication.PlayerView.mk _ _ _ = _
  rw [networks]
  exact congrArg₂ (fun view evidence =>
    (⟨right.network.observe who, view, evidence⟩ : (application setup leaks).PlayerView))
    views receipts

/-- Equal deviator traffic gives equal scheduler observations. -/
theorem observeEnvironment_eq_of_bindingTraffic (who : Player)
    {left right : (application setup leaks).Execution}
    (same : (runtime setup).bindingTraffic leaks who left =
      (runtime setup).bindingTraffic leaks who right) :
    left.observeEnvironment (application setup leaks) =
      right.observeEnvironment (application setup leaks) := by
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
    {left right : (application setup leaks).Execution}
    (same : (runtime setup).bindingTraffic leaks who left =
      (runtime setup).bindingTraffic leaks who right)
    (entries : List (application setup leaks).EnvironmentEntry) :
    (runtime setup).bindingTraffic leaks who { left with environmentRecall := entries } =
      (runtime setup).bindingTraffic leaks who { right with environmentRecall := entries } := by
  dsimp only [EventGraphRuntime.bindingTraffic] at same ⊢
  exact congrArg (fun read => (read.1, read.2.1, entries, read.2.2.2)) same

/-- Recording the same command keeps equal deviator traffic. -/
theorem bindingTraffic_record (who : Player)
    {left right : (application setup leaks).Execution}
    (same : (runtime setup).bindingTraffic leaks who left =
      (runtime setup).bindingTraffic leaks who right)
    (command : (application setup leaks).Command) :
    (runtime setup).bindingTraffic leaks who
        { left with environmentRecall := left.environmentRecall ++
          [⟨left.observeEnvironment (application setup leaks), command⟩] } =
      (runtime setup).bindingTraffic leaks who
        { right with environmentRecall := right.environmentRecall ++
          [⟨right.observeEnvironment (application setup leaks), command⟩] } := by
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  rw [environments, observeEnvironment_eq_of_bindingTraffic who same]
  exact bindingTraffic_with_environmentRecall who same _

/-- An application command that leaves the application state in place only
records itself. -/
theorem environmentStep_application_of_pure (execution : (application setup leaks).Execution)
    (command : EnvironmentCommand (graph setup))
    (unchanged : environmentStep (runtime setup) execution.application command =
      PMF.pure execution.application) :
    execution.environmentStep (application setup leaks) (.application command) =
      PMF.pure { execution with environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment (application setup leaks), .application command⟩] } := by
  change ((environmentStep (runtime setup) execution.application command).map
      fun state => { execution with application := state }).map _ = _
  rw [unchanged, PMF.pure_map, PMF.pure_map]

/-- While `event` is the ready event of a completed prefix and belongs to
`who` or to chance, a packet authored by any other player is rejected. -/
theorem handle_foreign_sender_none {event : (graph setup).EventId} {who : Player}
    (focal : (graph setup).actor? event = none ∨ (graph setup).actor? event = some who)
    (state : EventGraphRuntime.State (graph setup)) (ready : state.config.cut.Ready event)
    (message : Message Player (Payload (graph setup))) (other : message.sender ≠ who) :
    handle (runtime setup) state message = none := by
  cases accepted : handle (runtime setup) state message with
  | none => rfl
  | some next =>
      exfalso
      obtain ⟨named, namedEq, namedReady, _, _⟩ :=
        handle_config_mem_step (runtime setup) _ _ _ accepted
      have namedIs : named = event :=
        (soleReady_of_ready setup state ready).2 named
          ((state.publicView_eventReady named).mpr namedReady)
      subst namedIs
      have sender := handle_sender_actor (runtime setup) _ _ _ accepted named namedEq
      rcases focal with none | owned
      · rw [none] at sender
        cases sender
      · exact other (Option.some.inj (sender.symm.trans owned))

/-- Including a pending packet keeps equal deviator traffic when the handler
treats that packet alike for the deviator on both sides. -/
theorem include_bindingTraffic_of_handled {who : Player}
    {left right : (application setup leaks).Execution}
    (same : (runtime setup).bindingTraffic leaks who left =
      (runtime setup).bindingTraffic leaks who right)
    (id : MessageId Player)
    (handled : ∀ message, left.network.lookup id = some message →
      Option.map (fun state => state.playerView who)
          (handle (runtime setup) left.application ⟨message.id, message.payload.call⟩) =
        Option.map (fun state => state.playerView who)
          (handle (runtime setup) right.application ⟨message.id, message.payload.call⟩)) :
    (runtime setup).bindingTraffic leaks who
        (left.includePending (application setup leaks) id) =
      (runtime setup).bindingTraffic leaks who
        (right.includePending (application setup leaks) id) := by
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
      apply bindingTraffic_include_of_handler (runtime setup) leaks left right who same id
        message found
      simp only [reactiveApplication_handle]
      split
      · exact handled message found
      · rfl

/-- Including any pending packet keeps equal deviator traffic when the ready
event belongs to the deviator or to chance. -/
theorem focal_include_bindingTraffic {event : (graph setup).EventId} {who : Player}
    (focal : (graph setup).actor? event = none ∨ (graph setup).actor? event = some who)
    {left right : (application setup leaks).Execution}
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (same : (runtime setup).bindingTraffic leaks who left =
      (runtime setup).bindingTraffic leaks who right)
    (id : MessageId Player) :
    (runtime setup).bindingTraffic leaks who
        (left.includePending (application setup leaks) id) =
      (runtime setup).bindingTraffic leaks who
        (right.includePending (application setup leaks) id) := by
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) same
  apply include_bindingTraffic_of_handled same id
  intro message _
  by_cases sender : message.sender = who
  · exact handle_playerView_congr_of_sender (runtime setup) left.application
      right.application who ⟨message.id, message.payload.call⟩ views sender
  · rw [handle_foreign_sender_none focal left.application leftReady
        ⟨message.id, message.payload.call⟩ sender,
      handle_foreign_sender_none focal right.application rightReady
        ⟨message.id, message.payload.call⟩ sender]

/-- An application command keeps equal deviator traffic while the ready event
of a completed prefix is pending: clocks and expiry read the public view, and
public chance reads public data. -/
theorem application_environmentStep_traffic_congr {event : (graph setup).EventId}
    {who : Player} {left right : (application setup leaks).Execution}
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (same : (runtime setup).bindingTraffic leaks who left =
      (runtime setup).bindingTraffic leaks who right)
    (command : EnvironmentCommand (graph setup)) :
    (left.environmentStep (application setup leaks) (.application command)).map
        ((runtime setup).bindingTraffic leaks who) =
      (right.environmentStep (application setup leaks) (.application command)).map
        ((runtime setup).bindingTraffic leaks who) := by
  let app := application setup leaks
  have pureCase : environmentStep (runtime setup) left.application command =
      PMF.pure left.application →
      environmentStep (runtime setup) right.application command =
        PMF.pure right.application →
      (left.environmentStep app (.application command)).map
          ((runtime setup).bindingTraffic leaks who) =
        (right.environmentStep app (.application command)).map
          ((runtime setup).bindingTraffic leaks who) := by
    intro leftPure rightPure
    rw [environmentStep_application_of_pure left command leftPure,
      environmentStep_application_of_pure right command rightPure, PMF.pure_map,
      PMF.pure_map]
    exact congrArg PMF.pure (bindingTraffic_record (leaks := leaks) who same _)
  cases command with
  | advanceClock =>
      exact bindingTraffic_maintenance (runtime setup) leaks left right who same .advanceClock
        (fun _ impossible => by cases impossible)
  | expire other =>
      exact bindingTraffic_maintenance (runtime setup) leaks left right who same
        (.expire other) (fun _ impossible => by cases impossible)
  | executeSample other =>
      have publics : left.application.publicView = right.application.publicView :=
        congrArg (fun value => value.2.2.2.2.2) same
      have cuts := cut_eq_of_publicView_eq publics
      by_cases otherReady : left.application.config.cut.Ready other
      · have otherIs : other = event :=
          (soleReady_of_ready setup left.application leftReady).2 other
            ((left.application.publicView_eventReady other).mpr otherReady)
        subst otherIs
        cases node : nodeView (graph setup) other with
        | sample payload law outputEq codeEq =>
            exact bindingTraffic_sample (runtime setup) leaks left right who same other
              leftReady rightReady payload law outputEq codeEq node
        | bind owner payload outputEq codeEq =>
            apply pureCase
            · apply environmentStep_executeSample_of_nonsample _ _ _ leftReady
              intro payload law outputEq codeEq viewEq
              rw [node] at viewEq
              cases viewEq
            · apply environmentStep_executeSample_of_nonsample _ _ _ rightReady
              intro payload law outputEq codeEq viewEq
              rw [node] at viewEq
              cases viewEq
        | resolve owner payload binding checks outputEq codeEq =>
            apply pureCase
            · apply environmentStep_executeSample_of_nonsample _ _ _ leftReady
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

/-- **One focal round.** While `event` is ready and belongs to the deviator or
to chance, one round of the deviator against silence, under any scheduler,
gives equal deviator traffic laws from equal deviator traffic. -/
theorem focalRound_traffic_congr (scheduler : (application setup leaks).Scheduler)
    (who : Player) (deviation : (application setup leaks).Policy)
    {event : (graph setup).EventId}
    (focal : (graph setup).actor? event = none ∨ (graph setup).actor? event = some who)
    {left right : (application setup leaks).Execution}
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (same : (runtime setup).bindingTraffic leaks who left =
      (runtime setup).bindingTraffic leaks who right) :
    ((application setup leaks).round scheduler (focalPlayers setup leaks who deviation)
        left).map ((runtime setup).bindingTraffic leaks who) =
      ((application setup leaks).round scheduler (focalPlayers setup leaks who deviation)
        right).map ((runtime setup).bindingTraffic leaks who) := by
  let app := application setup leaks
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
      have activated : (runtime setup).bindingTraffic leaks who first =
          (runtime setup).bindingTraffic leaks who second :=
        bindingTraffic_activation (runtime setup) leaks left right who actor same sample
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
        exact bindingTraffic_owner_response (runtime setup) leaks first second who activated
          response
      · simp only [players, focalPlayers, Function.update_of_ne deviator,
          ReactiveApplication.silentPolicy_apply, PMF.pure_map]
        exact congrArg PMF.pure (bindingTraffic_silent (runtime setup) leaks first second who
          actor activated ⟨none⟩ rfl)
  | «include» id =>
      simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
      apply congrArg PMF.pure
      have included := focal_include_bindingTraffic (leaks := leaks) focal leftReady rightReady
        same id
      rw [environments, observed]
      exact bindingTraffic_with_environmentRecall who included _
  | application command =>
      change ((left.environmentStep app (.application command)).bind
          (app.resume players none)).map _ =
        ((right.environmentStep app (.application command)).bind
          (app.resume players none)).map _
      rw [show app.resume players none = PMF.pure from rfl, PMF.bind_pure, PMF.bind_pure]
      exact application_environmentStep_traffic_congr leftReady rightReady same command
  | wait =>
      simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
      exact congrArg PMF.pure (bindingTraffic_record (leaks := leaks) who same .wait)

/-- The phase invariant of a completion run: the ready event is pending at the
completed prefix below it, or it has completed. -/
def PhaseOpen (event : (graph setup).EventId) (execution : (application setup leaks).Execution) :
    Prop :=
  (execution.application.config.cut.IsPrefix event.val ∧
      execution.application.config.cut.Ready event) ∨
    execution.application.config.cut.IsPrefix (event.val + 1)

/-- A round of a running phase keeps the phase invariant. -/
theorem PhaseOpen.round {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy} {event : (graph setup).EventId}
    {execution next : (application setup leaks).Execution}
    (holds : PhaseOpen event execution)
    (running : event ∉ execution.application.config.cut.completed)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support) :
    PhaseOpen event next := by
  have step := round_configStep setup leaks scheduler players execution next reached
  have current : execution.application.config.cut.IsPrefix event.val ∧
      execution.application.config.cut.Ready event := by
    rcases holds with current | advanced
    · exact current
    · exact (running ((advanced.2 event).mpr (Nat.lt_succ_self _))).elim
  rcases step.prefix event.val current.1 with same | advanced
  · left
    rw [same]
    exact current
  · exact Or.inr advanced

/-- An open phase that has not stopped is at the completed prefix below its
ready event. -/
theorem PhaseOpen.running {event : (graph setup).EventId}
    {execution : (application setup leaks).Execution} (holds : PhaseOpen event execution)
    (running : event ∉ execution.application.config.cut.completed) :
    execution.application.config.cut.IsPrefix event.val ∧
      execution.application.config.cut.Ready event := by
  rcases holds with current | advanced
  · exact current
  · exact (running ((advanced.2 event).mpr (Nat.lt_succ_self _))).elim

/-- **The focal phase.** While the ready event belongs to the deviator or to
chance, the deviator against silence, under any scheduler, gives equal
deviator traffic laws at the end of a completion run from equal deviator
traffic. -/
theorem focalPhase_traffic_congr (scheduler : (application setup leaks).Scheduler)
    (who : Player) (deviation : (application setup leaks).Policy)
    {event : (graph setup).EventId}
    (focal : (graph setup).actor? event = none ∨ (graph setup).actor? event = some who) :
    ∀ (count : Nat) (left right : (application setup leaks).Execution),
      PhaseOpen event left → PhaseOpen event right →
      (runtime setup).bindingTraffic leaks who left =
        (runtime setup).bindingTraffic leaks who right →
      ((application setup leaks).runUntil scheduler (focalPlayers setup leaks who deviation)
          (fun final => event ∈ final.application.config.cut.completed) count left).map
          ((runtime setup).bindingTraffic leaks who) =
        ((application setup leaks).runUntil scheduler (focalPlayers setup leaks who deviation)
          (fun final => event ∈ final.application.config.cut.completed) count right).map
          ((runtime setup).bindingTraffic leaks who) := by
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
          (focalRound_traffic_congr scheduler who deviation focal
            (leftOpen.running stopped).2 (rightOpen.running rightRunning).2 same)
        intro next nextReached other otherReached equal
        exact ih next other (leftOpen.round stopped nextReached)
          (rightOpen.round rightRunning otherReached) equal

end Focal

section Phases

/-- **A phase without another owner.** Before an event of the deviator or of
chance completes, from a completed prefix whose recorded responses saw nothing
beyond it, the deviated first-turn profile runs as the deviator against
silence. -/
theorem runUntil_deviation_focal (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (deviation : (application setup leaks).Policy) (event : (graph setup).EventId)
    (focal : (graph setup).actor? event = none ∨ (graph setup).actor? event = some who)
    (count : Nat) (execution : (application setup leaks).Execution)
    (ordered : execution.application.config.cut.IsPrefix event.val)
    (seen : ReadySeen setup leaks event.val execution) :
    (application setup leaks).runUntil scheduler
        (deviatedTurnProfile bound turns (firstTurnTiming setup turns) profile who deviation)
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      (application setup leaks).runUntil scheduler (focalPlayers setup leaks who deviation)
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  rw [runUntil_deviation_eq_phase scheduler bound turns _ profile who deviation event count
    execution ordered seen]
  congr 1
  funext player
  by_cases same : player = who
  · subst player
    simp only [focalPlayers, Function.update_self]
  · simp only [focalPlayers, Function.update_of_ne same]
    rcases focal with actorless | owned
    · rw [phaseProfile_actorless setup leaks bound turns _ profile event actorless]
    · rw [phaseProfile_owned setup leaks bound turns _ profile event who owned,
        Function.update_of_ne same]

/-- **A phase of another owner.** Before an event of another player completes,
from a completion boundary of any players, if that owner's source decision at
the boundary configuration is `law` compiled to native responses, the deviated
first-turn profile runs as the `law`-mixture of the profiles in which the owner
decides one fixed action and the deviator plays against silence. -/
theorem runUntil_deviation_decided (scheduler : (application setup leaks).Scheduler)
    {reachers : Player → (application setup leaks).Policy}
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (deviation : (application setup leaks).Policy) (event : (graph setup).EventId)
    (owner : Player) (owned : (graph setup).actor? event = some owner) (foreign : owner ≠ who)
    (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler reachers event.val execution)
    (law : PMF ((graph setup).Action event))
    (policy : ∀ current : (application setup leaks).Execution,
      current.application.config = execution.application.config →
      sourceServiceCanonicalPolicy setup leaks profile owner (current.recall owner)
          (current.observe (application setup leaks) owner) =
        law.map fun action => (runtime setup).canonicalServiceDecision leaks owner
          (current.recall owner) (current.observe (application setup leaks) owner) event action)
    (count : Nat) :
    (application setup leaks).runUntil scheduler
        (deviatedTurnProfile bound turns (firstTurnTiming setup turns) profile who deviation)
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      law.bind fun action => (application setup leaks).runUntil scheduler
        (Function.update (focalPlayers setup leaks who deviation) owner
          (decidedTurnPolicy setup leaks bound owner event action))
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  obtain ⟨rank, ranked, seen⟩ := roundsFrom_ranked setup leaks scheduler reachers _ execution
    boundary.supported
  have rankEq := isPrefix_unique ranked boundary.ordered
  subst rankEq
  rw [runUntil_deviation_foreign scheduler bound turns _ profile who deviation event owner owned
    foreign count execution boundary.ordered seen (boundary.untouched event rfl)]
  change (PMF.pure (0 : Fin (turns + 1))).bind _ = _
  rw [PMF.pure_bind]
  exact firstTurn_runUntil_mixture_update event execution boundary owner owned bound turns
    profile law policy _ count

end Phases

end Vegas
