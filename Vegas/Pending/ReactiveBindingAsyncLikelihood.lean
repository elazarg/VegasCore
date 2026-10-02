/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOpeningLikelihood
import Interaction.ReactiveObservation

/-! # Opaque binding traffic under an arbitrary public scheduler

While a binding is the only ready event, a silent scheduler round has the
same complete focal traffic law at equal traffic projections. The scheduler
may activate any player, include any pending packet, wait, advance the clock,
expire any event, or request a sample. Sampling cannot run a different event
before this binding completes. Opening and withholding packets cannot complete
a binding. Commitment acceptance remains opaque to a foreign observer.

The law retains actual network state, receipts, public scheduler recall and
the focal player's private recall and view. Passive samples need no
independence or coverage assumption. This concerns silent response rounds;
source decisions and effective disclosure require their own kernels.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

private theorem environmentStep_of_identity {Principal : Type} [DecidableEq Principal]
    (app : ReactiveApplication Principal) (execution : app.Execution)
    (command : app.EnvironmentCommand)
    (law : app.environment execution.application command = PMF.pure execution.application) :
    execution.environmentStep app (.application command) =
      PMF.pure { execution with environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .application command⟩] } := by
  simp only [ReactiveApplication.Execution.environmentStep, law, PMF.pure_map]

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem handle_noncommitment_of_sole_binding
    (state : State graph) (event : graph.EventId)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (sole : state.publicView.SoleReady event)
    (message : Message Player (Payload graph))
    (noncommitment : ∀ target candidate, message.payload ≠ .commitment target candidate) :
    handle runtime state message = none := by
  cases packet : message.payload with
  | commitment target candidate => exact (noncommitment target candidate packet).elim
  | malformed raw => simp only [handle, packet]
  | opening target candidate raw | withhold target =>
      by_cases ready : state.config.cut.Ready target
      · have current : target = event :=
          sole.2 target ((state.publicView_eventReady target).mpr ready)
        subst target
        simp only [handle, packet, dite_eq_left ready, node]
        split <;> rfl
      · simp only [handle, packet, dite_eq_right ready]

omit [DecidableEq Player] in
private theorem sample_of_sole_binding
    (state : State graph) (event : graph.EventId)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (sole : state.publicView.SoleReady event) (target : graph.EventId) :
    environmentStep runtime state (.executeSample target) = PMF.pure state := by
  by_cases ready : state.config.cut.Ready target
  · have current : target = event :=
      sole.2 target ((state.publicView_eventReady target).mpr ready)
    subst target
    apply environmentStep_executeSample_of_nonsample runtime state event ready
    intro other law otherOutput otherCode sample
    rw [node] at sample
    cases sample
  · exact environmentStep_executeSample_of_not_ready runtime state target ready

/-- Any pending inclusion has the same focal traffic at equal projections
when the only ready event is a binding, including rejected stale packets. -/
theorem bindingTraffic_include_of_sole_binding
    (focal : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (sole : left.application.publicView.SoleReady event) (id : MessageId Player) :
    runtime.bindingTraffic leaks focal
        (left.includePending (runtime.reactiveApplication leaks) id) =
      runtime.bindingTraffic leaks focal
        (right.includePending (runtime.reactiveApplication leaks) id) := by
  have networks : left.network = right.network := congrArg Prod.fst same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) same
  have rightSole : right.application.publicView.SoleReady event := publics ▸ sole
  cases found : left.network.lookup id with
  | none =>
      have rightFound : right.network.lookup id = none := networks ▸ found
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, rightFound] using same
  | some message =>
      have rightFound : right.network.lookup id = some message := networks ▸ found
      have identified : message.id = id :=
        (of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1)
      cases packet : message.payload.call with
      | commitment target candidate =>
          rcases message with ⟨messageId, ⟨call, evidence, token⟩⟩
          dsimp only at packet identified
          subst call
          subst messageId
          exact runtime.bindingTraffic_include leaks focal left right same id target
            candidate evidence token found
      | opening target candidate raw | withhold target | malformed raw =>
          have rejected (state : State graph) (ready : state.publicView.SoleReady event) :
              (runtime.reactiveApplication leaks).handle state message = none := by
            apply reactiveHandle_none
            apply handle_noncommitment_of_sole_binding runtime state event owner payload
              outputEq codeEq node ready
            intro query candidate impossible
            rw [packet] at impossible
            cases impossible
          have leftRejected := rejected left.application sole
          have rightRejected := rejected right.application rightSole
          simpa only [bindingTraffic, ReactiveApplication.Execution.includePending,
            MessageNetwork.includePending, found, rightFound, leftRejected, rightRejected,
            Option.getD_none, Option.isSome_none] using
            congrArg (fun value => (value.1.includePending id |>.2,
              value.2.1 ++ [(id, false)], value.2.2)) same

/-- Silence retains the same joint focal traffic after a common passive
activation, even when the activated player is not the focal observer. -/
theorem bindingTraffic_silent_activation
    (focal actor : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right) :
    ((runtime.reactiveApplication leaks).dispatch
        (fun _ => (runtime.reactiveApplication leaks).silentPolicy) (.activate actor) left).map
          (runtime.bindingTraffic leaks focal) =
      ((runtime.reactiveApplication leaks).dispatch
        (fun _ => (runtime.reactiveApplication leaks).silentPolicy) (.activate actor) right).map
          (runtime.bindingTraffic leaks focal) := by
  let app := runtime.reactiveApplication leaks
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.recall focal = right.recall focal :=
    congrArg (fun value => value.2.2.2.1) same
  have views : left.application.playerView focal = right.application.playerView focal :=
    congrArg (fun value => value.2.2.2.2.1) same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) same
  have environment : left.observeEnvironment app = right.observeEnvironment app := by
    change ReactiveApplication.EnvironmentView.mk left.network.publicView
      left.application.publicView left.receipts = _
    rw [networks, publics, receipts]
    rfl
  simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    ReactiveApplication.Command.actor?, PMF.map_bind, PMF.map_comp,
    PMF.bind_map]
  rw [show left.network.pending = right.network.pending from
    congrArg MessageNetwork.pending networks]
  apply bind_congr_on_support _
  intro selected _
  simp only [Function.comp_apply, ReactiveApplication.resume, ReactiveApplication.invoke,
    ReactiveApplication.silentPolicy_apply, PMF.pure_map]
  apply congrArg PMF.pure
  dsimp only [Function.comp_apply, bindingTraffic, ReactiveApplication.Execution.respond,
    ReactiveApplication.Execution.observe, MessageNetwork.learn]
  rw [networks, receipts, environments, environment, publics]
  congr 1
  by_cases acting : focal = actor
  · subst actor
    simp only [↓reduceIte]
    rw [recalled]
    have localView := congrArg (fun view : PlayerView graph =>
      (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
        ReactivePlayerView graph)) views
    change (runtime.reactiveApplication leaks).observePlayer left.application focal =
      (runtime.reactiveApplication leaks).observePlayer right.application focal at localView
    rw [localView, views]
  · simp only [acting, ↓reduceIte]
    rw [recalled, views]

/-- An arbitrary public scheduler's next command and silent response have a
hidden-value-independent joint traffic law during a sole-ready binding. -/
theorem bindingTraffic_silent_round
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (focal : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (sole : left.application.publicView.SoleReady event) :
    ((runtime.reactiveApplication leaks).round scheduler
        (fun _ => (runtime.reactiveApplication leaks).silentPolicy) left).map
          (runtime.bindingTraffic leaks focal) =
      ((runtime.reactiveApplication leaks).round scheduler
        (fun _ => (runtime.reactiveApplication leaks).silentPolicy) right).map
          (runtime.bindingTraffic leaks focal) := by
  let app := runtime.reactiveApplication leaks
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) same
  have environment : left.observeEnvironment app = right.observeEnvironment app := by
    change ReactiveApplication.EnvironmentView.mk left.network.publicView
      left.application.publicView left.receipts = _
    rw [networks, publics, receipts]
    rfl
  have rightSole : right.application.publicView.SoleReady event := publics ▸ sole
  have waiting : app.resume (fun _ => app.silentPolicy) none = PMF.pure := rfl
  dsimp only [app] at environment waiting
  simp only [ReactiveApplication.round, PMF.map_bind, environments]
  rw [environment]
  apply bind_congr_on_support _
  intro command _
  cases command with
  | activate actor =>
      exact runtime.bindingTraffic_silent_activation leaks focal actor left right same
  | «include» id =>
      have coupled := runtime.bindingTraffic_include_of_sole_binding leaks focal left right same
        event owner payload outputEq codeEq node sole id
      simpa only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.pure_map,
        PMF.pure_bind, PMF.map_comp, bindingTraffic, Function.comp_apply, environments,
        environment, app] using
        congrArg (fun traffic => PMF.pure (traffic.1, traffic.2.1,
          right.environmentRecall ++ [⟨right.observeEnvironment
            (runtime.reactiveApplication leaks), .include id⟩],
            traffic.2.2.2)) coupled
  | wait =>
      simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.pure_map,
        PMF.pure_bind]
      simpa only [bindingTraffic, Function.comp_apply, environments, environment, app] using
        congrArg (fun traffic => PMF.pure (traffic.1, traffic.2.1,
          right.environmentRecall ++ [⟨right.observeEnvironment
            (runtime.reactiveApplication leaks), .wait⟩], traffic.2.2.2)) same
  | application command =>
      cases command with
      | advanceClock =>
          simpa only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
            waiting, PMF.bind_pure] using
            runtime.bindingTraffic_maintenance leaks left right focal same .advanceClock (by
              intro query impossible
              cases impossible)
      | expire target =>
          simpa only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
            waiting, PMF.bind_pure] using
            runtime.bindingTraffic_maintenance leaks left right focal same (.expire target) (by
              intro query impossible
              cases impossible)
      | executeSample target =>
          have leftLaw := sample_of_sole_binding runtime left.application event owner payload
            outputEq codeEq node sole target
          have rightLaw := sample_of_sole_binding runtime right.application event owner payload
            outputEq codeEq node rightSole target
          have leftEnvironment := environmentStep_of_identity app left
            (.executeSample target) leftLaw
          have rightEnvironment := environmentStep_of_identity app right
            (.executeSample target) rightLaw
          dsimp only [app] at leftEnvironment rightEnvironment
          simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
            waiting, PMF.bind_pure, leftEnvironment, rightEnvironment, PMF.pure_map]
          simpa only [bindingTraffic, Function.comp_apply, environments, environment, app] using
            congrArg (fun traffic => PMF.pure (traffic.1, traffic.2.1,
              right.environmentRecall ++ [⟨right.observeEnvironment
                (runtime.reactiveApplication leaks),
                .application (.executeSample target)⟩], traffic.2.2.2)) same

end Vegas.EventGraphRuntime
