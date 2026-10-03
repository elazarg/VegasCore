/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveSampleLikelihood
import Vegas.Pending.ReactiveBindingAsyncLikelihood

/-! # Actual silent traffic at a sole-ready public sample

Every player packet is rejected while the only ready event is public chance.
An arbitrary public scheduler therefore preserves the full focal traffic
coupling through each silent round. The actual public sample is coupled by
its common draw; stale sampling requests, inclusion, clock and expiry are
all covered without a cache or hidden-state agreement premise.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem handle_of_sole_sample
    (state : State graph) (event : graph.EventId)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (node : nodeView graph event = .sample payload law outputEq codeEq)
    (sole : state.publicView.SoleReady event)
    (message : Message Player (Payload graph)) :
    handle runtime state message = none := by
  cases packet : message.payload with
  | malformed raw => simp only [handle, packet]
  | commitment target candidate | opening target candidate raw | withhold target =>
      by_cases ready : state.config.cut.Ready target
      · have current : target = event :=
          sole.2 target ((state.publicView_eventReady target).mpr ready)
        subst target
        simp only [handle, packet, dite_eq_left ready, node]
        split <;> rfl
      · simp only [handle, packet, dite_eq_right ready]

/-- Every pending inclusion rejects its packet at a sole-ready chance event.
The resulting receipts, network and focal traffic are the actual ones. -/
theorem bindingTraffic_include_of_sole_sample
    (focal : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (event : graph.EventId) (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (node : nodeView graph event = .sample payload law outputEq codeEq)
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
      have rejected (state : State graph) (ready : state.publicView.SoleReady event) :
          (runtime.reactiveApplication leaks).handle state message = none := by
        apply reactiveHandle_none
        exact handle_of_sole_sample runtime state event payload law outputEq codeEq node ready _
      have leftRejected := rejected left.application sole
      have rightRejected := rejected right.application rightSole
      simpa only [bindingTraffic, ReactiveApplication.Execution.includePending,
        MessageNetwork.includePending, found, rightFound, leftRejected, rightRejected,
        Option.getD_none, Option.isSome_none] using
        congrArg (fun value => (value.1.includePending id |>.2,
          value.2.1 ++ [(id, false)], value.2.2)) same

/-- The genuine round law retains equal complete focal traffic while chance
is the only ready event. A successful sample uses its common public draw. -/
theorem bindingTraffic_sample_silent_round
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (focal : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (event : graph.EventId) (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (node : nodeView graph event = .sample payload law outputEq codeEq)
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
      have coupled := runtime.bindingTraffic_include_of_sole_sample leaks focal left right same
        event payload law outputEq codeEq node sole id
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
          by_cases current : target = event
          · subst target
            simpa only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
              waiting, PMF.bind_pure] using
              runtime.bindingTraffic_sample leaks left right focal same event
                ((left.application.publicView_eventReady event).mp sole.1)
                ((right.application.publicView_eventReady event).mp rightSole.1)
                payload law outputEq codeEq node
          · have notReady (state : State graph) (ready : state.publicView.SoleReady event) :
                ¬state.config.cut.Ready target := by
              intro active
              exact current (ready.2 target ((state.publicView_eventReady target).mpr active))
            have leftLaw := environmentStep_executeSample_of_not_ready runtime left.application
              target (notReady left.application sole)
            have rightLaw := environmentStep_executeSample_of_not_ready runtime right.application
              target (notReady right.application rightSole)
            change (runtime.reactiveApplication leaks).environment left.application
              (.executeSample target) = _ at leftLaw
            change (runtime.reactiveApplication leaks).environment right.application
              (.executeSample target) = _ at rightLaw
            simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
              waiting, PMF.bind_pure, ReactiveApplication.Execution.environmentStep,
              leftLaw, rightLaw, PMF.pure_map]
            simpa only [bindingTraffic, Function.comp_apply, environments, environment, app] using
              congrArg (fun traffic => PMF.pure (traffic.1, traffic.2.1,
                right.environmentRecall ++ [⟨right.observeEnvironment
                  (runtime.reactiveApplication leaks),
                  .application (.executeSample target)⟩], traffic.2.2.2)) same

end Vegas.EventGraphRuntime
