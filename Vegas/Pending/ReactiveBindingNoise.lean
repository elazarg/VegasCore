/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingObservation
import Vegas.Pending.ReactiveBinding
import Vegas.Pending.ReactiveFirstOpportunity
import GameTheory.Math.Probability.ConditionalObservation

/-! # Actual foreign binding observation channels -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- After a foreign opaque binding is actually submitted, the complete native
input at a passive activation is an independent observation channel for its
private source result. The original result is retained in the joint law. -/
theorem reactiveBinding_activation_joint_result_law
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (owner observer : Player) (different : observer ≠ owner)
    (event : graph.EventId) (payload : L.Ty) (serial : Nat)
    (choices : PMF (PublicationResult (L.Val payload))) :
    (choices.bind fun result =>
      ((execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveBinding leaks owner event payload result serial)).environmentStep
          (runtime.reactiveApplication leaks) (.activate observer)).map fun next =>
            (result, (next.recall observer,
              next.observe (runtime.reactiveApplication leaks) observer))) =
      bindPairLaw choices (fun _ =>
        ((execution.respond (runtime.reactiveApplication leaks) owner
          (runtime.reactiveBinding leaks owner event payload .failure serial)).environmentStep
            (runtime.reactiveApplication leaks) (.activate observer)).map fun next =>
              (next.recall observer,
                next.observe (runtime.reactiveApplication leaks) observer)) := by
  unfold bindPairLaw
  apply bind_congr_on_support
  intro result _
  rw [PMF.map_comp]
  have same := runtime.reactiveBinding_activation_other_input leaks execution owner observer
    different event payload result .failure serial
  have mapped := congrArg (PMF.map (fun input => (result, input))) same
  simpa only [PMF.map_comp, Function.comp_def] using mapped

/-- A genuine first prescribed binding callback has the same complete foreign
activation-input law for every source policy and every supported private memory.
The callback uses the unchanged actual behavioral prescribed compiler. -/
theorem prescribedReactivePolicy_binding_activation_input_law
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner observer : Player) (different : observer ≠ owner)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (focal : players owner = runtime.prescribedReactivePolicy leaks owner policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (count : Nat)
    (state : State graph) (execution : (runtime.reactiveApplication leaks).Execution)
    (reached : execution ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)).support)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (turn : execution.application.publicView.ownTurn? owner = some event)
    (earlierTurns : ∀ entry ∈ execution.recall owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event)
    (serial : Nat)
    (allocated : reactiveFreshSlot
      (execution.observe (runtime.reactiveApplication leaks) owner).application = some serial) :
    ((runtime.prescribedReactivePolicy leaks owner policy (execution.recall owner)
      (execution.observe (runtime.reactiveApplication leaks) owner)).bind fun action =>
        ((execution.respond (runtime.reactiveApplication leaks) owner action).environmentStep
          (runtime.reactiveApplication leaks) (.activate observer)).map fun next =>
            (next.recall observer, next.observe (runtime.reactiveApplication leaks) observer)) =
      ((execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveBinding leaks owner event payload .failure serial)).environmentStep
          (runtime.reactiveApplication leaks) (.activate observer)).map fun next =>
            (next.recall observer, next.observe (runtime.reactiveApplication leaks) observer) := by
  rw [prescribedReactivePolicy, ReactiveApplication.Implementation.policy_eq, PMF.bind_map]
  simp only [prescribedReactiveImplementation, PMF.bind_map, PMF.bind_bind]
  let baseline := ((execution.respond (runtime.reactiveApplication leaks) owner
    (runtime.reactiveBinding leaks owner event payload .failure serial)).environmentStep
      (runtime.reactiveApplication leaks) (.activate observer)).map fun next =>
        (next.recall observer, next.observe (runtime.reactiveApplication leaks) observer)
  change (((runtime.prescribedReactiveImplementation leaks owner policy).posterior
    (execution.recall owner)).bind fun intentions =>
      (runtime.prescribedReactiveResponse leaks owner policy (execution.recall owner) intentions
        (execution.observe (runtime.reactiveApplication leaks) owner)).bind fun response =>
          ((execution.respond (runtime.reactiveApplication leaks) owner response.1).environmentStep
            (runtime.reactiveApplication leaks) (.activate observer)).map fun next =>
              (next.recall observer, next.observe (runtime.reactiveApplication leaks) observer)) =
                baseline
  rw [← PMF.bind_const
    ((runtime.prescribedReactiveImplementation leaks owner policy).posterior
      (execution.recall owner)) baseline]
  apply bind_congr_on_support
  intro intentions memorySupported
  have flags := runtime.prescribedReactivePosterior_fresh_before_turn_of_initialized_support
    leaks owner policy players focal scheduler count state execution reached event earlierTurns
      intentions memorySupported
  let view := execution.observe (runtime.reactiveApplication leaks) owner
  have viewedTurn : view.application.publicView.ownTurn? owner = some event := turn
  have identity : view.application.who = owner := rfl
  have ready : view.application.publicView.EventReady event :=
    (view.application.publicView.ownTurn?_spec owner event viewedTurn).1
  have owned := (view.application.publicView.ownTurn?_spec owner event viewedTurn).2
  dsimp only [view] at viewedTurn identity ready
  rw [← PMF.bind_const
    (runtime.prescribedReactiveResponse leaks owner policy (execution.recall owner) intentions view)
    baseline]
  apply bind_congr_on_support
  intro response responseSupported
  simp only [prescribedReactiveResponse, viewedTurn, flags.1, flags.2, Bool.false_or,
    identity, ready, owned, ↓reduceIte] at responseSupported
  obtain ⟨action, _, equal⟩ := PMF.support_map .. ▸ responseSupported
  subst response
  change (((execution.respond (runtime.reactiveApplication leaks) owner
    (runtime.reactiveDecision leaks owner event action view.application)).environmentStep
      (runtime.reactiveApplication leaks) (.activate observer)).map
        (fun next => (next.recall observer,
          next.observe (runtime.reactiveApplication leaks) observer))) = baseline
  rw [runtime.reactiveDecision_binding_eq leaks owner owner event payload outputEq codeEq node
    action view.application serial allocated]
  exact runtime.reactiveBinding_activation_other_input leaks execution owner observer different
    event payload (cast (congrArg EventGraph.EventField.Action outputEq) action) .failure serial

end Vegas.EventGraphRuntime
