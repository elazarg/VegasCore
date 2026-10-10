/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicyFacts
import Interaction.ReactivePassiveContinuation

/-! # The actual downstream kernel at a final recovery callback

The scheduler may include, reject, expire or inspect the authored packet, and
other players may continue responding. If it never activates the recovering
owner again, the full native continuation is a fixed action-indexed kernel.
This identifies that kernel without asserting source payoff optimality for it.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Exact recovery continuation, including its conditioned private memory,
with every opponent continuation retained. No consistency assumption is needed. -/
theorem recoverReactivePolicy_final_callback (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (cursor count : Nat)
    (absent : ∀ past view, cursor ≤ past.length →
      ∀ command ∈ (scheduler past view).support,
        command.actor? (runtime.reactiveApplication leaks) ≠ some who)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (later : cursor ≤ execution.environmentRecall.length) :
    let app := runtime.reactiveApplication leaks
    let recovered := Function.update players who (runtime.recoverReactivePolicy leaks who policy)
    ((app.resume recovered (some who) execution).bind
      (app.runRounds scheduler recovered count)) =
    ((runtime.recoverReactiveImplementation leaks who policy).posterior
      (execution.recall who)).bind fun intentions =>
      (runtime.recoverReactiveResponse leaks who policy (execution.recall who) intentions
        (execution.observe app who)).bind fun response =>
          app.runRounds scheduler (Function.update players who app.silentPolicy) count
            (execution.respond app who response.1) := by
  dsimp only
  simp only [ReactiveApplication.resume, ReactiveApplication.invoke, Function.update_self,
    recoverReactivePolicy_apply, PMF.map_bind, PMF.bind_bind, PMF.bind_map]
  apply bind_congr_on_support
  intro intentions _supported
  apply bind_congr_on_support
  intro response _issued
  apply (runtime.reactiveApplication leaks).continuation_policy_independent_of_unactivated
    scheduler cursor who absent
  · intro actor different
    simp only [Function.update_of_ne different]
  · rwa [(runtime.reactiveApplication leaks).respond_environmentRecall]

/-- At a ready owned event, the final callback draws the genuine recovery law
and submits its source action before executing the native scheduler kernel. -/
theorem recoverReactivePolicy_final_ready_callback (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (cursor count : Nat)
    (absent : ∀ past view, cursor ≤ past.length →
      ∀ command ∈ (scheduler past view).support,
        command.actor? (runtime.reactiveApplication leaks) ≠ some who)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (later : cursor ≤ execution.environmentRecall.length)
    (event : graph.EventId)
    (turn : PublicView.ownTurn?
      (execution.observe (runtime.reactiveApplication leaks) who).application.publicView who =
        some event)
    (owner : (execution.observe (runtime.reactiveApplication leaks) who).application.who = who)
    (ready : PublicView.EventReady
      (execution.observe (runtime.reactiveApplication leaks) who).application.publicView event)
    (actor : graph.actor? event = some who) :
    let app := runtime.reactiveApplication leaks
    let view := execution.observe app who
    let history := execution.recall who
    let recovered := Function.update players who (runtime.recoverReactivePolicy leaks who policy)
    ((app.resume recovered (some who) execution).bind
      (app.runRounds scheduler recovered count)) =
    ((runtime.recoverReactiveImplementation leaks who policy).posterior history).bind
      fun intentions =>
        let observation : graph.PlayerObservation who := owner ▸ view.application.observation
        let recalled : graph.PlayerObservation who := { observation with
          ownActions := observation.ownActions.map
            (runtime.reactiveOriginal leaks who history intentions view.receipts) }
        (reactiveRecoveryLaw intentions event
          (graph.normalizePolicy who policy event actor recalled)).bind fun action =>
            app.runRounds scheduler (Function.update players who app.silentPolicy) count
              (execution.respond app who
                (runtime.reactiveDecision leaks who event action view.application)) := by
  dsimp only
  rw [runtime.recoverReactivePolicy_final_callback leaks who policy players scheduler
    cursor count absent execution later]
  apply bind_congr_on_support
  intro intentions _supported
  simp only [recoverReactiveResponse, turn, owner, ready, actor, ↓reduceDIte,
    ↓reduceIte, PMF.bind_map]
  rfl

end Vegas.EventGraphRuntime
