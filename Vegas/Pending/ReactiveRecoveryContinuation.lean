/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicyFacts
import Interaction.ReactivePassiveContinuation

/-! # The actual downstream kernel at a recovery callback

The scheduler may include, reject, expire or inspect the authored packet, and
other players may continue responding. The full native continuation retains the recovering owner
and every opponent policy at later callbacks. At a final callback the owner
can additionally be replaced by silence. Both kernels compare recovery with
alternative source-action lotteries when source values describe actual payoff.
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

/-- A ready recovery callback draws its genuine source-action law before
running the complete native continuation. Later callbacks retain the same
recovery policy and every opponent policy; no last-activation premise is needed. -/
theorem recoverReactivePolicy_ready_callback (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (count : Nat)
    (execution : (runtime.reactiveApplication leaks).Execution)
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
            app.runRounds scheduler
              (Function.update players who (runtime.recoverReactivePolicy leaks who policy)) count
              (execution.respond app who
                (runtime.reactiveDecision leaks who event action view.application)) := by
  dsimp only
  simp only [ReactiveApplication.resume, ReactiveApplication.invoke, Function.update_self,
    recoverReactivePolicy_apply, PMF.map_bind, PMF.bind_bind, PMF.bind_map]
  apply bind_congr_on_support
  intro intentions _supported
  simp only [recoverReactiveResponse, turn, owner, ready, actor, ↓reduceDIte,
    ↓reduceIte, PMF.bind_map]
  rfl

/-- Recovery dominates arbitrary posterior-dependent source-action lotteries
at one ready callback, with the incumbent recovery policy used at all later
callbacks. Values must equal actual full native continuation expectations and
the source law must maximize them. This proves one-response domination; source
value correspondence and arbitrary continuation-policy optimality are separate
obligations. No last-activation or consistency premise is needed. -/
theorem recoverReactivePolicy_ready_callback_comparison (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (count : Nat)
    (execution : (runtime.reactiveApplication leaks).Execution)
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
    let posterior := (runtime.recoverReactiveImplementation leaks who policy).posterior history
    let observation : graph.PlayerObservation who := owner ▸ view.application.observation
    let sourceLaw := fun intentions => graph.normalizePolicy who policy event actor
      { observation with ownActions := (observation.ownActions.map
          (runtime.reactiveOriginal leaks who history intentions view.receipts)) }
    let kernel := fun action => app.runRounds scheduler
      (Function.update players who (runtime.recoverReactivePolicy leaks who policy)) count
      (execution.respond app who
        (runtime.reactiveDecision leaks who event action view.application))
    ∀ (value : List (Option graph.Completion) → graph.Action event → ℝ)
      (utility : app.Execution → ℝ)
      (alternative : List (Option graph.Completion) → PMF (graph.Action event)),
      (∀ intentions ∈ posterior.support, ∀ action,
        expect (kernel action) utility = value intentions action) →
      (∀ intentions ∈ posterior.support, ∀ action ∈ (sourceLaw intentions).support,
        ∀ other, value intentions other ≤ value intentions action) →
      PayoffIntegrable (posterior.bind fun intentions =>
        (alternative intentions).bind kernel) utility →
      PayoffIntegrable ((app.resume
        (Function.update players who (runtime.recoverReactivePolicy leaks who policy))
        (some who) execution).bind
        (app.runRounds scheduler
          (Function.update players who (runtime.recoverReactivePolicy leaks who policy)) count))
        utility →
      expect (posterior.bind fun intentions => (alternative intentions).bind kernel) utility ≤
        expect ((app.resume
          (Function.update players who (runtime.recoverReactivePolicy leaks who policy))
          (some who) execution).bind
          (app.runRounds scheduler
            (Function.update players who (runtime.recoverReactivePolicy leaks who policy)) count))
          utility := by
  dsimp only
  intro value utility alternative values maximal alternativeIntegrable recoveredIntegrable
  rw [runtime.recoverReactivePolicy_ready_callback leaks who policy players scheduler
    count execution event turn owner ready actor] at recoveredIntegrable ⊢
  have alternativeLocal :=
    payoffIntegrable_bind_conditional_on_support _ _ _ alternativeIntegrable
  have recoveredLocal :=
    payoffIntegrable_bind_conditional_on_support _ _ _ recoveredIntegrable
  rw [expect_bind_tower _ _ _ alternativeIntegrable,
    expect_bind_tower _ _ _ recoveredIntegrable]
  apply expect_mono _
    (payoffIntegrable_bind_conditionalExpectation _ _ _ alternativeIntegrable)
    (payoffIntegrable_bind_conditionalExpectation _ _ _ recoveredIntegrable)
  intro intentions supported
  rw [expect_bind_tower _ _ _ (alternativeLocal intentions supported),
    expect_bind_tower _ _ _ (recoveredLocal intentions supported)]
  apply expect_le_const _ _
    (payoffIntegrable_bind_conditionalExpectation _ _ _ (alternativeLocal intentions supported))
  intro other _
  have bound := expect_mono (fun action used =>
    (values intentions supported other).trans_le
      ((maximal intentions supported action
        (reactiveRecoveryLaw_support intentions event _ action used) other).trans_eq
          (values intentions supported action).symm))
    (payoffIntegrable_constant _ _)
    (payoffIntegrable_bind_conditionalExpectation _ _ _ (recoveredLocal intentions supported))
  simpa only [expect_constant] using bound
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

/-- Compare genuine recovery with arbitrary posterior-dependent source-action
lotteries at a final callback. The source values must describe the actual
action-indexed native continuation, including the chosen terminal payoff.
All opponent policies remain in that continuation. This is a decision-site
comparison, not an off-path source/runtime simulation theorem. -/
theorem recoverReactivePolicy_final_callback_comparison (runtime : EventGraphRuntime graph)
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
    let posterior := (runtime.recoverReactiveImplementation leaks who policy).posterior history
    let observation : graph.PlayerObservation who := owner ▸ view.application.observation
    let sourceLaw := fun intentions => graph.normalizePolicy who policy event actor
      { observation with ownActions := (observation.ownActions.map
          (runtime.reactiveOriginal leaks who history intentions view.receipts)) }
    let kernel := fun action => app.runRounds scheduler
      (Function.update players who app.silentPolicy) count
      (execution.respond app who
        (runtime.reactiveDecision leaks who event action view.application))
    ∀ (value : List (Option graph.Completion) → graph.Action event → ℝ)
      (utility : app.Execution → ℝ)
      (alternative : List (Option graph.Completion) → PMF (graph.Action event)),
      (∀ intentions ∈ posterior.support, ∀ action,
        expect (kernel action) utility = value intentions action) →
      (∀ intentions ∈ posterior.support, ∀ action ∈ (sourceLaw intentions).support,
        ∀ other, value intentions other ≤ value intentions action) →
      PayoffIntegrable (posterior.bind fun intentions =>
        (alternative intentions).bind kernel) utility →
      PayoffIntegrable ((app.resume
        (Function.update players who (runtime.recoverReactivePolicy leaks who policy))
        (some who) execution).bind
        (app.runRounds scheduler
          (Function.update players who (runtime.recoverReactivePolicy leaks who policy)) count))
        utility →
      expect (posterior.bind fun intentions => (alternative intentions).bind kernel) utility ≤
        expect ((app.resume
          (Function.update players who (runtime.recoverReactivePolicy leaks who policy))
          (some who) execution).bind
          (app.runRounds scheduler
            (Function.update players who (runtime.recoverReactivePolicy leaks who policy)) count))
          utility := by
  dsimp only
  intro value utility alternative values maximal alternativeIntegrable recoveredIntegrable
  have kernelEq (action : graph.Action event) :
      (runtime.reactiveApplication leaks).runRounds scheduler
        (Function.update players who (runtime.recoverReactivePolicy leaks who policy)) count
        (execution.respond (runtime.reactiveApplication leaks) who
          (runtime.reactiveDecision leaks who event action
            (execution.observe (runtime.reactiveApplication leaks) who).application)) =
      (runtime.reactiveApplication leaks).runRounds scheduler
        (Function.update players who (runtime.reactiveApplication leaks).silentPolicy) count
        (execution.respond (runtime.reactiveApplication leaks) who
          (runtime.reactiveDecision leaks who event action
            (execution.observe (runtime.reactiveApplication leaks) who).application)) := by
    apply (runtime.reactiveApplication leaks).continuation_policy_independent_of_unactivated
      scheduler cursor who absent
    · intro other different
      simp only [Function.update_of_ne different]
    · rwa [(runtime.reactiveApplication leaks).respond_environmentRecall]
  have comparison := runtime.recoverReactivePolicy_ready_callback_comparison leaks who policy
    players scheduler count execution event turn owner ready actor value utility alternative
  dsimp only at comparison
  simp only [kernelEq] at comparison
  exact comparison values maximal alternativeIntegrable recoveredIntegrable

end Vegas.EventGraphRuntime
