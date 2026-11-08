/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceFirstTurnCompletion
import Vegas.Pending.CanonicalOutcomeHead

/-! # A solitary event's segment of the service run

While a solitary event is ready and untouched, the service runs until it
completes. When that event is not a publication, honest owner clients of a
ready-independent reference preserve the reference's outcome law over that
segment, against arbitrary other players: the owner's first callback draws the
reference's action, the fixed action has its own continuation, and a chance
event steps by itself.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}

/-- An event that is not a publication accepts every action. -/
theorem effectiveAction_of_not_publication (config : (serviceGraph setup mode).Config)
    (event : (serviceGraph setup mode).EventId)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication)
    (action : (serviceGraph setup mode).Action event) :
    EffectiveAction config event action := by
  unfold EffectiveAction
  cases view : nodeView (serviceGraph setup mode) event with
  | resolve owner payload binding checks outputEq codeEq =>
      exact (notPublication (by rw [outputEq]; trivial)).elim
  | bind owner payload outputEq codeEq => trivial
  | sample payload law outputEq codeEq => trivial

/-- **A solitary segment preserves the outcome law.** From an initialized
execution where a solitary leading event that is not a publication is ready and
untouched, running until it completes preserves the outcome law of a
ready-independent reference followed by the event's owner, whatever the other
players do. -/
theorem soleSegment_outcomeLaw
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    {horizon turns : Nat} (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (contract : AsyncContract runtime leaks (serviceInitialLaw setup mode) horizon scheduler
      delay bound)
    (timely : AsyncTimely runtime delay bound)
    (client : (serviceGraph setup mode).BehavioralProfile) (independent : ReadyIndependent client)
    {Outcome : Type*} (read : (serviceGraph setup mode).Config → Outcome)
    (keyed : ∀ left right : (serviceGraph setup mode).Config, runKey left = runKey right →
      read left = read right)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (event : (serviceGraph setup mode).EventId)
    (follows : ∀ owner, (serviceGraph setup mode).actor? event = some owner →
      players owner = serviceReferenceTurnPolicy setup mode runtime.deadline leaks bound turns
        (firstTurnTiming setup turns mode) client owner)
    (solitary : (serviceGraph setup mode).Solitary event)
    (leading : (serviceGraph setup mode).Leading event)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (supported : execution ∈ ((runtime.reactiveApplication leaks).roundsFrom
      (serviceInitialLaw setup mode) scheduler players execution.environmentRecall.length).support)
    (untouched : Untouched setup leaks event execution)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    ((runtime.reactiveApplication leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      (fun final => outcomeLaw client read final.application.config) =
      outcomeLaw client read execution.application.config := by
  classical
  let app := runtime.reactiveApplication leaks
  have drained := outcomeLaw_drain independent read keyed
  have least : ∀ other, other ∉ execution.application.config.cut.completed →
      event.val ≤ other.val := fun _ unfinished => leading _ ready unfinished
  cases owned : (serviceGraph setup mode).actor? event with
  | none =>
      exact chance_runUntil_bind_continuation runtime leaks (outcomeLaw client read) drained
        scheduler players event solitary
        (fun config configReady action => step_bind_outcomeLaw_ownerless client read config event
          configReady (fun _ unfinished => leading config.cut configReady unfinished) owned action)
        owned (horizon - execution.environmentRecall.length) execution ready
  | some owner =>
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
        players execution.environmentRecall.length bounded execution supported
      have facts := legalFacts setup leaks horizon scheduler _ trace
      have active : owner ∉ execution.application.config.defaulted :=
        execution.application.active_of_ready_owned facts.quiescent ready owned
      let law := client owner event owned
        ((serviceGraph setup mode).playerObserve owner execution.application.config) active
      have callback (current : app.Execution)
          (same : current.application.config = execution.application.config) :
          serviceReferencePolicy setup mode runtime.deadline leaks client owner
              (current.logs owner) (current.observe app owner) =
            law.map (fun action => runtime.canonicalServiceDecision leaks owner
              (current.logs owner) (current.observe app owner) event action) := by
        have currentReady : current.application.config.cut.Ready event := same.symm ▸ ready
        have turn := serviceOwnTurn?_of_ready setup current.application currentReady owned
        have currentActive : owner ∉ current.application.config.defaulted := same.symm ▸ active
        have kernel (left right : (serviceGraph setup mode).Config) (sameConfig : left = right)
            (leftActive : owner ∉ left.defaulted) (rightActive : owner ∉ right.defaulted) :
            client owner event owned ((serviceGraph setup mode).playerObserve owner left)
                leftActive =
              client owner event owned ((serviceGraph setup mode).playerObserve owner right)
                rightActive := by
          subst sameConfig
          rfl
        rw [sourceServiceCanonicalPolicy_at_event_reference setup leaks client owner current event
          turn owned, dite_eq_right currentActive]
        exact congrArg (PMF.map _) (kernel _ _ same currentActive active)
      have mixture := serviceReference_firstTurn_mixture runtime leaks scheduler bound client
        owner event owned solitary players (follows owner owned) execution ready supported
        untouched bounded law callback
      rw [mixture, PMF.bind_bind, outcomeLaw_actor client read execution.application.config event
        ready least owner owned active]
      apply bind_congr_on_support _
      intro action _
      exact serviceReference_fixedAction_continuation runtime leaks scheduler delay bound client
        (outcomeLaw client read) drained contract timely owner event owned solitary players
        (follows owner owned) action execution ready supported untouched bounded
        (effectiveAction_of_not_publication _ event notPublication action)

end Vegas
