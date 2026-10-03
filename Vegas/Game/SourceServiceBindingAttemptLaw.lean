/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingAttemptCompletion
import Vegas.Game.SourceServiceBindingChoiceSelection

/-! # Source commitment draws through actual include-or-miss selection

At an admitted clear prefix, the source commitment kernel draws a private
value and the manual timely canonical first call is submitted. Its actual
typed result and full public/foreign stopped traffic are the same joint law
as drawing that value alongside the value-independent physical selection
experiment. A true receipt for the original identifier selects the drawn
value; actual expiry selects typed failure. The reference failure call is
only a proof experiment. The prefix parameter remains in the same draw.

The subsequent owner follows any recorded turn policy, with arbitrary foreign
raw policies. No current geometric-policy transmission is asserted at an
unprotected opportunity.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The original source draw joins the actual acceptance-or-miss kernel,
including its typed output and the same full public/foreign stopped traffic. -/
theorem BindingSource.attempt_law
    {Parameter : Type} {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (bounds : MessageBounds (graph setup))
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (site : BindingSource setup profile event execution.application.config)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some site.owner, execution⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (execution.recall player) (execution.observe (application setup leaks) player) = false)
    (turn : execution.application.publicView.ownTurn? site.owner = some event)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (follows : players site.owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile site.owner)
    (parameter : Parameter) :
    let serial := execution.application.publicView.bindingCount site.owner
    let draw := commitKernel site.residual (site.source.view site.owner)
    let app := application setup leaks
    let traffic := (runtime setup).bindingPublicTraffic leaks site.owner
    let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
    let output : EventGraph.FieldRef (graph setup).layout (.binding site.owner site.payload) :=
      ⟨.inr event, site.outputEq⟩
    (draw.bind fun value =>
      (app.runUntilHorizon scheduler players stop horizon
        (execution.respond app site.owner
          ((runtime setup).reactiveBinding leaks site.owner event site.payload value serial))).map
        fun final =>
          (parameter, value, output.get? final.application.config.store, traffic final)) =
    ((app.runUntilHorizon scheduler players stop horizon
      (execution.respond app site.owner
        ((runtime setup).reactiveBinding leaks site.owner event site.payload .failure serial))).map
        traffic).bind fun selected => draw.map fun value =>
      (parameter, value,
        some (if ((site.owner, execution.network.nextSerial site.owner), true) ∈ selected.2.1
          then value else .failure), selected) := by
  classical
  dsimp only
  let app := application setup leaks
  let serial := execution.application.publicView.bindingCount site.owner
  let draw := commitKernel site.residual (site.source.view site.owner)
  let traffic := (runtime setup).bindingPublicTraffic leaks site.owner
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
  let output : EventGraph.FieldRef (graph setup).layout (.binding site.owner site.payload) :=
    ⟨.inr event, site.outputEq⟩
  let selectedResult := fun (receipts : List (MessageId Player × Bool))
      (value : PublicationResult (L.Val site.payload)) =>
    some (if ((site.owner, execution.network.nextSerial site.owner), true) ∈ receipts
      then value else .failure)
  have chosenResult : ∀ value, ∀ final ∈
      (app.runUntilHorizon scheduler players stop horizon
        (execution.respond app site.owner
          ((runtime setup).reactiveBinding leaks site.owner event site.payload
            value serial))).support,
      output.get? final.application.config.store =
        selectedResult (traffic final).2.1 value := by
    intro value final reached
    have outcome := sourceService_binding_attempt_completion bounds contract players timing profile
      execution event site trace clear turn unrecorded timely follows value final reached
    rcases outcome.2 with accepted | missed
    · dsimp only [selectedResult, traffic, bindingPublicTraffic]
      rw [ite_eq_left accepted.1, accepted.2.2]
      simp only [output, EventGraph.FieldRef.get?, EventGraph.Config.store_output,
        EventGraph.Config.complete_output_same]
      have castSome {alpha beta : Type} (same : alpha = beta) (item : alpha) :
          cast (congrArg Option same) (some item) = some (cast same item) := by
        cases same
        rfl
      change cast (congrArg Option (congrArg EventGraph.EventField.Value site.outputEq))
        (some (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) value)) = some value
      rw [castSome (congrArg EventGraph.EventField.Value site.outputEq)]
      have castInverse {alpha beta : Type} (same : alpha = beta) (item : beta) :
          cast same (cast same.symm item) = item := by
        cases same
        rfl
      exact congrArg some (castInverse (congrArg EventGraph.EventField.Value site.outputEq) value)
    · dsimp only [selectedResult, traffic, bindingPublicTraffic]
      rw [ite_eq_right missed.2.1]
      exact missed.2.2
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ site.owner event turn).1
  have choice := site.choice_selection setup leaks scheduler players bound turns timing profile
    horizon execution event ready follows parameter serial
  calc
    _ = (draw.bind fun value =>
        (app.runUntilHorizon scheduler players stop horizon
          (execution.respond app site.owner
            ((runtime setup).reactiveBinding leaks site.owner event site.payload value serial))).map
          fun final =>
            (parameter, value, selectedResult (traffic final).2.1 value, traffic final)) := by
      apply bind_congr_on_support draw
      intro value _supported
      apply map_congr_on_support _
      intro final reached
      rw [chosenResult value final reached]
    _ = _ := by
      have mapped := congrArg (fun law => law.map (fun selected =>
        (selected.1, selected.2.1,
          selectedResult selected.2.2.2.1 selected.2.1, selected.2.2))) choice
      simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using mapped

end Vegas
