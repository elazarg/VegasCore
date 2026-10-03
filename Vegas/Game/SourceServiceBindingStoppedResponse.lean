/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingAttemptLaw
import Vegas.Game.SourceServiceBindingResponseFactorization

/-! # Actual stopped binding response decomposition

A protected unrecorded geometric response either waits or makes the actual
source commitment draw. Both branches continue through the real completion
stop. Waiting retains its genuine subsequent timing policy and can later
submit or miss. The current canonical call uses the value-independent public
selection experiment, with its own true receipt selecting the typed value.
The law retains the same prefix parameter and all public and foreign traffic.

This is a local response decomposition at an actual retained input, including
earlier protected waits. The original-boundary timing lottery and stopping at
its first selected input are separate facts.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The actual response and full stopped continuation split into real waiting
and the source draw joined to actual receipt-driven include-or-miss selection.
-/
theorem sourceService_binding_stopped_response
    {Parameter : Type} (parameter : Parameter)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (bounds : MessageBounds (graph setup))
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (profile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy)
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (site : BindingSource setup profile event execution.application.config)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some site.owner, execution⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (execution.recall player) (execution.observe (application setup leaks) player) = false)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (turn : execution.application.publicView.ownTurn? site.owner = some event)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1)
    (follows : players site.owner = sourceServiceTurnPolicy setup leaks bound horizon
      (geometricTiming setup horizon weight positive.le below.le) profile site.owner) :
    let app := application setup leaks
    let output : EventGraph.FieldRef (graph setup).layout (.binding site.owner site.payload) :=
      ⟨.inr event, site.outputEq⟩
    let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
    let traffic := (runtime setup).bindingPublicTraffic leaks site.owner
    let serial := execution.application.publicView.bindingCount site.owner
    (players site.owner (execution.recall site.owner) (execution.observe app site.owner)).bind
      (fun response => (app.runUntilHorizon scheduler players stop horizon
        (execution.respond app site.owner response)).map fun final =>
          (parameter, bindingResponseResult? site.owner site.payload execution response,
            output.get? final.application.config.store, traffic final)) =
    mix weight positive.le below.le
      ((app.runUntilHorizon scheduler players stop horizon
        (execution.respond app site.owner ⟨none⟩)).map fun final =>
          (parameter, none, output.get? final.application.config.store, traffic final))
      (((app.runUntilHorizon scheduler players stop horizon
        (execution.respond app site.owner
          ((runtime setup).reactiveBinding leaks site.owner event site.payload
            .failure serial))).map
            traffic).bind fun selected =>
        (commitKernel site.residual (site.source.view site.owner)).map fun value =>
          (parameter, some value,
            some (if ((site.owner, execution.network.nextSerial site.owner), true) ∈ selected.2.1
              then value else .failure), selected)) := by
  classical
  dsimp only
  let app := application setup leaks
  let output : EventGraph.FieldRef (graph setup).layout (.binding site.owner site.payload) :=
    ⟨.inr event, site.outputEq⟩
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
  let traffic := (runtime setup).bindingPublicTraffic leaks site.owner
  let serial := execution.application.publicView.bindingCount site.owner
  rw [follows, sourceServiceDecision_clear_binding_response bounds bound profile execution event
    site trace clear unrecorded turn fits weight positive below, mix_bind, PMF.pure_bind,
    PMF.bind_map]
  congr 1
  have fresh := sourceService_clear_counted_candidate_fresh bounds bound site.owner execution trace
    clear event unrecorded turn
  have currentResult (value : PublicationResult (L.Val site.payload)) :
      bindingResponseResult? site.owner site.payload execution
        ((runtime setup).reactiveBinding leaks site.owner event site.payload value serial) =
      some value := by
    let next := execution.respond app site.owner
      ((runtime setup).reactiveBinding leaks site.owner event site.payload value serial)
    change some (next.application.bindingResult (site.owner, .prepared serial) site.payload) =
      some value
    exact congrArg some ((runtime setup).reactiveBinding_result leaks site.owner event site.payload
      value serial execution fresh)
  have chosen := site.attempt_law contract players
    (geometricTiming setup horizon weight positive.le below.le) profile execution event
    ((bounds.riskMenu (runtime setup) leaks bound).toRawTrace _ _ _ trace) fresh turn unrecorded
    fits.withinDeadline follows parameter
  have tagged := congrArg (fun law => law.map (fun selected =>
    (selected.1, some selected.2.1, selected.2.2.1, selected.2.2.2))) chosen
  calc
    _ = ((commitKernel site.residual (site.source.view site.owner)).bind fun value =>
        (app.runUntilHorizon scheduler players stop horizon
          (execution.respond app site.owner
            ((runtime setup).reactiveBinding leaks site.owner event site.payload
              value serial))).map
          fun final =>
            (parameter, some value, output.get? final.application.config.store,
              traffic final)) := by
      apply bind_congr_on_support _
      intro value _supported
      dsimp only [Function.comp_def]
      rw [currentResult value]
    _ = _ := by
      simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using tagged

end Vegas
