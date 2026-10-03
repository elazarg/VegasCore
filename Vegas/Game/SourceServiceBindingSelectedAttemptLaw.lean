/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingAttemptLaw
import Vegas.Game.SourceServiceBindingSelectedContinuation
import Vegas.Game.SourceServiceBindingResponseFactorization

/-! # The actual selected binding response and its stopped joint law

At an actual protected selected input, the family draws the aligned source
commitment and records its canonical counted packet. Its actual continuation
is the owner-silent continuation, as is the original timing policy after that
recorded call. The existing physical attempt law consequently identifies the
same source draw, typed output, prefix parameter and public/foreign traffic.
No selection probability or source posterior is supplied.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The selected family's actual current draw and whole stopped continuation
join the real receipt-driven selection kernel. Freshness is an owner-local
resource supplied by the initialized selected-input theorem, not global
admission of arbitrary foreign responses. -/
theorem BindingSource.selected_attempt_law
    {Parameter : Type} {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (site : BindingSource setup profile event execution.application.config)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some site.owner, execution⟩))
    (fresh : execution.application.candidates.lookup
      (site.owner, .prepared (execution.application.publicView.bindingCount site.owner)) = .fresh)
    (turn : execution.application.publicView.ownTurn? site.owner = some event)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (follows : players site.owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile site.owner)
    (slot : Fin (turns + 1))
    (selected : sourceServiceTurn setup leaks site.owner event (execution.recall site.owner)
      (execution.observe (application setup leaks) site.owner) = some slot.val)
    (parameter : Parameter) :
    let app := application setup leaks
    let serial := execution.application.publicView.bindingCount site.owner
    let draw := commitKernel site.residual (site.source.view site.owner)
    let family := sourceServiceTurnFamily setup leaks bound profile site.owner event turns slot
    let familyPlayers := Function.update players site.owner family
    let traffic := (runtime setup).bindingPublicTraffic leaks site.owner
    let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
    let output : EventGraph.FieldRef (graph setup).layout (.binding site.owner site.payload) :=
      ⟨.inr event, site.outputEq⟩
    (family (execution.recall site.owner) (execution.observe app site.owner)).bind
      (fun response => (app.runUntilHorizon scheduler familyPlayers stop horizon
        (execution.respond app site.owner response)).map fun final =>
          (parameter, bindingResponseResult? site.owner site.payload execution response,
            output.get? final.application.config.store, traffic final)) =
    ((app.runUntilHorizon scheduler players stop horizon
      (execution.respond app site.owner
        ((runtime setup).reactiveBinding leaks site.owner event site.payload .failure serial))).map
        traffic).bind fun chosen => draw.map fun value =>
      (parameter, some value,
        some (if ((site.owner, execution.network.nextSerial site.owner), true) ∈ chosen.2.1
          then value else .failure), chosen) := by
  classical
  let app := application setup leaks
  let serial := execution.application.publicView.bindingCount site.owner
  let draw := commitKernel site.residual (site.source.view site.owner)
  let traffic := (runtime setup).bindingPublicTraffic leaks site.owner
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
  let output : EventGraph.FieldRef (graph setup).layout (.binding site.owner site.payload) :=
    ⟨.inr event, site.outputEq⟩
  have canonical : sourceServiceCanonicalOpportunity setup leaks bound profile site.owner event
      (execution.recall site.owner) (execution.observe app site.owner) =
      draw.map (fun value =>
        (runtime setup).reactiveBinding leaks site.owner event site.payload value serial) := by
    rw [sourceServiceCanonicalOpportunity_protected bound profile site.owner event
      (execution.recall site.owner) (execution.observe app site.owner) unrecorded fits,
      sourceServiceCanonicalPolicy_at_event setup leaks profile site.owner execution event turn
        site.owned, BindingSource.compiled_choice execution site, PMF.map_comp]
    apply map_congr_on_support _
    intro value _supported
    exact (runtime setup).canonicalServiceDecision_binding leaks site.owner
      (execution.recall site.owner) (execution.observe app site.owner) event site.payload
      site.outputEq site.code (nodeView_eq_bind site.outputEq site.code) serial
      (canonicalFreshSlot_canonical site.owner (execution.observe app site.owner).application fresh)
      value
  have responseLaw : sourceServiceTurnFamily setup leaks bound profile site.owner event turns slot
      (execution.recall site.owner) (execution.observe app site.owner) =
      draw.map (fun value =>
        (runtime setup).reactiveBinding leaks site.owner event site.payload value serial) := by
    unfold sourceServiceTurnFamily
    rw [app.turnScheduledPolicy_selected _ slot _ _ _ _ selected]
    exact canonical
  have continued (value : PublicationResult (L.Val site.payload)) :
      app.runUntilHorizon scheduler
        (Function.update players site.owner
          (sourceServiceTurnFamily setup leaks bound profile site.owner event turns slot))
        stop horizon
        (execution.respond app site.owner
          ((runtime setup).reactiveBinding leaks site.owner event site.payload value serial)) =
      app.runUntilHorizon scheduler players stop horizon
        (execution.respond app site.owner
          ((runtime setup).reactiveBinding leaks site.owner event site.payload value serial)) := by
    rw [sourceService_binding_selected_continuation_silent scheduler players bound profile
      site.owner event turns slot execution selected]
    symm
    unfold ReactiveApplication.runUntilHorizon
    apply sourceServiceTurnPolicy_runUntil_owner_silent setup leaks scheduler players bound turns
      timing profile site.owner follows
    · rw [((runtime setup).reactive_respond_application leaks execution site.owner _).1]
      exact (execution.application.publicView_eventReady event).mp
        (PublicView.ownTurn?_spec _ site.owner event turn).1
    · exact site.owned
    · exact (runtime setup).eventRecorded_respond leaks execution site.owner _ event rfl
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
  have attempt := site.attempt_law contract players timing profile execution event trace fresh turn
    unrecorded fits.withinDeadline follows parameter
  have tagged := congrArg (fun law => law.map fun chosen =>
    (chosen.1, some chosen.2.1, chosen.2.2.1, chosen.2.2.2)) attempt
  dsimp only
  rw [responseLaw, PMF.bind_map]
  calc
    _ = draw.bind (fun value => (app.runUntilHorizon scheduler players stop horizon
        (execution.respond app site.owner
          ((runtime setup).reactiveBinding leaks site.owner event site.payload value serial))).map
        fun final =>
          (parameter, some value, output.get? final.application.config.store, traffic final)) := by
      apply bind_congr_on_support draw
      intro value _supported
      dsimp only [Function.comp_def]
      change (app.runUntilHorizon scheduler
        (Function.update players site.owner
          (sourceServiceTurnFamily setup leaks bound profile site.owner event turns slot))
        stop horizon (execution.respond app site.owner
          ((runtime setup).reactiveBinding leaks site.owner event site.payload value serial))).map
        (fun final => (parameter, bindingResponseResult? site.owner site.payload execution
          ((runtime setup).reactiveBinding leaks site.owner event site.payload value serial),
            output.get? final.application.config.store, traffic final)) = _
      rw [continued value, currentResult value]
    _ = _ := by
      simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using tagged

end Vegas
