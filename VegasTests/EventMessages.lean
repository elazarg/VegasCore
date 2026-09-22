/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphAssembly
import Vegas.Pending.EventApplication
import VegasTests.SourceSemantics

/-! # Native compiled-event message integration

The mixed source fixture is executed through native commitment and opening
handlers followed by the dependent chance command.  A separate application
trace checks that message delivery alone remains observational and does not
complete an event.
-/

namespace VegasTests.EventMessages

open GameTheory.Math.Probability Interaction Vegas
open SourceProgram.EventLowering

noncomputable section

private abbrev TestPlayer := VegasTests.SourceSemantics.Player
private abbrev graph := VegasTests.SourceSemantics.mixedInitial.eventGraph

private def runtime : EventGraphRuntime graph where
  deadline _ := 10

private abbrev app := runtime.application

private def initial : app.State :=
  MessageApplication.State.initial app <|
    EventGraphRuntime.State.initial VegasTests.SourceSemantics.mixedInitial.eventInputs

private abbrev choiceEvent : graph.EventId := ⟨0, by decide⟩
private abbrev choiceReveal : graph.EventId := ⟨1, by decide⟩
private abbrev seedReveal : graph.EventId := ⟨2, by decide⟩
private abbrev coinEvent : graph.EventId := ⟨3, by decide⟩

private abbrev choiceHandle : EventGraphRuntime.Handle graph :=
  (.alice, .prepared 0)

private abbrev seedHandle : EventGraphRuntime.Handle graph :=
  (.alice, .initial ⟨0, by decide⟩)

private def choiceRaw (value : Option Bool) : EventGraphRuntime.Raw simpleExpr :=
  ⟨.option .bool, value⟩

private def seedRaw : EventGraphRuntime.Raw simpleExpr := ⟨.bool, true⟩

private def prepared : EventGraphRuntime.State graph :=
  EventGraphRuntime.privateStep initial.application .alice
    (.prepare 0 (choiceRaw none))

private def commitment : Message TestPlayer (EventGraphRuntime.Payload graph) :=
  ⟨(.alice, 0), .commitment choiceEvent choiceHandle⟩

private theorem choiceReady : prepared.config.cut.Ready choiceEvent := by
  change (EventOrder.Cut.empty graph.order).Ready choiceEvent
  decide

private theorem choiceTimely : prepared.WithinDeadline runtime choiceEvent := by
  change 0 < 10
  decide

private theorem choiceUnused : prepared.HandleUnused choiceHandle := by
  intro field accepted
  change (EventGraphRuntime.State.initial
    VegasTests.SourceSemantics.mixedInitial.eventInputs).accepted field =
      some choiceHandle at accepted
  obtain ⟨input, owner, payload, _field, _layout, handle⟩ :=
    EventGraphRuntime.State.initial_accepted_eq_some
      VegasTests.SourceSemantics.mixedInitial.eventInputs field choiceHandle accepted
  cases handle

private theorem preparedResult :
    prepared.bindingResult choiceHandle (.option .bool) = .success none := by
  rfl

private def bound : EventGraphRuntime.State graph :=
  { (prepared.complete choiceEvent choiceReady (.success none) (.success none)) with
    accepted := Function.update prepared.accepted (.inr choiceEvent) (some choiceHandle)
    candidates := prepared.candidates.freeze choiceHandle }

private theorem handle_commitment :
    EventGraphRuntime.handle runtime prepared commitment = some bound := by
  unfold commitment
  rw [EventGraphRuntime.handle_commitment_eq runtime prepared (.alice, 0) choiceEvent
    choiceHandle .alice (.option .bool) rfl rfl rfl choiceReady choiceTimely rfl rfl rfl
    choiceUnused]
  simp [bound, preparedResult]

private def deliveryOnly : List app.Action := [
  .privateCommand .alice (.prepare 0 (choiceRaw none)),
  .submit .alice (.commitment choiceEvent choiceHandle),
  .deliver .alice (.alice, 0)]

/-- Delivery exposes the pending commitment to the recipient but does not
install the binding output. Inclusion is the application transition. -/
example :
    (app.run deliveryOnly initial).map
        (fun state => state.application.config.outputs choiceEvent) =
      FinDist.pure none := by
  simp only [deliveryOnly, MessageApplication.run, MessageApplication.step, app,
    EventGraphRuntime.application, FinDist.pure_bind, FinDist.bind_pure,
    FinDist.map_pure]
  change FinDist.pure
    ((EventGraphRuntime.State.initial
      VegasTests.SourceSemantics.mixedInitial.eventInputs).config.outputs choiceEvent) =
        FinDist.pure none
  rfl

private def choiceOpening : Message TestPlayer (EventGraphRuntime.Payload graph) :=
  ⟨(.alice, 1), .opening choiceReveal choiceHandle (choiceRaw none)⟩

private def seedOpening : Message TestPlayer (EventGraphRuntime.Payload graph) :=
  ⟨(.alice, 2), .opening seedReveal seedHandle seedRaw⟩

private theorem choiceRevealReady : bound.config.cut.Ready choiceReveal := by
  unfold bound prepared initial
  decide

private theorem choiceRevealTimely : bound.WithinDeadline runtime choiceReveal := by
  change 0 < 10
  decide

private def choiceOpened : EventGraphRuntime.State graph :=
  bound.complete choiceReveal choiceRevealReady true (.success none)

private theorem handle_choice_opening :
    EventGraphRuntime.handle runtime bound choiceOpening = some choiceOpened := by
  unfold choiceOpening choiceRaw
  rw [EventGraphRuntime.handle_opening_eq runtime bound (.alice, 1) choiceReveal
    choiceHandle .alice (.option .bool) _ _ rfl rfl rfl choiceRevealReady
    choiceRevealTimely rfl rfl rfl none rfl rfl (.success none) rfl]
  rfl

private theorem seedRevealReady : choiceOpened.config.cut.Ready seedReveal := by
  unfold choiceOpened bound prepared initial
  decide

private theorem seedRevealTimely : choiceOpened.WithinDeadline runtime seedReveal := by
  change 0 < 10
  decide

private def seedOpened : EventGraphRuntime.State graph :=
  choiceOpened.complete seedReveal seedRevealReady true (.success true)

private theorem handle_seed_opening :
    EventGraphRuntime.handle runtime choiceOpened seedOpening = some seedOpened := by
  unfold seedOpening seedRaw
  rw [EventGraphRuntime.handle_opening_eq runtime choiceOpened (.alice, 2) seedReveal
    seedHandle .alice .bool _ _ rfl rfl rfl seedRevealReady seedRevealTimely
    rfl rfl rfl true rfl rfl (.success true) rfl]
  rfl

private def settled? : Option (EventGraphRuntime.State graph) := do
  let afterChoice ← EventGraphRuntime.handle runtime prepared commitment
  let afterChoiceOpening ← EventGraphRuntime.handle runtime afterChoice choiceOpening
  EventGraphRuntime.handle runtime afterChoiceOpening seedOpening

private theorem settled_eq : settled? = some seedOpened := by
  unfold settled?
  rw [handle_commitment]
  change (do
    let afterChoiceOpening ← EventGraphRuntime.handle runtime bound choiceOpening
    EventGraphRuntime.handle runtime afterChoiceOpening seedOpening) = some seedOpened
  rw [handle_choice_opening]
  exact handle_seed_opening

private def successfulRun : FinDist (EventGraphRuntime.State graph) :=
  match settled? with
  | none => FinDist.pure prepared
  | some settled => EventGraphRuntime.environmentStep runtime settled (.executeSample coinEvent)

private def payout? (state : EventGraphRuntime.State graph) :
    Option (List (TestPlayer × Int)) :=
  if terminal : state.config.cut.Terminal then
    some (state.config.terminalPayoffs terminal)
  else none

/-- Native commitment and opening handlers followed by the chance command
reach the compiled terminal graph and retain the source program's successful
payoff. The fair coin is sampled once, but it does not affect this branch. -/
example :
    successfulRun.map payout? =
      FinDist.pure (some [(.alice, 10)]) := by
  unfold successfulRun
  rw [settled_eq]
  simp only [EventGraphRuntime.environmentStep]
  change FinDist.map _ (FinDist.map _ (FinDist.map (fun _value : Bool => _) _)) = _
  simp only [FinDist.map_comp]
  change (FinDist.map (fun _ : Bool =>
    some ([((VegasTests.SourceSemantics.Player.alice), 10)] :
      List (VegasTests.SourceSemantics.Player × Int))) _) = _
  exact FinDist.map_const _ _

end

end VegasTests.EventMessages
