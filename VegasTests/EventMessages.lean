module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphAssembly
public import Vegas.Pending.EventApplication
public import VegasTests.SourceSemantics

@[expose] public section

/-! # Native compiled-event message integration

The mixed source fixture is executed through native commitment and opening
handlers followed by the dependent chance command.
-/

namespace VegasTests.EventMessages

open GameTheory.Math.Probability Interaction Vegas

noncomputable section

abbrev TestPlayer := VegasTests.SourceSemantics.Player
abbrev graph := VegasTests.SourceSemantics.mixedSetup.eventGraph
abbrev inputs : graph.Inputs :=
  VegasTests.SourceSemantics.mixedSetup.eventInputs VegasTests.SourceSemantics.mixedState

def timeouts : EventTimeouts graph where
  duration _ := 10

def initial : EventGraphRuntime.State graph :=
  EventGraphRuntime.State.initial inputs

abbrev choiceEvent : graph.EventId := ⟨0, by decide⟩
abbrev choiceReveal : graph.EventId := ⟨1, by decide⟩
abbrev seedReveal : graph.EventId := ⟨2, by decide⟩
abbrev coinEvent : graph.EventId := ⟨3, by decide⟩

abbrev choiceHandle : EventGraphRuntime.Handle graph :=
  (.alice, .prepared 0)

abbrev seedHandle : EventGraphRuntime.Handle graph :=
  (.alice, .initial ⟨0, by decide⟩)

def choiceRaw (value : Option Bool) : EventGraphRuntime.Raw simpleExpr :=
  ⟨.option .bool, value⟩

def seedRaw : EventGraphRuntime.Raw simpleExpr := ⟨.bool, true⟩

def prepared : EventGraphRuntime.State graph :=
  EventGraphRuntime.privateStep initial .alice
    (.prepare 0 (choiceRaw none))

def commitment : Message TestPlayer (EventGraphRuntime.Payload graph) :=
  ⟨(.alice, 0), .commitment choiceEvent choiceHandle⟩

theorem choiceReady : prepared.config.cut.Ready choiceEvent := by
  change (EventOrder.Cut.empty graph.order).Ready choiceEvent
  decide

private theorem choiceTimely : prepared.WithinDeadline timeouts choiceEvent := by
  change 0 < 10
  decide

private theorem choiceUnused : prepared.HandleUnused choiceHandle := by
  intro field accepted
  change (EventGraphRuntime.State.initial inputs).accepted field =
      some choiceHandle at accepted
  obtain ⟨input, owner, payload, _field, _layout, handle⟩ :=
    EventGraphRuntime.State.initial_accepted_eq_some
      inputs field choiceHandle accepted
  cases handle

private theorem preparedResult :
    prepared.bindingResult choiceHandle (.option .bool) = .success none := by
  rfl

def bound : EventGraphRuntime.State graph :=
  { (prepared.complete choiceEvent choiceReady (some (.success none)) (.success none)) with
    accepted := Function.update prepared.accepted (.inr choiceEvent) (some choiceHandle)
    candidates := prepared.candidates.freeze choiceHandle }

private theorem handle_commitment :
    EventGraphRuntime.handle timeouts prepared commitment = some bound := by
  unfold commitment
  rw [EventGraphRuntime.handle_commitment_eq timeouts prepared (.alice, 0) choiceEvent
    choiceHandle .alice (.option .bool) rfl rfl rfl choiceReady choiceTimely
    (by change .alice ∉ (∅ : Finset TestPlayer); simp) rfl rfl rfl
    choiceUnused]
  simp [bound, preparedResult]

def choiceOpening : Message TestPlayer (EventGraphRuntime.Payload graph) :=
  ⟨(.alice, 1), .opening choiceReveal choiceHandle (choiceRaw none)⟩

def seedOpening : Message TestPlayer (EventGraphRuntime.Payload graph) :=
  ⟨(.alice, 2), .opening seedReveal seedHandle seedRaw⟩

theorem choiceRevealReady : bound.config.cut.Ready choiceReveal := by
  unfold bound prepared initial
  decide

private theorem choiceRevealTimely : bound.WithinDeadline timeouts choiceReveal := by
  change 0 < 10
  decide

def choiceOpened : EventGraphRuntime.State graph :=
  bound.complete choiceReveal choiceRevealReady true (.success none)

private theorem handle_choice_opening :
    EventGraphRuntime.handle timeouts bound choiceOpening = some choiceOpened := by
  unfold choiceOpening choiceRaw
  rw [EventGraphRuntime.handle_opening_eq timeouts bound (.alice, 1) choiceReveal
    choiceHandle .alice (.option .bool) _ _ rfl rfl rfl choiceRevealReady
    choiceRevealTimely (by change .alice ∉ (∅ : Finset TestPlayer); simp)
    rfl rfl rfl none rfl rfl (.success none) rfl]
  rfl

theorem seedRevealReady : choiceOpened.config.cut.Ready seedReveal := by
  unfold choiceOpened bound prepared initial
  decide

private theorem seedRevealTimely : choiceOpened.WithinDeadline timeouts seedReveal := by
  change 0 < 10
  decide

def seedOpened : EventGraphRuntime.State graph :=
  choiceOpened.complete seedReveal seedRevealReady true (.success true)

private theorem handle_seed_opening :
    EventGraphRuntime.handle timeouts choiceOpened seedOpening = some seedOpened := by
  unfold seedOpening seedRaw
  rw [EventGraphRuntime.handle_opening_eq timeouts choiceOpened (.alice, 2) seedReveal
    seedHandle .alice .bool _ _ rfl rfl rfl seedRevealReady seedRevealTimely
    (by change .alice ∉ (∅ : Finset TestPlayer); simp)
    rfl rfl rfl true rfl rfl (.success true) rfl]
  rfl

def settled? : Option (EventGraphRuntime.State graph) := do
  let afterChoice ← EventGraphRuntime.handle timeouts prepared commitment
  let afterChoiceOpening ← EventGraphRuntime.handle timeouts afterChoice choiceOpening
  EventGraphRuntime.handle timeouts afterChoiceOpening seedOpening

private theorem settled_eq : settled? = some seedOpened := by
  unfold settled?
  rw [handle_commitment]
  change (do
    let afterChoiceOpening ← EventGraphRuntime.handle timeouts bound choiceOpening
    EventGraphRuntime.handle timeouts afterChoiceOpening seedOpening) = some seedOpened
  rw [handle_choice_opening]
  exact handle_seed_opening

def successfulRun : PMF (EventGraphRuntime.State graph) :=
  match settled? with
  | none => PMF.pure prepared
  | some settled => EventGraphRuntime.environmentStep timeouts settled (.executeSample coinEvent)

def payout? (state : EventGraphRuntime.State graph) :
    Option (List (TestPlayer × Int)) :=
  if terminal : state.config.cut.Terminal then
    some (state.config.terminalPayoffs terminal)
  else none

/-- Native commitment and opening handlers followed by the chance command
reach the compiled terminal graph and retain the source program's successful
payoff. The fair coin is sampled once, but it does not affect this branch. -/
example :
    successfulRun.map payout? =
      PMF.pure (some [(.alice, 10)]) := by
  unfold successfulRun
  rw [settled_eq]
  simp only [EventGraphRuntime.environmentStep]
  change PMF.map _ (PMF.map _ (PMF.map (fun _value : Bool => _) _)) = _
  simp only [PMF.map_comp]
  change (PMF.map (fun _ : Bool =>
    some ([((VegasTests.SourceSemantics.Player.alice), 10)] :
      List (VegasTests.SourceSemantics.Player × Int))) _) = _
  exact PMF.map_const _ _

end

end VegasTests.EventMessages
