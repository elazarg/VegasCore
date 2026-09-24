/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Pending.ReactivePolicyFacts

/-! # Reconstructing disclosure intentions from accepted packets

These tests concern recall reconstruction, not proper-root correspondence.
The fixture has an unopenable input: both disclosure intentions emit a
withholding packet, while internal compiler state distinguishes the choices.
-/

noncomputable section

namespace VegasTests.ReactiveRecovery

open GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

private abbrev order : EventOrder where
  eventCount := 1
  predecessors _ := ∅
  predecessor_lt := by simp

private abbrev inputs : Fin 1 → EventGraph.EventField Unit simpleExpr :=
  fun _ => .binding () .bool

private abbrev outputs : Fin 1 → EventGraph.EventField Unit simpleExpr :=
  fun _ => .publication .bool

private abbrev layout := EventGraph.fieldLayout inputs outputs

private abbrev binding : EventGraph.FieldRef layout (.binding () .bool) := ⟨.inl 0, rfl⟩

private abbrev graph : EventGraph Unit simpleExpr where
  inputCount := 1
  order := order
  inputLayout := inputs
  outputLayout := outputs
  nodes _ := EventGraph.EventCode.resolve (layout := layout) () .bool binding []
  reads_available := by
    intro event field member
    cases field with
    | inl => trivial
    | inr producer =>
        simp [EventGraph.EventCode.readFields, EventGraph.GuardCheck.listReadFields] at member
  payoffs := []

private def runtime : EventGraphRuntime graph where
  deadline _ := 2

private def leaks : MessageNetwork.ObservationRule Unit (Payload graph) :=
  fun _ _ => FinDist.pure ∅

private abbrev app := runtime.reactiveApplication leaks

private def initial : app.Execution :=
  ReactiveApplication.Execution.initial app
    (State.initial (graph := graph) (fun _ => .failure))

private def response (disclose : Bool) : app.Action :=
  runtime.reactiveDecision leaks () 0 disclose (initial.observe app ()).application

private def entry (serial : Nat) (disclose : Bool) : app.PlayerEntry :=
  ⟨initial.observe app (), response disclose, some ⟨((), serial), .withhold 0⟩⟩

/-- The game contains a single semantic response for these two intentions. -/
theorem failed_disclosure_same_action : response true = response false := rfl

/-- A remembered failed disclosure is restored when its packet was accepted. -/
theorem accepted_intention :
    runtime.reactiveOriginal leaks () [entry 0 true] [some ⟨0, true⟩] [(((), 0), true)] ⟨0, false⟩ =
      ⟨0, true⟩ := by
  simp [reactiveOriginal, nodeView, entry, response, reactiveDecision, Payload.event?]

/-- Sending an intention is insufficient: pending and rejected packets do
not override the actual graph completion. -/
theorem unaccepted_intention :
    runtime.reactiveOriginal leaks () [entry 0 true] [some ⟨0, true⟩]
      [(((), 0), false)] ⟨0, false⟩ =
      ⟨0, false⟩ := by
  simp [reactiveOriginal, nodeView]

/-- With competing submissions, the accepted identifier determines recall. -/
theorem competing_intentions :
    runtime.reactiveOriginal leaks () [entry 0 true, entry 1 false]
      [some ⟨0, true⟩, some ⟨0, false⟩] [(((), 1), true)] ⟨0, false⟩ = ⟨0, false⟩ := by
  simp [reactiveOriginal, nodeView, entry, response, reactiveDecision, Payload.event?]

private def openable : app.Execution :=
  ReactiveApplication.Execution.initial app
    (State.initial (graph := graph) (fun _ => .success true))

/-- With an openable input, a stale internal intention cannot explain an
accepted withholding packet: the claimed intention would have generated an opening instead. -/
theorem mismatched_intention :
    let forged : app.PlayerEntry :=
      ⟨openable.observe app (),
        ⟨some (.submit ⟨.withhold 0, none⟩)⟩,
        some ⟨((), 0), .withhold 0⟩⟩
    runtime.reactiveOriginal leaks () [forged] [some ⟨0, true⟩] [(((), 0), true)] ⟨0, false⟩ =
      ⟨0, false⟩ := by
  have expected : runtime.reactiveDecision leaks () 0 true
      (openable.observe app ()).application = ReactiveApplication.Action.mk (app := app)
        (some (.submit ⟨.opening 0 ((), .initial 0) ⟨.bool, true⟩, none⟩)) := rfl
  have different : (ReactiveApplication.Action.mk (app := app)
      (some (.submit ⟨.withhold 0, none⟩))) ≠
        runtime.reactiveDecision leaks () 0 true (openable.observe app ()).application := by
    rw [expected]
    intro same
    have sent := congrArg (fun action : app.Action => action.transmission) same
    have material := ReactiveApplication.Transmission.submit.inj (Option.some.inj sent)
    have packet := congrArg (fun submission : Submission graph => submission.packet) material
    cases packet
  simp [reactiveOriginal, nodeView, different]

end VegasTests.ReactiveRecovery
