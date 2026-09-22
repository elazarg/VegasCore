/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Pending.EventService
import Vegas.Pending.EventPolicies

/-! # Native continuation recovery

A rejected, event-addressed submission makes the prescribed policy stop
submitting at that event, although a valid opening is still available. This
checks the operational obstruction to extending initial-play correctness to
arbitrary native continuations. It does not identify native subgame roots.
-/

namespace VegasTests.ContinuationRecovery

open GameTheory.Math.Probability Interaction Vegas
open Vegas.EventGraphRuntime

noncomputable section

private abbrev order : EventOrder where
  eventCount := 1
  predecessors _ := ∅
  predecessor_lt := by simp

private abbrev inputs : Fin 1 → EventGraph.EventField Unit simpleExpr :=
  fun _ => .binding () .bool

private abbrev outputs : Fin 1 → EventGraph.EventField Unit simpleExpr :=
  fun _ => .publication .bool

private abbrev layout := EventGraph.fieldLayout inputs outputs

private abbrev binding : EventGraph.FieldRef layout (.binding () .bool) :=
  ⟨.inl 0, rfl⟩

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

private def initial : State graph :=
  { State.initial (graph := graph) (fun _ => .success true) with
    serviceGrant := some 0 }

private def initialExecution : runtime.application.PolicyExecution :=
  MessageApplication.PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application initial)

private def badPacket : Payload graph := .commitment 0 ((), .initial 0)

private def opening : Payload graph := .opening 0 ((), .initial 0) ⟨.bool, true⟩

private def afterBadSubmission : runtime.application.PolicyExecution :=
  runtime.application.afterSubmit initialExecution () badPacket

private def disclose : graph.BehavioralPolicy () :=
  fun _ _ _ => FinDist.pure true

/-- The wrong packet is genuinely rejected by the application. -/
theorem badPacket_rejected :
    handle runtime initial ⟨((), 0), badPacket⟩ = none := by
  simp [handle, badPacket, nodeView]

/-- This state follows one legal player invocation; it is not fabricated cache
corruption. The invocation can be the first of the three owner opportunities. -/
theorem badSubmission_playerStep :
    runtime.application.playerStep () initialExecution (.submit badPacket) =
      FinDist.pure afterBadSubmission := by
  exact runtime.application.playerStep_submit_eq initialExecution () badPacket

/-- Resuming the compiled policy waits, regardless of the still-open deadline. -/
theorem compiled_waits_after_badSubmission :
    runtime.compilePlayerPolicy () disclose
        (afterBadSubmission.principalHistory ())
        (MessageApplication.State.observe runtime.application
          afterBadSubmission.native ()) = FinDist.pure .wait := by
  simp [compilePlayerPolicy, submittedAt, afterBadSubmission,
    MessageApplication.afterSubmit, initialExecution,
    MessageApplication.PolicyExecution.initial, badPacket, Payload.event?,
    MessageApplication.State.observe, MessageApplication.State.initial,
    application, submitStep, State.playerView, State.publicView, initial]

/-- A replacement can still publish the original binding successfully. -/
theorem opening_still_succeeds :
    (handle runtime afterBadSubmission.native.application
      ⟨((), 1), opening⟩).map (fun state => state.config.outputs 0) =
      some (some (.success true)) := by
  change (handle runtime initial ⟨((), 1), opening⟩).map
    (fun state => state.config.outputs 0) = some (some (.success true))
  have ready : initial.config.cut.Ready 0 := by
    change (EventOrder.Cut.empty order).Ready 0
    decide
  have timely : initial.WithinDeadline runtime 0 := by
    change 0 < 2
    decide
  rw [opening, handle_opening_eq runtime initial ((), 1) 0 ((), .initial 0)
    () .bool binding [] rfl rfl rfl ready timely rfl rfl rfl true rfl rfl
    (.success true) rfl]
  rfl

end

end VegasTests.ContinuationRecovery
