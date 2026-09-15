/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageService

/-! # Exact cursors for the shared service runner

Environment callbacks retain the whole actual history. Only the service-plan
index counts environment invocations; player invocations do not consume it.
These lemmas expose the next reserved command after a supported plan prefix.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type}

namespace ServiceInstruction

theorem environmentSlots_length (plan : List (ServiceInstruction Player)) :
    (plan.filterMap environmentSlot).length =
      (plan.map invocation).countP MessageApplication.Invocation.isEnvironment := by
  induction plan with
  | nil => rfl
  | cons instruction rest ih =>
      cases instruction <;>
        simpa [environmentSlot, invocation, MessageApplication.Invocation.isEnvironment] using ih

theorem environmentSlot_at (before suffix : List (ServiceInstruction Player))
    (instruction : ServiceInstruction Player)
    (isEnvironment : instruction.environmentSlot = some instruction) :
    ((before ++ instruction :: suffix).filterMap environmentSlot)[
      (before.filterMap environmentSlot).length]? = some instruction := by
  simp [List.filterMap_append, isEnvironment]

end ServiceInstruction

variable [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable {Δ : VCtx Player L}

/-- The next environment callback uses the exact current slot, even when
earlier player commands or wire choices advanced the application early. -/
theorem serviceEnvironment_at (runtime : GraphRuntime Player L Δ)
    (before suffix : List (ServiceInstruction Player)) (instruction : ServiceInstruction Player)
    (wire : runtime.application.WirePolicy) (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (isEnvironment : instruction.environmentSlot = some instruction)
    (cursor : history.length = (before.filterMap ServiceInstruction.environmentSlot).length) :
    runtime.serviceEnvironment (before ++ instruction :: suffix) wire history view =
      match instruction with
      | .wire => runtime.application.wireEnvironment wire history view
      | .includeLatest who =>
          FinDist.pure (runtime.application.latestSubmissionCommand who view)
      | .expire phase =>
          FinDist.pure (if view.application.pc = phase then .application .tick else .wait)
      | .player _ => FinDist.pure .wait := by
  unfold serviceEnvironment
  rw [cursor, ServiceInstruction.environmentSlot_at before suffix instruction isEnvironment]
  cases instruction <;> rfl

/-- A supported run of a service prefix advances its environment cursor by
exactly the number of environment instructions in that prefix. -/
theorem runPolicies_service_cursor (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (before : List (ServiceInstruction Player))
    (initial next : runtime.application.PolicyExecution)
    (supported : next ∈ (runtime.application.runPolicies players environment
      (before.map ServiceInstruction.invocation) initial).support) :
    next.environmentHistory.length = initial.environmentHistory.length +
      (before.filterMap ServiceInstruction.environmentSlot).length := by
  rw [ServiceInstruction.environmentSlots_length]
  exact runtime.application.runPolicies_environmentHistory_length
    players environment _ initial next supported

/-- Reserved and wire commands following an actually executed prefix are
selected without resetting any player's or the environment's history. -/
theorem serviceEnvironment_after_prefix (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (before suffix : List (ServiceInstruction Player)) (instruction : ServiceInstruction Player)
    (wire : runtime.application.WirePolicy)
    (initial next : runtime.application.PolicyExecution)
    (empty : initial.environmentHistory = [])
    (isEnvironment : instruction.environmentSlot = some instruction)
    (supported : next ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment (before ++ instruction :: suffix) wire)
      (before.map ServiceInstruction.invocation) initial).support) :
    runtime.serviceEnvironment (before ++ instruction :: suffix) wire next.environmentHistory
      (MessageApplication.State.environmentView runtime.application next.native) =
      match instruction with
      | .wire => runtime.application.wireEnvironment wire next.environmentHistory
          (MessageApplication.State.environmentView runtime.application next.native)
      | .includeLatest who => FinDist.pure (runtime.application.latestSubmissionCommand who
          (MessageApplication.State.environmentView runtime.application next.native))
      | .expire phase => FinDist.pure
          (if next.native.application.publicView.pc = phase then .application .tick else .wait)
      | .player _ => FinDist.pure .wait := by
  have cursor : next.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length := by
    simpa only [empty, List.length_nil, Nat.zero_add] using
      runtime.runPolicies_service_cursor players _ before initial next supported
  have law := runtime.serviceEnvironment_at before suffix instruction wire
    next.environmentHistory
    (MessageApplication.State.environmentView runtime.application next.native) isEnvironment cursor
  cases instruction <;> exact law

end Vegas.GraphRuntime
