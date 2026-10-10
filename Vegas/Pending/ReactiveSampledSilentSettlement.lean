/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDisclosureRealization
import Vegas.Pending.ReactiveDisclosureStability

/-! # Delayed expiry realizes the original silent resolution value -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A silent original resolution retains its semantic failure across arbitrary
native play. At actual due expiry the full typed store realizes the original
sampled action, including TRUE decisions rejected by deferred checks. -/
theorem reactiveDecision_silent_resolution_continuation_expiry_store
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution later : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (owner : Player) (event : graph.EventId)
    (readyBefore : execution.application.config.cut.Ready event)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (disclose : Bool)
    (silent : (runtime.reactiveDecision leaks owner event
      (cast (congrArg EventField.Action outputEq.symm) disclose)
      ((runtime.reactiveApplication leaks).observePlayer
        execution.application owner)).transmission =
        none)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy) (rounds : Nat)
    (reached : later ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players rounds
      (execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveDecision leaks owner event
          (cast (congrArg EventField.Action outputEq.symm) disclose)
          ((runtime.reactiveApplication leaks).observePlayer
            execution.application owner)))).support)
    (ready : later.application.config.cut.Ready event)
    (entered : Nat) (activated : later.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ later.application.clock - entered) :
    (environmentStep runtime later.application (.expire event)).map
        (fun after => after.config.store) =
      (later.application.config.step event ready
        (cast (congrArg EventField.Action outputEq.symm) disclose)).map Config.store := by
  have failed := runtime.reactiveDecision_silent_resolution_failure leaks execution.application
    valid owner event readyBefore payload binding checks outputEq codeEq node disclose silent
  have reads := resolution_readFields event owner payload binding checks outputEq codeEq
  have available : ∀ field ∈ insert binding.field (GuardCheck.listReadFields checks),
      (execution.application.config.store field).isSome = true := by
    intro field member
    exact execution.application.config.read_available readyBefore (reads.symm ▸ member)
  let action := runtime.reactiveDecision leaks owner event
    (cast (congrArg EventField.Action outputEq.symm) disclose)
    ((runtime.reactiveApplication leaks).observePlayer execution.application owner)
  have response := runtime.reactive_respond_application leaks execution owner action
  have initial : ∀ field ∈ insert binding.field (GuardCheck.listReadFields checks),
      (execution.respond (runtime.reactiveApplication leaks) owner action).application.config.store
          field = execution.application.config.store field ∧
        (execution.respond (runtime.reactiveApplication leaks) owner action).application.accepted
          field = execution.application.accepted field := by
    intro field _
    exact ⟨congrArg (fun config : graph.Config => config.store field) response.1,
      congrFun (congrArg PublicView.accepted response.2) field⟩
  have frame := (ReactiveApplication.Invariant.policyInvariant _
    (runtime.reactiveReadFrameInvariant leaks execution.application
      (insert binding.field (GuardCheck.listReadFields checks)) available) players).runRounds
        scheduler rounds (execution.respond (runtime.reactiveApplication leaks) owner action)
        later initial reached
  have stable := EventCode.resolveOutput?_congr binding checks disclose
    later.application.config.store execution.application.config.store
    (fun field member => (frame field member).1)
  have failedNow := stable.trans failed
  have law := later.application.config.step_eq_map_of_code event ready outputEq _ codeEq disclose
    (PMF.pure (PublicationResult.failure : PublicationResult (L.Val payload)))
    (by simp only [EventCode.eval?, failedNow, Option.map_some])
  rw [PMF.pure_map] at law
  rw [environmentStep_expire_resolve_eq runtime later.application event ready entered activated
      due owner payload binding checks outputEq codeEq node, law]
  simp only [PMF.pure_map]
  apply congrArg PMF.pure
  change (later.application.config.complete event ready _ _).store = _
  rw [store_complete, store_complete]

end Vegas.EventGraphRuntime
