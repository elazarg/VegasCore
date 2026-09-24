/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicy
import Vegas.Pending.ReactiveSafety
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactivePolicyInvariant

/-! # Compiled bindings across arbitrary intervening interaction

A compiled response fixes its selected binding before the envelope becomes
observable. Arbitrary later responses, passive leaks, inclusions and application
commands preserve that meaning. If the original packet is eventually included
at an admissible opportunity, it performs exactly that graph action.

The theorem does not coalesce submission with inclusion. Nor does it guarantee
which packet is selected, or that an admissible opportunity remains available.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveDecision_binding_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (action : graph.Action event) (view : ReactivePlayerView graph) (serial : Nat)
    (allocated : reactiveFreshSlot view = some serial) :
    runtime.reactiveDecision leaks who event action view =
      runtime.reactiveBinding leaks who event payload
        (cast (congrArg EventField.Action outputEq) action) serial := by
  simp only [reactiveDecision, node, allocated, Option.map_some, reactiveBinding]
  rfl

/-- This includes continuations in which the owner submits competing candidates,
other players react to partial leaks, and earlier inclusions are rejected. -/
theorem reactiveBinding_continuation_result (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy) (rounds : Nat)
    (reached : next ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players rounds
      (execution.respond (runtime.reactiveApplication leaks) who
        (runtime.reactiveBinding leaks who event payload result serial))).support) :
    next.application.bindingResult (who, .prepared serial) payload = result := by
  let app := runtime.reactiveApplication leaks
  let submitted := execution.respond app who
    (runtime.reactiveBinding leaks who event payload result serial)
  let candidate : Handle graph := (who, .prepared serial)
  have fixed : submitted.application.candidates.lookup candidate ≠ .fresh := by
    change (submitStep _ who (.commitment event candidate)).candidates.lookup candidate ≠ .fresh
    exact submitStep_commitment_fixed _ who event (.prepared serial)
  have invariant : app.Invariant (fun state =>
      state.candidates.lookup candidate = submitted.application.candidates.lookup candidate) := by
    constructor
    · intro state actor material same
      exact (runtime.reactive_respond_candidate_fixed leaks (.initial app state) actor
        ⟨some (.submit material)⟩ candidate (by
          change state.candidates.lookup candidate ≠ .fresh
          rwa [same])).trans same
    · intro state message target same accepted
      exact (handle_lookup_of_not_fresh runtime state target message candidate
        (by rwa [same]) accepted).trans same
    · intro state command target same supported
      rw [(environmentStep_tables runtime state target command supported).2]
      exact same
  have stable := (ReactiveApplication.Invariant.policyInvariant app invariant players).runRounds
    scheduler rounds submitted next rfl reached
  change next.application.candidates.lookup candidate =
    submitted.application.candidates.lookup candidate at stable
  have meaning := runtime.reactiveBinding_result leaks who event payload result serial
    execution fresh
  change submitted.application.bindingResult candidate payload = result at meaning
  rw [State.bindingResult, stable]
  exact meaning

/-- Conditional realization at the actual inclusion state. Readiness, the
deadline and handle availability are checked there, after the intervening play.
The conclusion retains the exact semantic action and its completion history. -/
theorem reactiveBinding_continuation_include (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (result : PublicationResult (L.Val payload)) (serial nonce : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (fresh : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy) (rounds : Nat)
    (reached : next ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players rounds
      (execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveBinding leaks owner event payload result serial))).support)
    (pending : next.network.lookup (owner, nonce) =
      some ⟨(owner, nonce), .commitment event (owner, .prepared serial)⟩)
    (ready : next.application.config.cut.Ready event)
    (timely : next.application.WithinDeadline runtime event)
    (vacant : next.application.accepted (.inr event) = none)
    (unused : next.application.HandleUnused (owner, .prepared serial)) :
    (next.includePending (runtime.reactiveApplication leaks) (owner, nonce)).application.config =
      next.application.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) result)
        (cast (congrArg EventField.Value outputEq.symm) result) ∧
    (next.includePending (runtime.reactiveApplication leaks) (owner, nonce)).receipts =
      next.receipts ++ [((owner, nonce), true)] := by
  have meaning := runtime.reactiveBinding_continuation_result leaks owner event payload result
    serial execution next fresh scheduler players rounds reached
  have accepted := runtime.handle_commitment_eq next.application (owner, nonce) event
    (owner, .prepared serial) owner payload outputEq codeEq node ready timely rfl rfl vacant unused
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending, pending]
  change _ ∧ _
  dsimp only [reactiveApplication]
  rw [accepted]
  simp only [Option.getD_some, State.complete, meaning, Option.isSome_some]
  exact ⟨trivial, trivial⟩

/-- The actual compiler, rather than a separately chosen binding submission,
realizes its sampled graph action at a later admissible inclusion. No restriction
is imposed on intermediate policies or on the passive observation kernel. -/
theorem reactiveDecision_binding_continuation_step (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (action : graph.Action event) (serial : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (allocated : reactiveFreshSlot
      ((runtime.reactiveApplication leaks).observePlayer execution.application owner) = some serial)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy) (rounds : Nat)
    (reached : next ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players rounds
      (execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveDecision leaks owner event action
          ((runtime.reactiveApplication leaks).observePlayer
            execution.application owner)))).support)
    (pending : next.network.lookup (owner, execution.network.nextSerial owner) =
      some ⟨(owner, execution.network.nextSerial owner),
        .commitment event (owner, .prepared serial)⟩)
    (ready : next.application.config.cut.Ready event)
    (timely : next.application.WithinDeadline runtime event)
    (vacant : next.application.accepted (.inr event) = none)
    (unused : next.application.HandleUnused (owner, .prepared serial)) :
    FinDist.pure ((next.includePending (runtime.reactiveApplication leaks)
      (owner, execution.network.nextSerial owner)).application.config) =
        next.application.config.step event ready action ∧
    (next.includePending (runtime.reactiveApplication leaks)
      (owner, execution.network.nextSerial owner)).receipts =
        next.receipts ++ [((owner, execution.network.nextSerial owner), true)] := by
  have fresh := reactiveFreshSlot_spec
    ((runtime.reactiveApplication leaks).observePlayer execution.application owner) serial allocated
  rw [runtime.reactiveDecision_binding_eq leaks owner owner event payload outputEq codeEq
    node action _ serial allocated] at reached
  obtain ⟨included, receipt⟩ := runtime.reactiveBinding_continuation_include leaks owner event
    payload outputEq codeEq node (cast (congrArg EventField.Action outputEq) action)
    serial (execution.network.nextSerial owner) execution next fresh scheduler players rounds
    reached pending ready timely vacant unused
  refine ⟨?_, receipt⟩
  rw [included]
  symm
  have law := next.application.config.step_eq_map_of_code event ready outputEq _ codeEq
    (cast (congrArg EventField.Action outputEq) action)
    (FinDist.pure (cast (congrArg EventField.Action outputEq) action)) rfl
  simpa only [FinDist.map_pure, cast_cast, cast_eq] using law

end Vegas.EventGraphRuntime
