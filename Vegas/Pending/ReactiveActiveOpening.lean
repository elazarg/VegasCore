/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOpeningExpiry

/-! # Opening completion from an already observed response opportunity

The current activation has already sampled pending traffic. An unpassed
scheduled opening and the remaining response roster use the existing window
invariant, followed by protected inclusion and deadline settlement.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A clean window may start at any unsent opportunity before its selected
response. No earlier private computation is represented by this invariant. -/
theorem OpeningWindowFrame.initial_at (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (visits : Nat)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (counted : (initial.recall owner).length = offset + visits)
    (unpassed : openingPassed selected visits = false)
    (serials : initial.network.SerialsBeforeNext)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id) :
    runtime.OpeningWindowFrame leaks owner event candidate raw offset selected visits
      initial initial where
  application := rfl
  ledger := rfl
  receipts := rfl
  count := counted
  counters := by simp only [unpassed, Bool.false_eq_true, and_false, ↓reduceIte, Nat.add_zero]
  serials := serials
  packets := published.mono fun _ member => Or.inl member
  opened := by simp only [unpassed, Bool.false_eq_true, false_implies]

/-- Invoke the current owner response exactly once, then run all remaining
opportunities and the actual inclusion/tick/expiry service. A selected future
opening succeeds; selecting no opening produces the ordinary deadline result. -/
theorem openingWindow_active_expiry (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle graph) (value : L.Val payload)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (ready : initial.application.config.cut.Ready event)
    (serials : initial.network.SerialsBeforeNext)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (owned : candidate.1 = owner)
    (valid : initial.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (accepted : (runtime.reactiveApplication leaks).handle initial.application
      (runtime.windowEnvelope leaks owner event candidate ⟨payload, value⟩ initial) =
        some (initial.application.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) true)
          (cast (congrArg EventField.Value outputEq.symm) (PublicationResult.success value))))
    (entered ticks : Nat) (activated : initial.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ initial.application.clock + ticks - entered)
    (offset visits : Nat) {slots : Nat} (selected : Option (Fin slots))
    (counted : (initial.recall owner).length = offset + visits)
    (unpassed : openingPassed selected visits = false)
    (remaining : List Player) (complete : visits + 1 + remaining.count owner = slots)
    (network : runtime.NetworkPolicy leaks)
    (final : (runtime.reactiveApplication leaks).Execution) :
    let app := runtime.reactiveApplication leaks
    let players := runtime.openingWindowPlayers leaks owner event candidate ⟨payload, value⟩
      offset selected
    final ∈ ((app.invoke players owner initial).bind
      (runtime.runInteractionPlan leaks players network
        (remaining.map ServiceInstruction.player ++
          (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])))).support →
    final.application = (if selected.isSome then
      { initial.application.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) true)
          (cast (congrArg EventField.Value outputEq.symm) (PublicationResult.success value)) with
        clock := initial.application.clock + ticks }
      else ({ initial.application with clock := initial.application.clock + ticks } : State graph)
        |>.complete event ready (cast (congrArg EventField.Action outputEq.symm) false)
          (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure)) := by
  intro app players reached
  have start := OpeningWindowFrame.initial_at runtime leaks owner event candidate ⟨payload, value⟩
    offset selected visits initial counted unpassed serials published
  simp only [ReactiveApplication.invoke, PMF.bind_map, PMF.support_bind,
      Function.comp_def] at reached
  obtain ⟨response, chosen, reached⟩ := Set.mem_iUnion₂.mp reached
  rw [runtime.runInteractionPlan_append, PMF.support_bind] at reached
  obtain ⟨current, prior, reached⟩ := Set.mem_iUnion₂.mp reached
  have responded := start.response runtime leaks owner event candidate ⟨payload, value⟩
    offset selected visits initial initial owner response chosen owned (fun _ => valid)
  simp only [↓reduceIte] at responded
  have frame := responded.run runtime leaks owner event candidate ⟨payload, value⟩
    offset selected (visits + 1) initial (initial.respond app owner response)
      network remaining current prior owned (fun _ => valid)
  rw [complete] at frame
  exact (frame.expiry runtime leaks owner event payload binding checks outputEq codeEq node
    candidate value initial current offset selected ready serials accepted entered ticks activated
      due players network final reached).1

end Vegas.EventGraphRuntime
