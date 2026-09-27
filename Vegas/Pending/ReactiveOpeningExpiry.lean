/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOpeningSettlement
import Vegas.Pending.ReactiveRevealSettlement

/-! # Source revelation outcomes after an opening window and expiry

This is the existing roster, inclusion, tick and expiry interpreter. The
selected opening completes at inclusion; the never-opening branch completes
at the deadline. Actual pending copies and private observations are retained.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem openingWindow_expiry (runtime : EventGraphRuntime graph)
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
    (roster : List Player) (selected : Option (Fin (roster.count owner)))
    (network : runtime.NetworkPolicy leaks)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks
      (runtime.openingWindowPlayers leaks owner event candidate ⟨payload, value⟩
        (initial.recall owner).length selected) network
      ((roster.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        List.replicate ticks .tick ++ [.expire event]) initial).support) :
    final.application = (if selected.isSome then
      { initial.application.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) true)
          (cast (congrArg EventField.Value outputEq.symm) (PublicationResult.success value)) with
        clock := initial.application.clock + ticks }
      else ({ initial.application with clock := initial.application.clock + ticks } : State graph)
        |>.complete event ready (cast (congrArg EventField.Action outputEq.symm) false)
          (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure)) ∧
    final.network.Satisfies (fun message => message.id ∈ final.network.ledger.map Message.id) := by
  let players := runtime.openingWindowPlayers leaks owner event candidate ⟨payload, value⟩
    (initial.recall owner).length selected
  rw [List.append_assoc, runtime.runInteractionPlan_append] at reached
  obtain ⟨middle, prior, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  obtain ⟨application, clean⟩ := runtime.openingWindow_settlement leaks owner event candidate
    ⟨payload, value⟩ roster selected initial serials published owned (fun _ => valid)
      network middle prior
  cases selected with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at application ⊢
      have stillReady : middle.application.config.cut.Ready event := application ▸ ready
      obtain ⟨next, law, state, messages, _, _⟩ := runtime.canonical_silent_expiry leaks players
        network middle owner event payload binding checks outputEq codeEq node stillReady entered
          ticks (application ▸ activated) (application ▸ due)
      rw [law] at reached
      cases FinDist.mem_support_pure.mp reached
      refine ⟨?_, ?_⟩
      · simpa only [application] using state
      · simpa only [messages] using clean
  | some slot =>
      simp only [Option.isSome_some, ↓reduceIte, accepted, Option.getD_some] at application ⊢
      have settled : ¬middle.application.config.cut.Ready event := by
        rw [application]
        intro unfinished
        exact unfinished.1 (by simp [State.complete, EventOrder.Cut.complete])
      obtain ⟨next, law, state, messages, _, _⟩ := runtime.settled_reveal_expiry leaks players
        network middle event settled ticks
      rw [law] at reached
      cases FinDist.mem_support_pure.mp reached
      refine ⟨?_, ?_⟩
      · simpa only [application, State.complete] using state
      · simpa only [messages] using clean

end Vegas.EventGraphRuntime
