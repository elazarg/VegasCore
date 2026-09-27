/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceState
import Vegas.Pending.ReactiveOpeningExpiry

/-! # Typed source revelation through an arbitrary activation roster

The current owner chooses one opening opportunity or withholds. Other players
may read and replay the pending envelope before protected inclusion. The full
block, including deadline expiry, advances the actual source store and decoded
source action history. Native response and observation memories remain intact.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_reveal_source_step (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (source : Config Player L Γ) (empty : source.registry = [])
    (refs : ContextRefs (graph setup).layout Γ)
    (initial : (application setup leaks).Execution)
    (agree : refs.Agrees source.state initial.application.config.store)
    (history : decodeHistory setup.program
      (initial.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding) [])
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get binding) [] outputEq codeEq)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (decoded : ∀ disclose, decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
        some (.reveal owner name disclose))
    (value : L.Val payload) (bound : source.state.get binding = .success value)
    (candidate : Handle (graph setup)) (owned : candidate.1 = owner)
    (associated : initial.application.accepted (refs.get binding).field = some candidate)
    (valid : initial.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (ready : initial.application.config.cut.Ready event)
    (timely : initial.application.WithinDeadline (runtime setup) event)
    (entered ticks : Nat) (activated : initial.application.activatedAt event = some entered)
    (due : (runtime setup).deadline event ≤ initial.application.clock + ticks - entered)
    (clean : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (serials : initial.network.SerialsBeforeNext)
    (roster : List Player) (selected : Option (Fin (roster.count owner)))
    (network : (runtime setup).NetworkPolicy leaks)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      ((runtime setup).openingWindowPlayers leaks owner event candidate ⟨payload, value⟩
        (initial.recall owner).length selected) network
      ((roster.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        List.replicate ticks .tick ++ [.expire event]) initial).support) :
    (refs.cons (name := published) ⟨.inr event, outputEq⟩).Agrees
      (revealSuccessor published binding source selected.isSome).state
        final.application.config.store ∧
    decodeHistory setup.program
      (final.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) =
      (revealSuccessor published binding source selected.isSome).history ∧
    final.network.Satisfies (fun message => message.id ∈ final.network.ledger.map Message.id) := by
  have stored : (refs.get binding).get? initial.application.config.store =
      some (.success value) := by
    simpa only [bound, cellValue] using agree binding
  have resolved : EventGraph.EventCode.resolveOutput? (refs.get binding) [] true
      initial.application.config.store = some (.success value) := by
    simp only [EventGraph.EventCode.resolveOutput?, stored,
      EventGraph.GuardCheck.allAccepted?, ↓reduceIte]
    rfl
  have accepted : (application setup leaks).handle initial.application
      ((runtime setup).windowEnvelope leaks owner event candidate ⟨payload, value⟩ initial) =
        some (initial.application.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (PublicationResult.success value))) :=
    handle_opening_eq (runtime setup) initial.application _ event candidate owner payload
      (refs.get binding) [] outputEq codeEq node ready timely rfl owned associated
      value valid stored (.success value) resolved
  obtain ⟨state, publishedPackets⟩ := (runtime setup).openingWindow_expiry leaks owner event payload
    (refs.get binding) [] outputEq codeEq node candidate value initial ready serials clean owned
      valid accepted entered ticks activated due roster selected network final reached
  refine ⟨?_, ?_, publishedPackets⟩
  · have stores : (refs.cons (name := published) ⟨.inr event, outputEq⟩).Agrees
        (revealSuccessor published binding source selected.isSome).state
        (initial.application.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) selected.isSome)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (if selected.isSome then source.state.get binding
              else PublicationResult.failure))).config.store :=
      complete_reveal_agrees published binding source empty refs initial.application
        agree event ready outputEq before selected.isSome
    simp only [bound] at stores
    rw [state]
    cases selected <;> simp only [Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte] at stores ⊢ <;> exact @stores
  · have histories := complete_reveal_history setup published binding source initial.application
      history event ready (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        selected.isSome)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (if selected.isSome then PublicationResult.success value else .failure))
      selected.isSome (decoded _)
    rw [state]
    cases selected <;> simp only [Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte] at histories ⊢ <;> exact histories

end Vegas.SourceProgram.RevealService
