/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterSupport
import Vegas.Game.RevealServiceRosterBlock

/-! # Source completion under arbitrary permitted roster policies

Every retained continuation, including off-path play, completes exactly one
source reveal or withholding. The selected opening time is extracted from
actual response recall. Public records are independent of that time and of
passive observations and replay choices.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_menu_reveal_source_step (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
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
    (granted : initial.application.serviceGrant = some event)
    (ownedEvent : (graph setup).actor? event = some owner)
    (opening : rosterOpening? setup leaks owner event
      (initial.observe (application setup leaks) owner) = some (candidate, ⟨payload, value⟩))
    (offset : (initial.recall owner).length = rosterOffset setup rosters owner event)
    (entered ticks : Nat) (activated : initial.application.activatedAt event = some entered)
    (due : (runtime setup).deadline event ≤ initial.application.clock + ticks - entered)
    (clean : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (serials : initial.network.SerialsBeforeNext)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ rosterActions setup leaks bounds rosters who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        List.replicate ticks .tick ++ [.expire event]) initial).support) :
    ∃ selected : Option (Fin ((rosters event).count owner)),
      (refs.cons (name := published) ⟨.inr event, outputEq⟩).Agrees
        (revealSuccessor published binding source selected.isSome).state
          final.application.config.store ∧
      decodeHistory setup.program
        (final.application.config.history.map
          (setup.eventGraph.fromModeCompletion .sequential)) =
        (revealSuccessor published binding source selected.isSome).history ∧
      final.application = (if selected.isSome then
        { initial.application.complete event ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm)
              (PublicationResult.success value)) with clock := initial.application.clock + ticks }
        else ({ initial.application with clock := initial.application.clock + ticks } :
          EventGraphRuntime.State (graph setup)).complete event ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm) PublicationResult.failure)) ∧
      final.network.Satisfies (fun message => message.id ∈ final.network.ledger.map Message.id) ∧
      final.network.ledger = (if selected.isSome then List.append initial.network.ledger
        [(runtime setup).windowEnvelope leaks owner event candidate ⟨payload, value⟩ initial]
        else initial.network.ledger) ∧
      final.receipts = (if selected.isSome then initial.receipts ++
        [((owner, initial.network.nextSerial owner), true)] else initial.receipts) ∧
      final.network.nextSerial = fun who => initial.network.nextSerial who +
        if who = owner ∧ selected.isSome then 1 else 0 := by
  rw [List.append_assoc, List.append_assoc, (runtime setup).runInteractionPlan_append] at reached
  obtain ⟨current, prior, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  obtain ⟨selected, frame, _, _⟩ := roster_window_support setup leaks bounds rosters
    initial event owner granted ownedEvent candidate ⟨payload, value⟩ opening owned valid
      offset serials clean players covered network (rosters event) (Nat.le_refl _) current prior
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
  obtain ⟨state, publishedPackets, ledger, receipts, counters⟩ := frame.expiry (runtime setup)
    leaks owner event payload (refs.get binding) [] outputEq codeEq node candidate value
      initial current (rosterOffset setup rosters owner event) selected ready serials accepted
        entered ticks activated due players network final reached
  refine ⟨selected, ?_, ?_, state, publishedPackets, ledger, receipts, counters⟩
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

end Vegas
