/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceActions
import Vegas.Game.RevealServiceState
import Vegas.Pending.ReactiveRevealResponse

/-! # Actual restricted responses complete source revelation steps

The service suffix is executed by the existing native interpreter. Every
ordinary response resolves the current source choice, including every published
replay alias of withholding. The exact application equation retains completion
times, and the network equation retains the physical response and its receipt.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Each allowed physical response runs the full inclusion, monitoring, and
expiry suffix, with the source Boolean branch and its actual completion time. -/
theorem ordinary_response_settlement (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (players : Player → (application setup leaks).Policy) (watcher : Player)
    (policy : players watcher = (application setup leaks).silentPolicy)
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (selected : HasVar Γ name (.commitment owner payload))
    (source : State L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source execution.application.config.store)
    (valid : execution.application.BindingInvariant)
    (event : (graph setup).EventId)
    (ownedEvent : (graph setup).actor? event = some owner)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [])
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get selected) [] outputEq codeEq)
    (value : L.Val payload) (bound : source.get selected = .success value)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (entered ticks : Nat) (activated : execution.application.activatedAt event = some entered)
    (due : (runtime setup).deadline event ≤ execution.application.clock + ticks - entered)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (response : (application setup leaks).Action)
    (member : response ∈ ordinaryActions setup leaks bounds owner (execution.recall owner)
      (execution.observe (application setup leaks) owner)) :
    let app := application setup leaks
    let disclose := sourceChoice setup leaks response
    let submitted := execution.respond app owner response
    let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose
    let result := cast (congrArg EventGraph.EventField.Value outputEq.symm)
      (if disclose then PublicationResult.success value else .failure)
    ∃ next, (runtime setup).runInteractionPlan leaks players
        ((runtime setup).idleNetwork leaks)
        ([.includeLatest event owner, .player watcher, .wire] ++
          List.replicate ticks .tick ++ [.expire event]) submitted = PMF.pure next ∧
      next.application =
        (if disclose then
          { execution.application.complete event ready action result with
            clock := execution.application.clock + ticks }
        else
          (({ execution.application with clock := execution.application.clock + ticks } :
            EventGraphRuntime.State (graph setup)).complete event ready action result).markMissed
              event) ∧
      next.network = (if disclose then
        (submitted.network.includePending (owner, execution.network.nextSerial owner)).2
        else submitted.network) ∧
      next.receipts = (if disclose then execution.receipts ++
        [((owner, execution.network.nextSerial owner), true)] else execution.receipts) ∧
      ∀ observer, observer ≠ watcher → next.recall observer = submitted.recall observer := by
  dsimp only
  cases chosen : sourceChoice setup leaks response with
  | false =>
      obtain refuses := (ordinary_false_iff setup leaks bounds owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) response member).mp chosen
      obtain ⟨next, law, applicationEq, networkEq, receiptsEq, recallEq⟩ :=
        (runtime setup).refusing_response_settlement leaks players watcher policy execution
          pending owner event payload (refs.get selected) [] outputEq codeEq
          node ready entered ticks activated due response refuses
      refine ⟨next, law, ?_, ?_, ?_, ?_⟩
      · simpa only [chosen, Bool.false_eq_true, ↓reduceIte] using applicationEq
      · simpa only [chosen, Bool.false_eq_true, ↓reduceIte] using networkEq
      · simpa only [chosen, Bool.false_eq_true, ↓reduceIte] using receiptsEq
      · intro observer different
        rw [recallEq]
        exact (application setup leaks).respond_recall_other _ watcher observer different _
  | true =>
      obtain ⟨candidate, associated, owned, verified, opening⟩ :=
        opening_at_checkpoint setup leaks selected source refs execution agree valid event
          ownedEvent outputEq codeEq node
          (ownTurn?_of_ready setup execution.application ready ownedEvent) value bound
      have same := (ordinary_true_iff setup leaks bounds owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) _ opening response member).mp chosen
      obtain ⟨evidence, shape⟩ := (runtime setup).normalized_reveal_response leaks owner
        (execution.recall owner) (execution.observe (application setup leaks) owner)
        event candidate ⟨payload, value⟩
      have responseEq := same.trans shape
      have stored : (refs.get selected).get? execution.application.config.store =
          some (.success value) := by
        simpa only [bound, cellValue] using agree selected
      have resolved : EventGraph.EventCode.resolveOutput? (refs.get selected) [] true
          execution.application.config.store = some (.success value) := by
        simp only [EventGraph.EventCode.resolveOutput?, stored,
          EventGraph.GuardCheck.allAccepted?, ↓reduceIte]
        rfl
      let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) true
      let result := cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (PublicationResult.success value)
      let after := execution.application.complete event ready action result
      have accepted : (runtime setup).handle execution.application
          ⟨(owner, execution.network.nextSerial owner),
            .opening event candidate ⟨payload, value⟩⟩ = some after :=
        handle_opening_eq (runtime setup) execution.application _ event candidate owner payload
          (refs.get selected) [] outputEq codeEq node ready timely rfl owned associated
          value verified stored (.success value) resolved
      have settled : ¬after.config.cut.Ready event := by
        intro stillReady
        exact stillReady.1 (by simp [after, EventGraphRuntime.State.complete,
          EventGraph.Config.complete, EventOrder.Cut.complete])
      obtain ⟨next, law, applicationEq, networkEq, receiptsEq, recallEq⟩ :=
        (runtime setup).opening_response_settlement leaks players watcher policy execution
          pending serials owner event candidate ⟨payload, value⟩ evidence after
          accepted settled ticks
      refine ⟨next, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [responseEq] using law
      · simpa only [chosen, ↓reduceIte, after, EventGraphRuntime.State.complete,
          action, result] using applicationEq
      · simpa only [chosen, ↓reduceIte, responseEq] using networkEq
      · simpa only [chosen, ↓reduceIte] using receiptsEq
      · simpa only [responseEq] using recallEq

/-- The completed native block advances the actual typed source configuration.
Both the store and the owner's source-action history are transported; physical
replay names remain solely in native recall and network input history. -/
theorem ordinary_response_source_step (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (players : Player → (application setup leaks).Policy) (watcher : Player)
    (policy : players watcher = (application setup leaks).silentPolicy)
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (selected : HasVar Γ name (.commitment owner payload))
    (source : Config Player L Γ) (empty : source.registry = [])
    (refs : ContextRefs (graph setup).layout Γ)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (valid : execution.application.BindingInvariant)
    (event : (graph setup).EventId)
    (ownedEvent : (graph setup).actor? event = some owner)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [])
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get selected) [] outputEq codeEq)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (decoded : ∀ disclose, decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
        some (.reveal owner name disclose))
    (value : L.Val payload) (bound : source.state.get selected = .success value)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (entered ticks : Nat) (activated : execution.application.activatedAt event = some entered)
    (due : (runtime setup).deadline event ≤ execution.application.clock + ticks - entered)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (response : (application setup leaks).Action)
    (member : response ∈ ordinaryActions setup leaks bounds owner (execution.recall owner)
      (execution.observe (application setup leaks) owner)) :
    let disclose := sourceChoice setup leaks response
    let sourceNext := revealSuccessor published selected source disclose
    let resultRef : EventGraph.FieldRef (graph setup).layout (.publication payload) :=
      ⟨.inr event, outputEq⟩
    ∃ next, (runtime setup).runInteractionPlan leaks players
        ((runtime setup).idleNetwork leaks)
        ([.includeLatest event owner, .player watcher, .wire] ++
          List.replicate ticks .tick ++ [.expire event])
        (execution.respond (application setup leaks) owner response) = PMF.pure next ∧
      (refs.cons (name := published) resultRef).Agrees sourceNext.state
        next.application.config.store ∧
      decodeHistory setup.program
        (next.application.config.history.map
          (setup.eventGraph.fromModeCompletion .sequential)) = sourceNext.history := by
  dsimp only
  obtain ⟨next, law, applicationEq, _networkEq, _receiptsEq, _recallEq⟩ :=
    ordinary_response_settlement setup leaks bounds players watcher policy selected source.state
      refs execution agree valid event ownedEvent outputEq codeEq node value bound
      ready timely entered ticks activated due pending serials response member
  refine ⟨next, law, ?_, ?_⟩
  · have stores :
        (refs.cons (name := published) ⟨.inr event, outputEq⟩).Agrees
          (revealSuccessor published selected source (sourceChoice setup leaks response)).state
          (execution.application.complete event ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm)
              (sourceChoice setup leaks response))
            (cast (congrArg EventGraph.EventField.Value outputEq.symm)
              (if sourceChoice setup leaks response then source.state.get selected
                else PublicationResult.failure))).config.store :=
      complete_reveal_agrees published selected source empty refs execution.application
        agree event ready outputEq before (sourceChoice setup leaks response)
    simp only [bound] at stores
    rw [applicationEq]
    cases chosen : sourceChoice setup leaks response <;>
      simp only [chosen] at stores ⊢ <;> exact @stores
  · have histories := complete_reveal_history setup published selected source
      execution.application history event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (sourceChoice setup leaks response))
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (if sourceChoice setup leaks response then PublicationResult.success value else .failure))
      (sourceChoice setup leaks response) (decoded _)
    rw [applicationEq]
    cases chosen : sourceChoice setup leaks response <;>
      simp only [chosen] at histories ⊢ <;> exact histories

end Vegas
