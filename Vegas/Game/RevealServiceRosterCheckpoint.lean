/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterCompletion
import Vegas.Game.RevealServiceCheckpoint

/-! # Public source checkpoints after arbitrary permitted revelation rosters

The actual pending pool, sampled leak lists, input traffic and response recall
are retained. The source state determines only application state and the public
ledger, receipts and allocation counters at the boundary. This invariant holds
for arbitrary retained policies, including off-path continuations.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_opening_at_checkpoint (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (selected : HasVar Γ name (.commitment owner payload))
    (source : State L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source execution.application.config.store)
    (valid : execution.application.BindingInvariant)
    (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [])
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get selected) [] outputEq codeEq)
    (value : L.Val payload) (bound : source.get selected = .success value) :
    ∃ candidate, execution.application.accepted (refs.get selected).field = some candidate ∧
      candidate.1 = owner ∧
      execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
      rosterOpening? setup leaks owner event
        (execution.observe (application setup leaks) owner) =
          some (candidate, ⟨payload, value⟩) := by
  have stored : (refs.get selected).get? execution.application.config.store =
      some (.success value) := by
    simpa only [bound, cellValue] using agree selected
  obtain ⟨candidate, associated, owned, verified⟩ :=
    valid.success_provenance (refs.get selected) value stored
  refine ⟨candidate, associated, owned, verified, ?_⟩
  let view := execution.observe (application setup leaks) owner
  have seesAccepted : view.application.publicView.accepted (refs.get selected).field =
      some candidate := associated
  have resolved : EventGraph.EventCode.resolveOutput? (refs.get selected) [] true
      view.application.observation.store = some (.success value) := by
    change EventGraph.EventCode.resolveOutput? (refs.get selected) [] true
      ((graph setup).playerStore owner execution.application.config.store) = _
    rw [EventGraph.EventCode.resolveOutput?_playerStore]
    simp only [EventGraph.EventCode.resolveOutput?, stored,
      EventGraph.GuardCheck.allAccepted?, ↓reduceIte]
    rfl
  change rosterOpening? setup leaks owner event view = _
  simp only [rosterOpening?, node, resolved, seesAccepted, bind, Option.bind_some,
    owned, ne_eq, not_true_eq_false, ↓reduceIte]

/-- Public checkpoint preservation depends on the actual settlement endpoint,
not on how the opening time was selected. -/
theorem PublicCheckpoint.reveal_endpoint
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    {source : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (checkpoint : PublicCheckpoint setup leaks initial source refs rank execution)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (selected : HasVar Γ name (.commitment owner payload))
    (event : (graph setup).EventId) (eventRank : event.val = rank)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [])
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get selected) [] outputEq codeEq)
    (ready : execution.application.config.cut.Ready event)
    (value : L.Val payload) (candidate : Handle (graph setup))
    (associated : execution.application.accepted (refs.get selected).field = some candidate)
    (disclose : Bool) (next : (application setup leaks).Execution)
    (nextInvariant : EventGraphRuntime.State.Invariant (graph := graph setup)
      (setup.eventInputs initial) next.application)
    (store : (refs.cons (name := published) ⟨.inr event, outputEq⟩).Agrees
      (revealSuccessor published selected source disclose).state next.application.config.store)
    (history : decodeHistory setup.program
      (next.application.config.history.map (setup.eventGraph.fromModeCompletion .sequential)) =
      (revealSuccessor published selected source disclose).history)
    (applicationEq : next.application = (if disclose then
      { execution.application.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (PublicationResult.success value)) with
          clock := execution.application.clock + (event.val + 1) }
      else ({ execution.application with clock := execution.application.clock + (event.val + 1) } :
        EventGraphRuntime.State (graph setup)).complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) PublicationResult.failure)))
    (ledger : next.network.ledger = (if disclose then List.append execution.network.ledger
      [(runtime setup).windowEnvelope leaks owner event candidate ⟨payload, value⟩ execution]
      else execution.network.ledger))
    (receipts : next.receipts = (if disclose then execution.receipts ++
      [((owner, execution.network.nextSerial owner), true)] else execution.receipts))
    (counters : next.network.nextSerial = fun who => execution.network.nextSerial who +
      if who = owner ∧ disclose then 1 else 0) :
    PublicCheckpoint setup leaks initial (revealSuccessor published selected source disclose)
      (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1) next := by
  let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose
  let result := cast (congrArg EventGraph.EventField.Value outputEq.symm)
    (if disclose then PublicationResult.success value else .failure)
  have configEq : next.application.config =
      (execution.application.complete event ready action result).config := by
    dsimp only [action, result]
    rw [applicationEq]
    cases disclose <;> rfl
  change next.application.config = execution.application.config.complete event ready action result
    at configEq
  have tables : next.application.accepted = execution.application.accepted ∧
      next.application.candidates = execution.application.candidates ∧
      next.application.remembered = execution.application.remembered := by
    rw [applicationEq]
    cases disclose <;> exact ⟨rfl, rfl, rfl⟩
  let initialAccepted :=
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).accepted
  have acceptedCandidate : initialAccepted (refs.get selected).field = some candidate := by
    rw [checkpoint.accepted] at associated
    exact associated
  have packet : publicationPacket? initialAccepted
      (execution.application.config.complete event ready action result).store event =
      if disclose then some (owner, (⟨.opening event candidate ⟨payload, value⟩,
        some ⟨candidate, ⟨payload, value⟩⟩⟩ : WitnessedPacket (graph setup))) else none := by
    cases choice : disclose <;> simp only [result, choice, Bool.false_eq_true, ↓reduceIte]
    · exact publicationPacket?_complete_resolve initialAccepted execution.application.config
        event ready owner payload (refs.get selected) [] outputEq codeEq node action .failure
    · rw [publicationPacket?_complete_resolve initialAccepted execution.application.config
        event ready owner payload (refs.get selected) [] outputEq codeEq node action
          (.success value),
        acceptedCandidate]
      rfl
  have transcript : next.network.ledger =
        publicationLedger initialAccepted ((graph setup).publicObserve next.application.config) ∧
      next.receipts =
        publicationReceipts initialAccepted ((graph setup).publicObserve next.application.config) ∧
      next.network.nextSerial =
        publicationSerial initialAccepted
          ((graph setup).publicObserve next.application.config) := by
    change next.network.ledger = (if disclose then _ else _) at ledger
    change next.receipts = (if disclose then _ else _) at receipts
    change next.network.nextSerial = (fun who => _ + if who = owner ∧ disclose then 1 else 0)
      at counters
    rw [configEq]
    cases choice : disclose
    · simp only [choice, Bool.false_eq_true, ↓reduceIte, and_false, Nat.add_zero]
        at packet ledger receipts counters
      rw [publicationLedger_complete_none _ _ _ _ _ _ packet,
        publicationReceipts_complete_none _ _ _ _ _ _ packet,
        publicationSerial_complete_none _ _ _ _ _ _ packet]
      exact ⟨ledger.trans checkpoint.ledger, receipts.trans checkpoint.receipts,
        counters.trans checkpoint.counters⟩
    · simp only [choice, ↓reduceIte, and_true] at packet ledger receipts counters
      refine ⟨?_, ?_, ?_⟩
      · rw [publicationLedger_complete _ _ _ _ _ _ _ _ packet, ledger]
        simp only [windowEnvelope, checkpoint.ledger, checkpoint.counters]
        rfl
      · rw [publicationReceipts_complete _ _ _ _ _ _ _ _ packet, receipts,
          checkpoint.receipts, checkpoint.counters]
      · funext who
        rw [publicationSerial_complete _ _ _ _ _ _ _ _ packet, counters, checkpoint.counters]
        simp only [eq_comm]
        rfl
  have packetPresence : (publicationPacket? initialAccepted
      (execution.application.config.complete event ready action result).store event).isSome =
      disclose := by rw [packet]; cases disclose <;> rfl
  have calendar := settlement_calendar setup checkpoint.reveals execution.application
    checkpoint.invariant event ready action result disclose initialAccepted
      (eventRank.symm ▸ checkpoint.clock) packetPresence
  have actualCalendar : next.application.clock = clockAt (rank + 1) ∧
      next.application.activatedAt = checkpointActivations setup initialAccepted
        ((graph setup).publicObserve next.application.config) (rank + 1) := by
    rw [applicationEq]
    cases disclose <;> simpa only [action, result, eventRank,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte] using calendar
  have boundAfter := checkpoint.binding.complete_nonbinding event ready action result (by
    intro other otherPayload bindingEq
    cases outputEq.symm.trans bindingEq)
  refine {
    emptyRegistry := revealSuccessor_registry_empty published selected source
      checkpoint.emptyRegistry _
    openable := revealSuccessor_bindingsOpenable published selected source checkpoint.openable _
    agrees := @store
    history := history
    ordered := ?_
    invariant := nextInvariant
    binding := boundAfter.copy configEq tables.1 tables.2.1
    accepted := tables.1.trans checkpoint.accepted
    candidates := tables.2.1.trans checkpoint.candidates
    remembered := tables.2.2.trans checkpoint.remembered
    timely := ?_
    reveals := checkpoint.reveals
    covered := checkpoint.covered.cons setup.program (cell := .publication payload)
      ⟨.inr event, outputEq⟩ event rfl eventRank
    ledger := transcript.1
    receipts := transcript.2.1
    counters := transcript.2.2
    clock := actualCalendar.1
    activated := actualCalendar.2 }
  · rw [configEq]
    exact checkpoint.ordered.complete_at event ready eventRank
  · intro successor nextRank actor
    rw [applicationEq]
    have timelyNext := settlement_successor_timely setup execution.application checkpoint.invariant
      event successor ready (by omega) actor action result disclose
    cases disclose <;> simpa only [action, result,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte] using timelyNext


theorem PublicCheckpoint.reveal_roster [Fintype Player]
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    {source : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (checkpoint : PublicCheckpoint setup leaks initial source refs rank execution)
    (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ rosterActions setup leaks bounds rosters who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (selected : HasVar Γ name (.commitment owner payload))
    (event : (graph setup).EventId) (eventRank : event.val = rank)
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
    (offset : (execution.recall owner).length = rosterOffset setup rosters owner event)
    (clean : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (next : (application setup leaks).Execution)
    (reached : next ∈ ((runtime setup).runInteractionPlan leaks players network
      (((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        List.replicate (event.val + 1) .tick ++ [.expire event]) execution).support) :
    ∃ disclose : Bool,
      PublicCheckpoint setup leaks initial (revealSuccessor published selected source disclose)
        (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1) next ∧
      next.network.Satisfies (fun message => message.id ∈ next.network.ledger.map Message.id) := by
  have ready : execution.application.config.cut.Ready event := by
    have active : rank < (graph setup).order.eventCount := eventRank ▸ event.isLt
    have chosenEvent : (⟨rank, active⟩ : (graph setup).EventId) = event := Fin.ext eventRank.symm
    rw [← chosenEvent]
    exact checkpoint.ordered.ready active
  have strategic : ((graph setup).actor? event).isSome = true := by rw [ownedEvent]; rfl
  have timely := checkpoint.timely event eventRank strategic
  obtain ⟨entered, activated⟩ := checkpoint.invariant.activatedAt_eq_some_of_ready_actor
    event ready strategic
  have due := checkpoint.invariant.due_after_deadline (runtime setup) event entered activated
  obtain ⟨value, bound⟩ := checkpoint.openable selected
  obtain ⟨candidate, associated, owned, verified, opening⟩ :=
    roster_opening_at_checkpoint setup leaks selected source.state refs execution checkpoint.agrees
      checkpoint.binding event outputEq codeEq node value bound
  obtain ⟨slot, store, history, applicationEq, cleanAfter, ledger, receipts, counters⟩ :=
    roster_menu_reveal_source_step setup leaks bounds rosters published selected source
      checkpoint.emptyRegistry refs execution checkpoint.agrees checkpoint.history event outputEq
        codeEq node before decoded value bound candidate owned associated verified ready timely
          ownedEvent opening offset entered (event.val + 1) activated due clean serials
            players covered network next reached
  have progressed := (runtime setup).runInteractionPlan_facts leaks (setup.eventInputs initial)
    players network _ execution next checkpoint.invariant reached
  exact ⟨slot.isSome, checkpoint.reveal_endpoint published selected event eventRank outputEq
    codeEq node ready value candidate associated slot.isSome next progressed.invariant
      store history applicationEq ledger receipts counters, cleanAfter⟩

/-- Every supported timed implementation of one fixed source disclosure choice
advances the same public source checkpoint, while retaining all traffic memory. -/
theorem PublicCheckpoint.reveal_scheduled
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    {source : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (checkpoint : PublicCheckpoint setup leaks initial source refs rank execution)
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (event : (graph setup).EventId) (eventRank : event.val = rank)
    (ownedEvent : (graph setup).actor? event = some owner)
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
    (associated : execution.application.accepted (refs.get binding).field = some candidate)
    (valid : execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (offset : (execution.recall owner).length = rosterOffset setup rosters owner event)
    (clean : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (slot : Option (Fin ((rosters event).count owner)))
    (next : (application setup leaks).Execution)
    (reached : next ∈ ((runtime setup).runInteractionPlan leaks
      ((runtime setup).openingWindowPlayers leaks owner event candidate ⟨payload, value⟩
        (rosterOffset setup rosters owner event) slot) network
      (((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        List.replicate (event.val + 1) .tick ++ [.expire event]) execution).support) :
    PublicCheckpoint setup leaks initial (revealSuccessor published binding source slot.isSome)
      (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1) next ∧
    next.network.Satisfies (fun message => message.id ∈ next.network.ledger.map Message.id) := by
  have ready : execution.application.config.cut.Ready event := by
    have active : rank < (graph setup).order.eventCount := eventRank ▸ event.isLt
    have chosenEvent : (⟨rank, active⟩ : (graph setup).EventId) = event := Fin.ext eventRank.symm
    rw [← chosenEvent]
    exact checkpoint.ordered.ready active
  have strategic : ((graph setup).actor? event).isSome = true := by rw [ownedEvent]; rfl
  have timely := checkpoint.timely event eventRank strategic
  obtain ⟨entered, activated⟩ := checkpoint.invariant.activatedAt_eq_some_of_ready_actor
    event ready strategic
  have due := checkpoint.invariant.due_after_deadline (runtime setup) event entered activated
  have reached' := reached
  rw [← offset] at reached'
  obtain ⟨store, history, cleanAfter⟩ := roster_reveal_source_step setup leaks published binding
    source checkpoint.emptyRegistry refs execution checkpoint.agrees checkpoint.history event
      outputEq codeEq node before decoded value bound candidate owned associated valid ready
        timely entered (event.val + 1) activated due clean serials (rosters event) slot network
          next reached'
  have stored : (refs.get binding).get? execution.application.config.store =
      some (.success value) := by
    simpa only [bound, cellValue] using checkpoint.agrees binding
  have resolved : EventGraph.EventCode.resolveOutput? (refs.get binding) [] true
      execution.application.config.store = some (.success value) := by
    simp only [EventGraph.EventCode.resolveOutput?, stored,
      EventGraph.GuardCheck.allAccepted?, ↓reduceIte]
    rfl
  have accepted : (application setup leaks).handle execution.application
      ((runtime setup).windowEnvelope leaks owner event candidate ⟨payload, value⟩ execution) =
        some (execution.application.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (PublicationResult.success value))) :=
    handle_opening_eq (runtime setup) execution.application _ event candidate owner payload
      (refs.get binding) [] outputEq codeEq node ready timely rfl owned associated
        value valid stored (.success value) resolved
  obtain ⟨applicationEq, _clean, ledger, receipts, counters⟩ :=
    (runtime setup).openingWindow_expiry leaks owner event payload (refs.get binding) [] outputEq
      codeEq node candidate value execution ready serials clean owned valid accepted entered
        (event.val + 1) activated due (rosters event) slot network next reached'
  have progressed := (runtime setup).runInteractionPlan_facts leaks (setup.eventInputs initial)
    _ network _ execution next checkpoint.invariant reached
  exact ⟨checkpoint.reveal_endpoint published binding event eventRank outputEq codeEq node ready
    value candidate associated slot.isSome next progressed.invariant store history applicationEq
      ledger receipts counters, cleanAfter⟩

end Vegas
