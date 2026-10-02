/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRevealSettlement

/-! # Complete response blocks for source revelation choices

Each law includes reserved inclusion, the watcher's actual observation and
silent response, the idle network slot, the clock ticks, and expiry. Published
replays are retained as distinct physical responses and network inputs. Their
effect on the source event is withholding; no private history is erased.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Certificate normalization changes only the request naming the evidence;
the successful source action remains exactly the same opening call. -/
theorem normalized_reveal_response (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L) :
    ∃ evidence, (runtime.reactiveNormalization leaks).action owner past view
        (runtime.canonicalRevealResponse leaks event candidate raw true) =
      ⟨some ⟨⟨.opening event candidate raw, none⟩, evidence⟩⟩ := by
  simp only [ReactiveApplication.SubmissionNormalization.action, canonicalRevealResponse,
    ↓reduceIte, disclosureSubmission, reactiveNormalization,
    WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none]
  exact ⟨_, rfl⟩

/-- At a source checkpoint, passive observation contributes no new random
signal. The existing player instruction samples exactly the player's response
law and records the activation in the scheduler's own recall. -/
theorem player_instruction_published (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (published : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id) :
    let app := runtime.reactiveApplication leaks
    let activated : app.Execution :=
      { execution with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate owner⟩] }
    runtime.interactionStep leaks players network (.player owner) execution =
      (players owner (execution.recall owner) (execution.observe app owner)).map
        (activated.respond app owner) := by
  simp only [interactionStep, interactionInstruction, PMF.pure_bind,
    ReactiveApplication.dispatch,
    ReactiveApplication.Execution.activate_of_pending_published _ _ _ published,
    PMF.pure_bind]
  rfl

/-- Source withholding executes the complete monitored failure branch. -/
theorem refusing_response_settlement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy) (watcher : Player)
    (policy : players watcher = (runtime.reactiveApplication leaks).silentPolicy)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (ready : execution.application.config.cut.Ready event)
    (entered ticks : Nat) (activated : execution.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ execution.application.clock + ticks - entered)
    (response : (runtime.reactiveApplication leaks).Action)
    (refuses : response = ⟨none⟩) :
    let app := runtime.reactiveApplication leaks
    let submitted := execution.respond app owner response
    ∃ next, runtime.runInteractionPlan leaks players (runtime.idleNetwork leaks)
        ([.includeLatest event owner, .player watcher, .wire] ++
          List.replicate ticks .tick ++ [.expire event]) submitted = PMF.pure next ∧
      next.application =
        ({ execution.application with clock := execution.application.clock + ticks } :
          State graph).complete event ready
            (cast (congrArg EventField.Action outputEq.symm) false)
            (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure) ∧
      next.network = submitted.network ∧ next.receipts = execution.receipts ∧
      next.recall = (submitted.respond app watcher ⟨none⟩).recall := by
  let app := runtime.reactiveApplication leaks
  let submitted := execution.respond app owner response
  have quiet : submitted.application = execution.application ∧
      (∀ message ∈ submitted.network.pending,
        message.id ∈ submitted.network.ledger.map Message.id) := by
    rcases refuses with rfl
    exact ⟨rfl, pending⟩
  let waited : app.Execution := { submitted with
    environmentRecall := submitted.environmentRecall ++
      [⟨submitted.observeEnvironment app, .wait⟩] }
  have inclusion : runtime.interactionStep leaks players (runtime.idleNetwork leaks)
      (.includeLatest event owner) submitted = PMF.pure waited := by
    rw [runtime.interaction_includeLatest_of_pending_published leaks players
      (runtime.idleNetwork leaks) submitted owner event quiet.2]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    rfl
  have waitedReady : waited.application.config.cut.Ready event := by
    change submitted.application.config.cut.Ready event
    rw [quiet.1]
    exact ready
  have waitedActivation : waited.application.activatedAt event = some entered := by
    change submitted.application.activatedAt event = some entered
    rw [quiet.1]
    exact activated
  have waitedDue : runtime.deadline event ≤ waited.application.clock + ticks - entered := by
    change runtime.deadline event ≤ submitted.application.clock + ticks - entered
    rw [quiet.1]
    exact due
  obtain ⟨next, law, applicationEq, networkEq, receiptEq, recallEq⟩ :=
    runtime.monitored_silent_reveal leaks players watcher policy waited quiet.2 owner event
      payload binding checks outputEq codeEq node waitedReady entered ticks waitedActivation
      waitedDue
  refine ⟨next, ?_, ?_, networkEq, ?_, recallEq⟩
  · change (runtime.interactionStep leaks players (runtime.idleNetwork leaks)
        (.includeLatest event owner) submitted).bind _ = _
    rw [inclusion, PMF.pure_bind]
    exact law
  · simpa only [show waited.application = execution.application from quiet.1] using applicationEq
  · exact receiptEq.trans (app.respond_receipts execution owner response)

/-- A timely accepted opening executes the same complete monitoring and expiry
suffix. The fresh envelope is published once and no extra receipt is produced. -/
theorem opening_response_settlement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy) (watcher : Player)
    (policy : players watcher = (runtime.reactiveApplication leaks).silentPolicy)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (evidence : EvidenceRequest graph) (after : State graph)
    (accepted : runtime.handle execution.application
      ⟨(owner, execution.network.nextSerial owner), .opening event candidate raw⟩ = some after)
    (settled : ¬after.config.cut.Ready event) (ticks : Nat) :
    let app := runtime.reactiveApplication leaks
    let submitted := execution.respond app owner
      ⟨some ⟨⟨.opening event candidate raw, none⟩, evidence⟩⟩
    ∃ next, runtime.runInteractionPlan leaks players (runtime.idleNetwork leaks)
        ([.includeLatest event owner, .player watcher, .wire] ++
          List.replicate ticks .tick ++ [.expire event]) submitted = PMF.pure next ∧
      next.application = { after with clock := after.clock + ticks } ∧
      next.network = (submitted.network.includePending
        (owner, execution.network.nextSerial owner)).2 ∧
      next.receipts = execution.receipts ++
        [((owner, execution.network.nextSerial owner), true)] ∧
      ∀ observer, observer ≠ watcher → next.recall observer = submitted.recall observer := by
  let app := runtime.reactiveApplication leaks
  let submitted := execution.respond app owner
    ⟨some ⟨⟨.opening event candidate raw, none⟩, evidence⟩⟩
  obtain ⟨included, inclusion, applicationEq, pendingEq, receiptsEq, recallEq, networkEq⟩ :=
    runtime.opening_published_checkpoint leaks players (runtime.idleNetwork leaks)
      execution owner event candidate raw evidence after pending
      (serials.next_unpublished owner) accepted
  have notReady : ¬included.application.config.cut.Ready event := by
    rw [applicationEq]
    exact settled
  obtain ⟨next, law, nextApplication, nextNetwork, nextReceipts, nextRecall⟩ :=
    runtime.monitored_settled_reveal leaks players watcher policy included pendingEq event
      notReady ticks
  refine ⟨next, ?_, ?_, nextNetwork.trans networkEq, nextReceipts.trans receiptsEq, ?_⟩
  · change (runtime.interactionStep leaks players (runtime.idleNetwork leaks)
        (.includeLatest event owner) submitted).bind _ = _
    rw [inclusion, PMF.pure_bind]
    exact law
  · simpa only [applicationEq] using nextApplication
  · intro observer different
    rw [nextRecall]
    change (if observer = watcher then _ else included.recall observer) = _
    rw [ite_eq_right different, recallEq]

end Vegas.EventGraphRuntime
