/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRevealSettlement

/-! # Complete response blocks for source revelation choices

Each law includes reserved inclusion, the watcher's actual observation and
silent response, the idle network slot, the clock ticks, and expiry. Actual
pending messages and private observations remain in the execution.
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

/-- A timely accepted decision executes the complete monitoring and expiry
suffix. The fresh envelope is published once and no extra receipt is produced. -/
theorem decision_response_settlement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy) (watcher : Player)
    (policy : players watcher = (runtime.reactiveApplication leaks).silentPolicy)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (owner : Player) (event : graph.EventId) (submission : WitnessedSubmission graph)
    (addressed : submission.call.packet.event? graph = some event) (after : State graph)
    (accepted : (runtime.reactiveApplication leaks).handle
      ((runtime.reactiveApplication leaks).submit execution.application owner submission)
      ⟨(owner, execution.network.nextSerial owner),
        (runtime.reactiveApplication leaks).packet
          ((runtime.reactiveApplication leaks).submit execution.application owner submission) owner
          (execution.network.known owner) submission⟩ = some after)
    (settled : ¬after.config.cut.Ready event) (ticks : Nat) :
    let app := runtime.reactiveApplication leaks
    let submitted := execution.respond app owner
      ⟨some submission⟩
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
    ⟨some submission⟩
  obtain ⟨included, inclusion, applicationEq, pendingEq, receiptsEq, recallEq, networkEq⟩ :=
    runtime.submission_published_checkpoint leaks players (runtime.idleNetwork leaks)
      execution owner event submission addressed after pending
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
