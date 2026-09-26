/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRevealSettlement

/-! # Complete response blocks for source revelation choices

Each law includes reserved inclusion, the watcher's actual observation and
response, public report selection, the clock ticks, and expiry. Published
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
      ⟨some (.submit ⟨⟨.opening event candidate raw, none⟩, evidence⟩)⟩ := by
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
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch,
    ReactiveApplication.Execution.activate_of_pending_published _ _ _ published,
    FinDist.pure_bind]
  rfl

/-- Every physical name for source withholding executes the complete monitored
failure branch. The resulting network still contains the actual replay input. -/
theorem refusing_response_settlement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy) (watcher : Player)
    (policy : players watcher = (runtime.reactiveApplication leaks).reportFirstUnpublished)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (leaked : ∀ message ∈ execution.network.leaked watcher,
      message.id ∈ execution.network.ledger.map Message.id)
    (inputs : ∀ input ∈ execution.network.inputs,
      input.envelope.id ∈ execution.network.ledger.map Message.id)
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
    (refuses : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩ ∧
      id ∈ execution.network.ledger.map Message.id) :
    let app := runtime.reactiveApplication leaks
    let submitted := execution.respond app owner response
    ∃ next, runtime.runInteractionPlan leaks players (runtime.reportNetwork leaks watcher)
        ([.includeLatest event owner, .player watcher, .wire] ++
          List.replicate ticks .tick ++ [.expire event]) submitted = FinDist.pure next ∧
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
        message.id ∈ submitted.network.ledger.map Message.id) ∧
      (∀ message ∈ submitted.network.leaked watcher,
        message.id ∈ submitted.network.ledger.map Message.id) ∧
      (∀ input ∈ submitted.network.inputs,
        input.envelope.id ∈ submitted.network.ledger.map Message.id) := by
    rcases refuses with rfl | ⟨id, rfl, spent⟩
    · exact ⟨rfl, pending, leaked, inputs⟩
    · refine ⟨rfl, execution.network.replay_pending_published owner id pending spent, ?_, ?_⟩
      · change ∀ message ∈ (execution.network.replay owner id).2.leaked watcher,
          message.id ∈ (execution.network.replay owner id).2.ledger.map Message.id
        have observed := execution.network.replay_observe owner watcher id
        have leakedEq := congrArg MessageNetwork.PlayerView.leaked observed
        have ledgerEq := congrArg MessageNetwork.PlayerView.ledger observed
        change (execution.network.replay owner id).2.leaked watcher =
          execution.network.leaked watcher at leakedEq
        change (execution.network.replay owner id).2.ledger = execution.network.ledger at ledgerEq
        rw [leakedEq, ledgerEq]
        exact leaked
      · change ∀ input ∈ (execution.network.replay owner id).2.inputs,
          input.envelope.id ∈ (execution.network.replay owner id).2.ledger.map Message.id
        cases found : (execution.network.known owner).find? (fun packet => packet.id = id) with
        | none => simpa only [MessageNetwork.replay, found] using inputs
        | some packet =>
            have identified : packet.id = id := by
              simpa only [decide_eq_true_eq] using List.find?_some found
            intro input member
            change input ∈ (execution.network.replay owner id).2.inputs at member
            simp only [MessageNetwork.replay, found] at member ⊢
            rcases List.mem_append.mp member with prior | added
            · exact inputs input prior
            · obtain rfl := List.mem_singleton.mp added
              simpa only [identified] using spent
  let waited : app.Execution := { submitted with
    environmentRecall := submitted.environmentRecall ++
      [⟨submitted.observeEnvironment app, .wait⟩] }
  have inclusion : runtime.interactionStep leaks players (runtime.reportNetwork leaks watcher)
      (.includeLatest event owner) submitted = FinDist.pure waited := by
    rw [runtime.interaction_includeLatest_of_pending_published leaks players
      (runtime.reportNetwork leaks watcher) submitted owner event quiet.2.1]
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
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
    runtime.monitored_silent_reveal leaks players watcher policy waited quiet.2.1 quiet.2.2.1
      (fun input member _ => quiet.2.2.2 input member) owner event payload binding checks
      outputEq codeEq node waitedReady entered ticks waitedActivation waitedDue
  refine ⟨next, ?_, ?_, networkEq, ?_, recallEq⟩
  · change (runtime.interactionStep leaks players (runtime.reportNetwork leaks watcher)
        (.includeLatest event owner) submitted).bind _ = _
    rw [inclusion, FinDist.pure_bind]
    exact law
  · simpa only [show waited.application = execution.application from quiet.1] using applicationEq
  · exact receiptEq.trans (app.respond_receipts execution owner response)

/-- A timely accepted opening executes the same complete monitoring and expiry
suffix. The fresh envelope is published once and no extra receipt is produced. -/
theorem opening_response_settlement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy) (watcher : Player)
    (policy : players watcher = (runtime.reactiveApplication leaks).reportFirstUnpublished)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (leaked : ∀ message ∈ execution.network.leaked watcher,
      message.id ∈ execution.network.ledger.map Message.id)
    (inputs : ∀ input ∈ execution.network.inputs,
      input.envelope.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (evidence : EvidenceRequest graph) (after : State graph)
    (accepted : runtime.handle execution.application
      ⟨(owner, execution.network.nextSerial owner), .opening event candidate raw⟩ = some after)
    (settled : ¬after.config.cut.Ready event) (ticks : Nat) :
    let app := runtime.reactiveApplication leaks
    let submitted := execution.respond app owner
      ⟨some (.submit ⟨⟨.opening event candidate raw, none⟩, evidence⟩)⟩
    ∃ next, runtime.runInteractionPlan leaks players (runtime.reportNetwork leaks watcher)
        ([.includeLatest event owner, .player watcher, .wire] ++
          List.replicate ticks .tick ++ [.expire event]) submitted = FinDist.pure next ∧
      next.application = { after with clock := after.clock + ticks } ∧
      next.network = (submitted.network.includePending
        (owner, execution.network.nextSerial owner)).2 ∧
      next.receipts = execution.receipts ++
        [((owner, execution.network.nextSerial owner), true)] ∧
      ∀ observer, observer ≠ watcher → next.recall observer = submitted.recall observer := by
  let app := runtime.reactiveApplication leaks
  let submitted := execution.respond app owner
    ⟨some (.submit ⟨⟨.opening event candidate raw, none⟩, evidence⟩)⟩
  let packet := app.packet execution.application owner (execution.network.known owner)
    ⟨⟨.opening event candidate raw, none⟩, evidence⟩
  let envelope : Message Player app.Payload :=
    ⟨(owner, execution.network.nextSerial owner), packet⟩
  have found : submitted.network.lookup envelope.id = some envelope :=
    serials.lookup_submit owner packet
  obtain ⟨included, inclusion, applicationEq, pendingEq, receiptsEq, recallEq, networkEq⟩ :=
    runtime.opening_published_checkpoint leaks players (runtime.reportNetwork leaks watcher)
      execution owner event candidate raw evidence after pending
      (serials.next_unpublished owner) accepted
  have ledgerEq : included.network.ledger = execution.network.ledger ++ [envelope] := by
    rw [networkEq]
    change (submitted.network.includePending envelope.id).2.ledger = _
    simp only [MessageNetwork.includePending, found]
    rfl
  have leakedEq : included.network.leaked watcher = execution.network.leaked watcher := by
    rw [networkEq]
    change (submitted.network.includePending envelope.id).2.leaked watcher = _
    simp only [MessageNetwork.includePending, found]
    rfl
  have inputsEq : included.network.inputs = execution.network.inputs ++ [⟨owner, envelope⟩] := by
    rw [networkEq]
    change (submitted.network.includePending envelope.id).2.inputs = _
    simp only [MessageNetwork.includePending, found]
    rfl
  have includedLeaks : ∀ message ∈ included.network.leaked watcher,
      message.id ∈ included.network.ledger.map Message.id := by
    intro message member
    rw [leakedEq] at member
    rw [ledgerEq, List.map_append]
    exact List.mem_append_left _ (leaked message member)
  have includedInputs : ∀ input ∈ included.network.inputs,
      input.envelope.id ∈ included.network.ledger.map Message.id := by
    intro input member
    rw [inputsEq] at member
    rw [ledgerEq, List.map_append]
    rcases List.mem_append.mp member with prior | added
    · exact List.mem_append_left _ (inputs input prior)
    · obtain rfl := List.mem_singleton.mp added
      exact List.mem_append_right _ (by simp)
  have notReady : ¬included.application.config.cut.Ready event := by
    rw [applicationEq]
    exact settled
  obtain ⟨next, law, nextApplication, nextNetwork, nextReceipts, nextRecall⟩ :=
    runtime.monitored_settled_reveal leaks players watcher policy included pendingEq
      includedLeaks (fun input member _ => includedInputs input member) event notReady ticks
  refine ⟨next, ?_, ?_, nextNetwork.trans networkEq, nextReceipts.trans receiptsEq, ?_⟩
  · change (runtime.interactionStep leaks players (runtime.reportNetwork leaks watcher)
        (.includeLatest event owner) submitted).bind _ = _
    rw [inclusion, FinDist.pure_bind]
    exact law
  · simpa only [applicationEq] using nextApplication
  · intro observer different
    rw [nextRecall]
    change (if observer = watcher then _ else included.recall observer) = _
    rw [ite_eq_right different, recallEq]

end Vegas.EventGraphRuntime
