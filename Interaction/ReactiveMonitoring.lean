/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveLedgerConformance
import Interaction.ReactiveReceipts
import Interaction.MessageMonitoringProbability
import Interaction.ReactiveQuiescent

/-! # Passive observation followed by public report inclusion

The service uses an ordinary watcher activation and a subsequent inclusion of
its public rebroadcast. It never reads the watcher's private sample. Inclusion
is at most once, and all later policies and scheduler commands are unrestricted.
The resulting evidence bound is conditional on the specified snapshot and local
reporting policy. Choosing a sound conformance predicate, providing the reserved
service, and collecting a financial charge are separate obligations.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- Include the latest public rebroadcast by this watcher, if still unpublished.
The command inspects public traffic only, not observation samples or player recall. -/
def includeReported (watcher : Principal) (view : app.EnvironmentView) : app.Command :=
  match view.network.inputs.getLast? with
  | none => .wait
  | some input => if input.broadcaster = watcher ∧ input.envelope.sender ≠ watcher then
      app.atMostOnceCommand view (.include input.envelope.id) else .wait

theorem includeReported_fresh (watcher : Principal) (view : app.EnvironmentView)
    (id : MessageId Principal) (included : app.includeReported watcher view = .include id) :
    view.Unpublished app id := by
  unfold includeReported at included
  split at included
  · cases included
  · split at included
    · exact app.atMostOnceCommand_fresh view _ id included
    · cases included

/-- A single reporting policy, fixed independently of any deviation or
equilibrium. Previously published material cannot conceal a fresh report. -/
def reportFirstUnpublished : app.Policy := fun _ view =>
  FinDist.pure <| match view.messages.leaked.find? (fun message =>
      decide (message.id ∉ view.messages.ledger.map Message.id)) with
    | none => ⟨none⟩
    | some message => ⟨some (.replay message.id)⟩

theorem reportFirstUnpublished_silent (past : List app.PlayerEntry) (view : app.PlayerView)
    (published : ∀ message ∈ view.messages.leaked,
      message.id ∈ view.messages.ledger.map Message.id) :
    app.reportFirstUnpublished past view = FinDist.pure ⟨none⟩ := by
  have absent : view.messages.leaked.find? (fun message =>
      decide (message.id ∉ view.messages.ledger.map Message.id)) = none := by
    apply List.find?_eq_none.mpr
    intro message member
    simp only [published message member, not_true_eq_false, decide_false, Bool.false_eq_true,
      not_false_eq_true]
  simp only [reportFirstUnpublished, absent]

theorem includeReported_wait_of_published (watcher : Principal) (view : app.EnvironmentView)
    (published : ∀ input ∈ view.network.inputs, input.broadcaster = watcher →
      input.envelope.id ∈ view.network.ledger.map Message.id) :
    app.includeReported watcher view = .wait := by
  cases latest : view.network.inputs.getLast? with
  | none => simp only [includeReported, latest]
  | some input =>
      by_cases reported : input.broadcaster = watcher ∧ input.envelope.sender ≠ watcher
      · have spent := published input (List.mem_of_getLast? latest) reported.1
        simp only [includeReported, latest, reported, ↓reduceIte, atMostOnceCommand,
          EnvironmentView.Unpublished, spent, not_true_eq_false, ite_self]
      · simp only [includeReported, latest, reported, ↓reduceIte]

theorem reportFirstUnpublished_reports (past : List app.PlayerEntry) (view : app.PlayerView)
    (id : MessageId Principal) (message : Message Principal app.Payload)
    (seen : message ∈ view.messages.leaked) (identified : message.id = id)
    (fresh : id ∉ view.messages.ledger.map Message.id)
    (unique : ∀ packet ∈ view.messages.leaked,
      packet.id ∉ view.messages.ledger.map Message.id → packet.id = id) :
    app.reportFirstUnpublished past view = FinDist.pure ⟨some (.replay id)⟩ := by
  unfold reportFirstUnpublished
  cases selected : view.messages.leaked.find? (fun packet =>
      decide (packet.id ∉ view.messages.ledger.map Message.id)) with
  | none =>
      have excluded := List.find?_eq_none.mp selected message seen
      exact (excluded (by simp only [identified, decide_eq_true_eq]; exact fresh)).elim
  | some packet =>
      have pending : packet.id ∉ view.messages.ledger.map Message.id :=
        of_decide_eq_true (List.find?_eq_some_iff_append.mp selected).1
      dsimp only
      rw [unique packet (List.mem_of_find?_eq_some selected) pending]

private theorem replay_lookup (execution : app.Execution) (watcher : Principal)
    (id : MessageId Principal) (message : Message Principal app.Payload)
    (found : execution.network.lookup id = some message) :
    (execution.respond app watcher ⟨some (.replay id)⟩).network.lookup id = some message := by
  change execution.network.pending.find? (fun packet => packet.id = id) = some message at found
  cases known : (execution.network.known watcher).find? (fun packet => packet.id = id) <;>
    simp only [Execution.respond, MessageNetwork.replay, known, MessageNetwork.lookup,
      List.find?_append, found, Option.or]

private theorem replay_reported (execution : app.Execution) (watcher : Principal)
    (id : MessageId Principal) (packet : Message Principal app.Payload)
    (known : (execution.network.known watcher).find? (fun message => message.id = id) = some packet)
    (foreign : id.1 ≠ watcher)
    (fresh : id ∉ execution.network.ledger.map Message.id) :
    app.includeReported watcher
      ((execution.respond app watcher ⟨some (.replay id)⟩).observeEnvironment app) =
        .include id := by
  have identified : packet.id = id := by
    simpa using (List.find?_eq_some_iff_append.mp known).1
  simp only [includeReported, Execution.respond, MessageNetwork.replay, known,
    Execution.observeEnvironment, MessageNetwork.publicView, List.getLast?_append,
    List.getLast?_singleton, Option.or, ↓reduceIte, atMostOnceCommand,
    EnvironmentView.Unpublished, Message.sender, identified, fresh, not_false_eq_true]
  exact ite_eq_left ⟨trivial, foreign⟩

private theorem known_of_leaked (execution : app.Execution) (watcher : Principal)
    (id : MessageId Principal) (message : Message Principal app.Payload)
    (seen : message ∈ execution.network.leaked watcher) (identified : message.id = id) :
    ∃ packet, (execution.network.known watcher).find? (fun packet => packet.id = id) =
      some packet := by
  have known : message ∈ execution.network.known watcher := by
    unfold MessageNetwork.known
    exact List.mem_append_left _ (List.mem_append_right _ seen)
  cases selected : (execution.network.known watcher).find? (fun packet => packet.id = id) with
  | some packet => exact ⟨packet, rfl⟩
  | none =>
      have absent := List.find?_eq_none.mp selected message known
      exact (absent (by simp [identified])).elim

private def sampled (execution : app.Execution) (watcher : Principal)
    (selected : Finset (MessageId Principal)) : app.Execution :=
  { execution with
    network := execution.network.learn watcher selected
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate watcher⟩] }

private theorem activation_law (execution : app.Execution) (watcher : Principal) :
    execution.environmentStep app (.activate watcher) =
      (app.observePending watcher execution.network.pending).map
        (sampled app execution watcher) := by
  simp only [Execution.environmentStep, FinDist.map_comp]
  rfl

private theorem sampled_mem (execution : app.Execution) (watcher : Principal)
    (selected : Finset (MessageId Principal))
    (supported : selected ∈ (app.observePending watcher execution.network.pending).support) :
    sampled app execution watcher selected ∈
      (execution.environmentStep app (.activate watcher)).support := by
  rw [activation_law, FinDist.support_map]
  exact ⟨selected, supported, rfl⟩

/-- A clean prefix plus one unpublished identifier is enough for the fixed
reporter to select that departure. Older leaked packets may remain in memory;
they are skipped using the ordinary public ledger. -/
theorem reportFirstUnpublished_after_activation
    (execution : app.Execution) (watcher : Principal) (id : MessageId Principal)
    (message : Message Principal app.Payload) (identified : message.id = id)
    (fresh : id ∉ execution.network.ledger.map Message.id)
    (oldPublished : ∀ packet ∈ execution.network.leaked watcher,
      packet.id ∈ execution.network.ledger.map Message.id)
    (uniquePending : ∀ packet ∈ execution.network.pending,
      packet.id ∉ execution.network.ledger.map Message.id → packet.id = id)
    (observed : app.Execution)
    (reached : observed ∈ (execution.environmentStep app (.activate watcher)).support)
    (seen : message ∈ (observed.observe app watcher).messages.leaked) :
    app.reportFirstUnpublished (observed.recall watcher) (observed.observe app watcher) =
      FinDist.pure ⟨some (.replay id)⟩ := by
  rw [activation_law, FinDist.support_map] at reached
  obtain ⟨selected, _, rfl⟩ := reached
  apply app.reportFirstUnpublished_reports _ _ id message seen identified fresh
  intro packet retained unpublished
  rcases execution.network.learn_mem watcher selected packet retained with old | pending
  · exact (unpublished (oldPublished packet old)).elim
  · exact uniquePending packet pending.1 unpublished

/-- Receipt evidence persists under every subsequent raw response and command. -/
theorem receipt_policyInvariant (players : Principal → app.Policy)
    (receipt : MessageId Principal × Bool) :
    app.PolicyInvariant players (fun execution => receipt ∈ execution.receipts) where
  respond execution who action present _ := by
    rw [app.respond_receipts]
    exact present
  environment execution next command present reached :=
    (app.environmentStep_receipts_prefix execution next command reached).subset present

/-- Composition of existing activation, response and public inclusion operations. -/
def reportInclusion (players : Principal → app.Policy) (watcher : Principal)
    (execution : app.Execution) : FinDist app.Execution :=
  (app.dispatch players (.activate watcher) execution).bind fun reported =>
    app.dispatch players (app.includeReported watcher (reported.observeEnvironment app)) reported

/-- A clean reporting block remains quiet even with spent envelopes pending.
It records the watcher's actual silent response and both service commands. -/
theorem reportInclusion_quiescent (players : Principal → app.Policy) (watcher : Principal)
    (policy : players watcher = app.reportFirstUnpublished) (execution : app.Execution)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (leaked : ∀ message ∈ execution.network.leaked watcher,
      message.id ∈ execution.network.ledger.map Message.id)
    (inputs : ∀ input ∈ execution.network.inputs, input.broadcaster = watcher →
      input.envelope.id ∈ execution.network.ledger.map Message.id) :
    ∃ next, app.reportInclusion players watcher execution = FinDist.pure next ∧
      next.application = execution.application ∧ next.network = execution.network ∧
      next.receipts = execution.receipts ∧
      next.recall = (execution.respond app watcher ⟨none⟩).recall ∧
      next.environmentRecall.length = execution.environmentRecall.length + 2 := by
  let activated : app.Execution := { execution with
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate watcher⟩] }
  let silent := activated.respond app watcher ⟨none⟩
  let next : app.Execution := { silent with environmentRecall := silent.environmentRecall ++
    [⟨silent.observeEnvironment app, .wait⟩] }
  have reports : app.reportFirstUnpublished (activated.recall watcher)
      (activated.observe app watcher) = FinDist.pure ⟨none⟩ :=
    app.reportFirstUnpublished_silent _ _ leaked
  have activation : app.dispatch players (.activate watcher) execution =
      FinDist.pure silent := by
    rw [dispatch, execution.activate_of_pending_published app watcher pending,
      FinDist.pure_bind]
    change app.invoke players watcher activated = _
    rw [invoke, policy, reports, FinDist.map_pure]
  have quiet : app.includeReported watcher (silent.observeEnvironment app) = .wait :=
    app.includeReported_wait_of_published watcher _ inputs
  refine ⟨next, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [reportInclusion, activation, FinDist.pure_bind, quiet]
    simp only [dispatch, Command.actor?, resume, Execution.environmentStep,
      FinDist.map_pure, FinDist.pure_bind, next]
  · simp only [next, silent, activated, Execution.respond, List.length_append,
      List.length_cons, List.length_nil]

private theorem reportInclusion_law (players : Principal → app.Policy) (watcher : Principal)
    (execution : app.Execution) :
    app.reportInclusion players watcher execution =
      (app.observePending watcher execution.network.pending).bind fun selected =>
        (app.invoke players watcher (sampled app execution watcher selected)).bind fun reported =>
          app.dispatch players (app.includeReported watcher (reported.observeEnvironment app))
            reported := by
  unfold reportInclusion
  rw [dispatch, activation_law, FinDist.bind_map, FinDist.bind_bind]
  rfl

private theorem sampled_leaked (execution : app.Execution) (watcher : Principal)
    (id : MessageId Principal) (message : Message Principal app.Payload)
    (found : execution.network.lookup id = some message) (foreign : id.1 ≠ watcher)
    (unknown : (execution.network.known watcher).any (fun packet => packet.id = id) = false)
    (fresh : id ∉ execution.network.ledger.map Message.id)
    (selected : Finset (MessageId Principal)) (chosen : id ∈ selected) :
    message ∈ (sampled app execution watcher selected).network.leaked watcher := by
  have reported := execution.network.reports_learn_selected (fun _ => true) watcher selected
    id message found foreign chosen unknown rfl
  have seen := ((MessageNetwork.PlayerView.mem_reports ..).mp reported).1
  rcases seen with seen | published
  · exact seen
  · have identified : message.id = id := by
      simpa using (List.find?_eq_some_iff_append.mp found).1
    exact (fresh (List.mem_map.mpr ⟨message, published, identified⟩)).elim

private theorem report_recorded (players : Principal → app.Policy)
    (execution : app.Execution) (watcher : Principal) (id : MessageId Principal)
    (message : Message Principal app.Payload)
    (found : execution.network.lookup id = some message)
    (foreign : id.1 ≠ watcher)
    (fresh : id ∉ execution.network.ledger.map Message.id)
    (seen : message ∈ execution.network.leaked watcher)
    (reports : players watcher (execution.recall watcher) (execution.observe app watcher) =
      FinDist.pure ⟨some (.replay id)⟩)
    (next : app.Execution)
    (reached : next ∈ ((app.invoke players watcher execution).bind fun reported =>
      app.dispatch players (app.includeReported watcher (reported.observeEnvironment app))
        reported).support) :
    (id, (app.handle execution.application message).isSome) ∈ next.receipts ∧
      message ∈ next.network.ledger := by
  have identified : message.id = id := by
    simpa using (List.find?_eq_some_iff_append.mp found).1
  obtain ⟨packet, known⟩ := app.known_of_leaked execution watcher id message seen identified
  rw [invoke, reports, FinDist.map_pure, FinDist.pure_bind,
    app.replay_reported execution watcher id packet known foreign fresh] at reached
  simp only [dispatch, Command.actor?, Execution.environmentStep, FinDist.map_pure,
    FinDist.pure_bind] at reached
  change next ∈ (FinDist.pure _).support at reached
  cases FinDist.mem_support_pure.mp reached
  have lookup := app.replay_lookup execution watcher id message found
  change (id, (app.handle execution.application message).isSome) ∈
    ((execution.respond app watcher ⟨some (.replay id)⟩).includePending app id).receipts ∧
      message ∈
        ((execution.respond app watcher ⟨some (.replay id)⟩).includePending app id).network.ledger
  simp only [Execution.includePending, MessageNetwork.includePending]
  rw [lookup]
  simp only [Execution.respond, MessageNetwork.replay, known]
  exact ⟨List.mem_append_right _ (List.mem_singleton_self _),
    List.mem_append_right _ (List.mem_singleton_self _)⟩

/-- A passive sample has an actual public receipt with at least the same
probability, even after arbitrary later responses and scheduling. The reporting
premise is local to the watcher's ordinary view at this activation. No sampling
or reporting premise is imposed on subsequent player activations. -/
theorem sampling_receipt_lower (players : Principal → app.Policy) (watcher : Principal)
    (execution : app.Execution) (id : MessageId Principal)
    (message : Message Principal app.Payload)
    (found : execution.network.lookup id = some message) (foreign : id.1 ≠ watcher)
    (unknown : (execution.network.known watcher).any (fun packet => packet.id = id) = false)
    (fresh : id ∉ execution.network.ledger.map Message.id)
    (reports : ∀ observed ∈ (execution.environmentStep app (.activate watcher)).support,
      message ∈ (observed.observe app watcher).messages.leaked →
        players watcher (observed.recall watcher) (observed.observe app watcher) =
          FinDist.pure ⟨some (.replay id)⟩)
    (scheduler : app.Scheduler) (count : Nat) :
    (app.observePending watcher execution.network.pending).probOf {selected | id ∈ selected} ≤
      ((app.reportInclusion players watcher execution).bind
        (app.runRounds scheduler players count)).probOf
          {final | (id, (app.handle execution.application message).isSome) ∈ final.receipts} := by
  classical
  rw [app.reportInclusion_law, FinDist.bind_bind,
    ← FinDist.expect_indicator_eq_probOf, ← FinDist.expect_indicator_eq_probOf,
    FinDist.expect_bind]
  apply FinDist.expect_mono
  intro selected supported
  let law := ((app.invoke players watcher (sampled app execution watcher selected)).bind
    fun reported => app.dispatch players
      (app.includeReported watcher (reported.observeEnvironment app)) reported).bind
        (app.runRounds scheduler players count)
  change (if id ∈ selected then (1 : ℝ) else 0) ≤ law.expect _
  by_cases chosen : id ∈ selected
  · have seen := app.sampled_leaked execution watcher id message found foreign unknown fresh
      selected chosen
    have reported := reports (sampled app execution watcher selected)
      (app.sampled_mem execution watcher selected supported) seen
    have observedLookup : (sampled app execution watcher selected).network.lookup id =
        some message := found
    have observedFresh : id ∉
        (sampled app execution watcher selected).network.ledger.map Message.id := fresh
    simp only [chosen, ↓reduceIte]
    calc
      (1 : ℝ) = law.expect (fun _ => 1) := (FinDist.expect_const law 1).symm
      _ ≤ _ := by
        apply FinDist.expect_mono
        intro final reached
        obtain ⟨recorded, included, continued⟩ :=
          Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
        have receipt := app.report_recorded players (sampled app execution watcher selected)
          watcher id message observedLookup foreign observedFresh seen reported recorded included
        have persists := (app.receipt_policyInvariant players
          (id, (app.handle execution.application message).isSome)).runRounds scheduler count
            recorded final receipt.1 continued
        simp only [Set.mem_ofPred_eq, persists, ↓reduceIte, le_refl]
  · simp only [chosen, ↓reduceIte]
    calc
      (0 : ℝ) = law.expect (fun _ => 0) := (FinDist.expect_const law 0).symm
      _ ≤ _ := FinDist.expect_mono (fun _ _ => by split <;> norm_num)

/-- A rejected report remains attributable after its payload becomes admissible
in a later phase. The receipt stores the result of this actual inclusion. This
does not prove that rejection is a sound reason to fine a compliant sender. -/
theorem sampling_rejected_receipt_lower (players : Principal → app.Policy) (watcher : Principal)
    (execution : app.Execution) (id : MessageId Principal)
    (message : Message Principal app.Payload)
    (found : execution.network.lookup id = some message) (foreign : id.1 ≠ watcher)
    (unknown : (execution.network.known watcher).any (fun packet => packet.id = id) = false)
    (fresh : id ∉ execution.network.ledger.map Message.id)
    (reports : ∀ observed ∈ (execution.environmentStep app (.activate watcher)).support,
      message ∈ (observed.observe app watcher).messages.leaked →
        players watcher (observed.recall watcher) (observed.observe app watcher) =
          FinDist.pure ⟨some (.replay id)⟩)
    (rejected : app.handle execution.application message = none)
    (scheduler : app.Scheduler) (count : Nat) :
    (app.observePending watcher execution.network.pending).probOf {selected | id ∈ selected} ≤
      ((app.reportInclusion players watcher execution).bind
        (app.runRounds scheduler players count)).probOf {final | (id, false) ∈ final.receipts} := by
  simpa only [rejected, Option.isSome_none] using
    app.sampling_receipt_lower players watcher execution id message found foreign unknown fresh
      reports scheduler count

/-- Static packet nonconformance can be audited even when the included
application call succeeds. The reported original author's ledger liability
survives every later policy and service choice. -/
theorem sampling_ledger_violation_lower (players : Principal → app.Policy) (watcher who : Principal)
    (permitted : app.Payload → Bool) (execution : app.Execution) (id : MessageId Principal)
    (message : Message Principal app.Payload)
    (found : execution.network.lookup id = some message) (foreign : id.1 ≠ watcher)
    (unknown : (execution.network.known watcher).any (fun packet => packet.id = id) = false)
    (fresh : id ∉ execution.network.ledger.map Message.id)
    (authored : message.sender = who) (nonconforming : permitted message.payload = false)
    (reports : ∀ observed ∈ (execution.environmentStep app (.activate watcher)).support,
      message ∈ (observed.observe app watcher).messages.leaked →
        players watcher (observed.recall watcher) (observed.observe app watcher) =
          FinDist.pure ⟨some (.replay id)⟩)
    (scheduler : app.Scheduler) (count : Nat) :
    (app.observePending watcher execution.network.pending).probOf {selected | id ∈ selected} ≤
      ((app.reportInclusion players watcher execution).bind
        (app.runRounds scheduler players count)).probOf
          {final | ledgerViolation who permitted final.network.ledger = true} := by
  classical
  rw [app.reportInclusion_law, FinDist.bind_bind,
    ← FinDist.expect_indicator_eq_probOf, ← FinDist.expect_indicator_eq_probOf,
    FinDist.expect_bind]
  apply FinDist.expect_mono
  intro selected supported
  let law := ((app.invoke players watcher (sampled app execution watcher selected)).bind
    fun reported => app.dispatch players
      (app.includeReported watcher (reported.observeEnvironment app)) reported).bind
        (app.runRounds scheduler players count)
  change (if id ∈ selected then (1 : ℝ) else 0) ≤ law.expect _
  by_cases chosen : id ∈ selected
  · have seen := app.sampled_leaked execution watcher id message found foreign unknown fresh
      selected chosen
    have reported := reports (sampled app execution watcher selected)
      (app.sampled_mem execution watcher selected supported) seen
    have observedLookup : (sampled app execution watcher selected).network.lookup id =
        some message := found
    have observedFresh : id ∉
        (sampled app execution watcher selected).network.ledger.map Message.id := fresh
    simp only [chosen, ↓reduceIte]
    calc
      (1 : ℝ) = law.expect (fun _ => 1) := (FinDist.expect_const law 1).symm
      _ ≤ _ := by
        apply FinDist.expect_mono
        intro final reached
        obtain ⟨recorded, included, continued⟩ :=
          Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
        have receipt := app.report_recorded players (sampled app execution watcher selected)
          watcher id message observedLookup foreign observedFresh seen reported recorded included
        have detected : ledgerViolation who permitted recorded.network.ledger = true :=
          (ledgerViolation_iff ..).mpr ⟨message, receipt.2, authored, nonconforming⟩
        have persists := app.ledgerViolation_continuation who permitted players scheduler count
          recorded final detected continued
        simp only [Set.mem_ofPred_eq, persists, ↓reduceIte, le_refl]
  · simp only [chosen, ↓reduceIte]
    calc
      (0 : ℝ) = law.expect (fun _ => 0) := (FinDist.expect_const law 0).symm
      _ ≤ _ := FinDist.expect_mono (fun _ _ => by split <;> norm_num)

end Interaction.ReactiveApplication
