/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeServiceCompletion
import Vegas.Examples.LateOpeningRuntimeServiceDecision
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveAllocation
import Interaction.ReactiveReceipts
import Interaction.ReactiveRecallInvariant

/-! # Physical receipt guarantees for the late-opening service

Protected author turns consume the newly emitted authenticated envelope even
when its application call is rejected. These facts concern arbitrary raw
submissions and the actual native scheduler, rather than an assumed delivery
law or a restricted client policy.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeService

open SourceProgram EventGraph EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource

/-- The protected author selector includes a newly submitted envelope,
regardless of its addressed event, payload, or validity. -/
theorem latestAuthor_after_submit (execution : app.Execution) (who : Player)
    (submission : app.Submission) (serials : execution.network.SerialsBeforeNext) :
    latestAuthor who ((execution.respond app who ⟨some submission⟩).observeEnvironment app) =
      .include (who, execution.network.nextSerial who) := by
  have unpublished := serials.next_unpublished who
  unfold latestAuthor
  change (match (execution.network.pending ++ [(⟨(who, execution.network.nextSerial who),
      app.packet (app.submit execution.application who submission) who
        (execution.network.known who) submission⟩ : Message Player app.Payload)]).reverse.find?
      (fun message : Message Player app.Payload => decide (message.sender = who ∧
        message.id ∉ execution.network.ledger.map Message.id)) with
    | none => ReactiveApplication.Command.wait
    | some message => ReactiveApplication.Command.include message.id) = _
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.find?_cons, Message.sender, unpublished, not_false_eq_true,
    and_self, decide_true]

/-- An immediate protected author turn issues a receipt for every raw
submission, including one rejected by the application. -/
theorem latestAuthor_submit_receipt (execution next : app.Execution) (who : Player)
    (submission : app.Submission) (serials : execution.network.SerialsBeforeNext)
    (reached : next ∈ ((execution.respond app who ⟨some submission⟩).environmentStep app
      (latestAuthor who
        ((execution.respond app who ⟨some submission⟩).observeEnvironment app))).support) :
    ∃ accepted, ((who, execution.network.nextSerial who), accepted) ∈ next.receipts := by
  rw [latestAuthor_after_submit execution who submission serials] at reached
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
  cases (PMF.mem_support_pure_iff _ _).mp reached
  change ∃ accepted, ((who, execution.network.nextSerial who), accepted) ∈
    ((execution.respond app who ⟨some submission⟩).includePending app
      (who, execution.network.nextSerial who)).receipts
  have lookup := serials.lookup_submit who
    (app.packet (app.submit execution.application who submission) who
      (execution.network.known who) submission)
  change (execution.respond app who ⟨some submission⟩).network.lookup
    (who, execution.network.nextSerial who) = some _ at lookup
  unfold ReactiveApplication.Execution.includePending
  simp only [MessageNetwork.includePending, lookup]
  simp only [List.mem_append, List.mem_singleton]
  exact ⟨_, Or.inr rfl⟩

private def ReceiptAccounted (weight : ℝ) (nonnegative : 0 ≤ weight) :
    app.ProtocolState → Prop
  | none => True
  | some control => ∀ who entry, entry ∈ control.execution.recall who →
      ∀ message, entry.emitted = some message →
      (who = bob ∨ entry.beforeView.application.publicView.clock = 0) →
      (∃ accepted, (message.id, accepted) ∈ control.execution.receipts) ∨
        (control.actor = none ∧ ∃ (before : app.Execution) (submission : app.Submission),
          control.execution = before.respond app who ⟨some submission⟩ ∧
          before.network.SerialsBeforeNext ∧ message.id = (who, before.network.nextSerial who) ∧
          entry.beforeView.application.publicView.clock = control.execution.application.clock ∧
          scheduler weight nonnegative control.execution.environmentRecall
            (control.execution.observeEnvironment app) =
              PMF.pure (latestAuthor who (control.execution.observeEnvironment app)))

private theorem accounted_environment (weight : ℝ) (nonnegative : 0 ≤ weight)
    (remaining : Nat) (execution next : app.Execution) (command : app.Command)
    (accounted : ReceiptAccounted weight nonnegative (some ⟨remaining + 1, none, execution⟩))
    (selected : command ∈ (scheduler weight nonnegative execution.environmentRecall
      (execution.observeEnvironment app)).support)
    (reached : next ∈ (execution.environmentStep app command).support) :
    ReceiptAccounted weight nonnegative (some ⟨remaining, command.actor? app, next⟩) := by
  dsimp only [ReceiptAccounted] at accounted ⊢
  intro who entry member message emitted tracked
  rw [app.environmentStep_recall execution next command reached] at member
  rcases accounted who entry member message emitted tracked with received | outstanding
  · obtain ⟨accepted, caught⟩ := received
    exact Or.inl ⟨accepted,
      (app.environmentStep_receipts_prefix execution next command reached).subset caught⟩
  · obtain ⟨_, before, submission, responded, serials, identified, _, served⟩ := outstanding
    rw [served, PMF.mem_support_pure_iff] at selected
    subst command
    subst execution
    obtain ⟨accepted, caught⟩ := latestAuthor_submit_receipt before next who submission serials
      reached
    exact Or.inl ⟨accepted, by simpa only [identified] using caught⟩

private theorem accounted_response (weight : ℝ) (nonnegative : 0 ≤ weight)
    (remaining : Nat) (execution : app.Execution) (actor : Player) (action : app.Action)
    (accounted : ReceiptAccounted weight nonnegative (some ⟨remaining, some actor, execution⟩))
    (serials : execution.network.SerialsBeforeNext)
    (served : actor = bob ∨ execution.application.clock = 0 →
      scheduler weight nonnegative (execution.respond app actor action).environmentRecall
        ((execution.respond app actor action).observeEnvironment app) =
          PMF.pure (latestAuthor actor
            ((execution.respond app actor action).observeEnvironment app))) :
    ReceiptAccounted weight nonnegative
      (some ⟨remaining, none, execution.respond app actor action⟩) := by
  dsimp only [ReceiptAccounted] at accounted ⊢
  intro who entry member message emitted tracked
  by_cases old : entry ∈ execution.recall who
  · rcases accounted who entry old message emitted tracked with received | outstanding
    · obtain ⟨accepted, caught⟩ := received
      exact Or.inl ⟨accepted, (app.respond_receipts execution actor action).symm ▸ caught⟩
    · cases outstanding.1
  · have same : who = actor := by
      by_contra different
      rw [app.respond_recall_other execution actor who different action] at member
      exact old member
    subst who
    rcases action with ⟨transmission⟩
    cases transmission with
    | none =>
        simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
          List.mem_singleton] at member
        rcases member with prior | rfl
        · exact (old prior).elim
        · cases emitted
    | some submission =>
        simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit, ↓reduceIte,
          List.mem_append, List.mem_singleton] at member
        rcases member with prior | rfl
        · exact (old prior).elim
        · cases Option.some.inj emitted
          have condition : actor = bob ∨ execution.application.clock = 0 := tracked
          exact Or.inr ⟨rfl, execution, submission, rfl, serials, rfl,
            (runtime.reactive_respond_clock leaks execution actor ⟨some submission⟩).symm,
            served condition⟩

private theorem receipt_accounted_history (weight : ℝ) (nonnegative : 0 ≤ weight) :
    ∀ {state} (_trace : (app.protocol initial horizon (scheduler weight nonnegative)).Trace state),
      ReceiptAccounted weight nonnegative state
  | _, .start => trivial
  | _, @ExecutionProtocol.Trace.extend _ _ source target prior joint legal reached => by
      have inherited := receipt_accounted_history weight nonnegative prior
      change target ∈ (app.transition initial horizon (scheduler weight nonnegative)
        source joint).support at reached
      cases source with
      | none =>
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
          intro who entry member
          cases member
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact accounted_response weight nonnegative remaining execution who _ inherited
                (app.serialsBeforeNext_history (scheduler weight nonnegative) initial horizon prior)
                (fun tracked => protected_response_scheduler weight nonnegative
                  ⟨remaining, some who, execution⟩ prior who rfl _ tracked)
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  exact accounted_environment weight nonnegative remaining execution next command
                    inherited selected supported

/-- Every raw Bob output, and every raw Alice output sent at clock zero,
has an inclusion receipt once the public clock passes its send clock. -/
theorem protected_submission_receipt (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial horizon (scheduler weight nonnegative)).Trace (some control))
    (who : Player) (entry : app.PlayerEntry) (member : entry ∈ control.execution.recall who)
    (message : Message Player app.Payload) (emitted : entry.emitted = some message)
    (tracked : who = bob ∨ entry.beforeView.application.publicView.clock = 0)
    (later : entry.beforeView.application.publicView.clock < control.execution.application.clock) :
    ∃ accepted, (message.id, accepted) ∈ control.execution.receipts := by
  rcases receipt_accounted_history weight nonnegative trace who entry member message emitted
    tracked with received | outstanding
  · exact received
  · obtain ⟨_, _, _, _, _, _, sameClock, _⟩ := outstanding
    omega

/-- By the next active callback, every protected authored envelope has a
public receipt, including packets rejected by the application. -/
theorem protected_submission_receipt_of_active (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial horizon (scheduler weight nonnegative)).Trace (some control))
    (who : Player) (entry : app.PlayerEntry) (member : entry ∈ control.execution.recall who)
    (message : Message Player app.Payload) (emitted : entry.emitted = some message)
    (tracked : who = bob ∨ entry.beforeView.application.publicView.clock = 0)
    (active : control.actor ≠ none) :
    ∃ accepted, (message.id, accepted) ∈ control.execution.receipts := by
  rcases receipt_accounted_history weight nonnegative trace who entry member message emitted
    tracked with received | outstanding
  · exact received
  · exact (active outstanding.1).elim

/-- The actual all-raw scheduler supplies the asynchronous contract's
protected inclusion guarantee for every finite nonnegative lottery weight. -/
theorem inclusion (weight : ℝ) (nonnegative : 0 ≤ weight) :
    runtime.ProtectedInclusion leaks initial horizon (scheduler weight nonnegative) bound := by
  intro control trace event owner owned earlier later entry message splitRecall emitted
    _authored _addressed _ready _sole unfinished late
  have member : entry ∈ control.execution.recall owner := by rw [splitRecall]; simp
  change Fin 3 at event
  fin_cases event
  · change some alice = some owner at owned
    cases Option.some.inj owned
    by_cases zero : entry.beforeView.application.publicView.clock = 0
    · apply protected_submission_receipt weight nonnegative control trace alice entry member
        message emitted (Or.inr zero)
      change entry.beforeView.application.publicView.clock + 2 <
        control.execution.application.clock at late
      omega
    · have phase := completion_phase_history weight nonnegative control trace
      have beforeExpire : control.execution.environmentRecall.length < 11 := by
        by_contra past
        exact unfinished (phase.afterAlice (by omega)).1
      have clockBound : control.execution.application.clock ≤ 3 := by
        rw [clock_history weight nonnegative control trace]
        generalize located : control.execution.environmentRecall.length = cursor at beforeExpire ⊢
        interval_cases cursor <;> decide
      change entry.beforeView.application.publicView.clock + 2 <
        control.execution.application.clock at late
      omega
  · change some bob = some owner at owned
    cases Option.some.inj owned
    exact protected_submission_receipt weight nonnegative control trace bob entry member message
      emitted (Or.inl rfl) late
  · change some bob = some owner at owned
    cases Option.some.inj owned
    exact protected_submission_receipt weight nonnegative control trace bob entry member message
      emitted (Or.inl rfl) late

end Vegas.Examples.LateOpeningRuntimeService
