/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecall
import Interaction.ReactiveServiceInvariant
import Interaction.ReactivePublication
import Interaction.MessageNetworkCounters

/-! # Envelope serials count fresh own submissions

The network counter is determined by existing player recall. Silence,
passive reads and inclusion do not allocate a serial. This holds for arbitrary
raw responses and schedulers, independently of packet conformance.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

def Action.isSubmission (action : app.Action) : Bool :=
  match action.transmission with
  | some _ => true
  | none => false

def submissionCount (past : List app.PlayerEntry) : Nat :=
  past.countP fun entry => entry.action.isSubmission app

theorem submissionCount_append (first second : List app.PlayerEntry) :
    app.submissionCount (first ++ second) =
      app.submissionCount first + app.submissionCount second := by
  simp only [submissionCount, List.countP_append]

def Execution.SerialRecall (execution : app.Execution) : Prop :=
  ∀ who, execution.network.nextSerial who = app.submissionCount (execution.recall who)

theorem initial_serialRecall (state : app.State) :
    (Execution.initial app state).SerialRecall app := fun _ => rfl

variable [DecidableEq Principal]

theorem respond_serialRecall (execution : app.Execution) (who : Principal)
    (action : app.Action) (valid : execution.SerialRecall app) :
    (execution.respond app who action).SerialRecall app := by
  intro observer
  have earlier := valid observer
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      by_cases same : observer = who
      · subst observer
        simpa [Execution.respond, submissionCount, Action.isSubmission] using earlier
      · simpa [Execution.respond, same] using earlier
  | some submission =>
      by_cases same : observer = who
      · subst observer
        simpa [Execution.respond, MessageNetwork.submit, submissionCount,
          Action.isSubmission] using earlier
      · simpa [Execution.respond, MessageNetwork.submit, same] using earlier

theorem environment_serialRecall (execution next : app.Execution) (command : app.Command)
    (valid : execution.SerialRecall app)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.SerialRecall app := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact valid
  | «include» id =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      cases found : execution.network.lookup id <;>
        simpa [Execution.SerialRecall, Execution.includePending,
          MessageNetwork.includePending, found] using valid
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact valid

theorem serialRecallInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (fun execution => execution.SerialRecall app) where
  respond := app.respond_serialRecall
  environment execution next command valid _ reached :=
    app.environment_serialRecall execution next command valid reached

theorem serialRecall_history (scheduler : app.Scheduler) (initial : PMF app.State)
    (horizon : Nat) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => execution.SerialRecall app) state :=
  (app.serialRecallInvariant scheduler).history initial horizon
    (fun state _ => app.initial_serialRecall state) trace

/-- During a phase with no inclusion, the serial equals the settled baseline
exactly when no new own submission has occurred. The suffix may include any
number of waits. -/
theorem serial_eq_ledger_iff_no_submission
    (before after : app.Execution) (who : Principal)
    (beforeRecall : before.SerialRecall app) (afterRecall : after.SerialRecall app)
    (settled : before.network.nextSerial who =
      Message.distinctAuthoredCount before.network.ledger who)
    (ledger : after.network.ledger = before.network.ledger)
    (suffix : List app.PlayerEntry)
    (recalled : after.recall who = before.recall who ++ suffix) :
    after.network.nextSerial who =
        Message.distinctAuthoredCount after.network.ledger who ↔
      app.submissionCount suffix = 0 := by
  rw [afterRecall who, recalled, app.submissionCount_append, ← beforeRecall who, ledger,
    ← settled]
  omega

/-- A completed fresh submission restores the public serial test for the next
phase. The fact concerns network inclusion, so rejected application calls have
the same accounting as successful calls. -/
theorem submit_include_serials_match_ledger (execution : app.Execution)
    (serials : execution.network.SerialsBeforeNext)
    (who : Principal) (submission : app.Submission) (observer : Principal)
    (settled : execution.network.nextSerial observer =
      Message.distinctAuthoredCount execution.network.ledger observer) :
    let next := (execution.respond app who ⟨some submission⟩).includePending app
      (who, execution.network.nextSerial who)
    next.network.nextSerial observer =
      Message.distinctAuthoredCount next.network.ledger observer := by
  dsimp only
  rw [app.includePending_network]
  exact serials.submit_include_serials_match_ledger who
    (app.packet (app.submit execution.application who submission) who
      (execution.network.known who) submission) observer settled

/-- Every serial allocated to an author was emitted by one of its recorded
fresh submissions. -/
def Execution.SerialsIssued (execution : app.Execution) : Prop :=
  ∀ who serial, serial < execution.network.nextSerial who →
    ∃ entry ∈ execution.recall who, entry.action.isSubmission app = true ∧
      ∃ message, entry.emitted = some message ∧ message.id = (who, serial)

theorem respond_nextSerial (execution : app.Execution) (who observer : Principal)
    (action : app.Action) :
    (execution.respond app who action).network.nextSerial observer =
      execution.network.nextSerial observer +
        if observer = who ∧ action.isSubmission app = true then 1 else 0 := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => simp [Execution.respond, Action.isSubmission]
  | some submission =>
      by_cases same : observer = who
      · subst observer
        simp [Execution.respond, MessageNetwork.submit, Action.isSubmission]
      · simp [Execution.respond, MessageNetwork.submit, Action.isSubmission, same]

theorem environmentStep_nextSerial (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.network.nextSerial = execution.network.nextSerial := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | «include» id =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      cases found : execution.network.lookup id <;>
        simp [Execution.includePending, MessageNetwork.includePending, found]
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl

theorem respond_serialsIssued (execution : app.Execution) (who : Principal)
    (action : app.Action) (valid : execution.SerialsIssued app) :
    (execution.respond app who action).SerialsIssued app := by
  intro observer serial lower
  rw [app.respond_nextSerial] at lower
  by_cases fresh : observer = who ∧ action.isSubmission app = true ∧
      serial = execution.network.nextSerial who
  · obtain ⟨rfl, submits, rfl⟩ := fresh
    rcases action with ⟨transmission⟩
    rcases transmission with _ | submission
    · cases submits
    · refine ⟨⟨execution.observe app observer, ⟨some submission⟩,
        some (execution.network.submit observer (app.packet (app.submit execution.application
          observer submission) observer (execution.network.known observer) submission)).1⟩,
        ?_, rfl, _, rfl, rfl⟩
      simp [Execution.respond]
  · have old : serial < execution.network.nextSerial observer := by
      by_cases counted : observer = who ∧ action.isSubmission app = true
      · obtain ⟨same, submits⟩ := counted
        subst observer
        simp only [submits, and_self, ↓reduceIte] at lower
        have different : serial ≠ execution.network.nextSerial who :=
          fun equal => fresh ⟨rfl, submits, equal⟩
        omega
      · simpa only [counted, ↓reduceIte, Nat.add_zero] using lower
    obtain ⟨entry, member, submitted, message, emitted, identified⟩ := valid observer serial old
    exact ⟨entry, app.respond_recall_mono execution who observer action member, submitted,
      message, emitted, identified⟩

theorem serialsIssuedInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (fun execution => execution.SerialsIssued app) where
  respond := app.respond_serialsIssued
  environment execution next command valid _ reached := by
    intro who serial lower
    rw [app.environmentStep_nextSerial execution next command reached] at lower
    rw [app.environmentStep_recall execution next command reached]
    exact valid who serial lower

theorem serialsIssued_history (scheduler : app.Scheduler) (initial : PMF app.State)
    (horizon : Nat) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => execution.SerialsIssued app) state :=
  (app.serialsIssuedInvariant scheduler).history initial horizon
    (fun _ _ _ _ lower => (Nat.not_lt_zero _ lower).elim) trace

end Interaction.ReactiveApplication
