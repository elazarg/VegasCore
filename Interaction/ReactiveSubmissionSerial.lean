/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecall
import Interaction.ReactiveServiceInvariant

/-! # Envelope serials count fresh own submissions

The network counter is determined by existing player recall. Silence, replays,
passive reads and inclusion do not allocate a serial. This holds for arbitrary
raw responses and schedulers, independently of packet conformance.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

def Action.isSubmission (action : app.Action) : Bool :=
  match action.transmission with
  | some (.submit _) => true
  | none | some (.replay _) => false

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
  | some transmission =>
      cases transmission with
      | submit submission =>
          by_cases same : observer = who
          · subst observer
            simpa [Execution.respond, MessageNetwork.submit, submissionCount,
              Action.isSubmission] using earlier
          · simpa [Execution.respond, MessageNetwork.submit, same] using earlier
      | replay id =>
          cases known : (execution.network.known who).find? (fun message => message.id = id)
          all_goals by_cases same : observer = who
          all_goals first
            | subst observer
              simpa [Execution.respond, MessageNetwork.replay, known, submissionCount,
                Action.isSubmission] using earlier
            | simpa [Execution.respond, MessageNetwork.replay, known, same] using earlier

theorem environment_serialRecall (execution next : app.Execution) (command : app.Command)
    (valid : execution.SerialRecall app)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.SerialRecall app := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact valid
  | «include» id =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      cases found : execution.network.lookup id <;>
        simpa [Execution.SerialRecall, Execution.includePending,
          MessageNetwork.includePending, found] using valid
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact valid

theorem serialRecallInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (fun execution => execution.SerialRecall app) where
  respond := app.respond_serialRecall
  environment execution next command valid _ reached :=
    app.environment_serialRecall execution next command valid reached

theorem serialRecall_history (scheduler : app.Scheduler) (initial : FinDist app.State)
    (horizon : Nat) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => execution.SerialRecall app) state :=
  (app.serialRecallInvariant scheduler).history initial horizon
    (fun state _ => app.initial_serialRecall state) trace

/-- During a phase with no inclusion, the serial equals the settled baseline
exactly when no new own submission has occurred. The suffix may include any
number of waits and replays. -/
theorem serial_eq_ledger_iff_no_submission
    (before after : app.Execution) (who : Principal)
    (beforeRecall : before.SerialRecall app) (afterRecall : after.SerialRecall app)
    (settled : before.network.nextSerial who =
      before.network.ledger.countP (fun message => message.sender = who))
    (ledger : after.network.ledger = before.network.ledger)
    (suffix : List app.PlayerEntry)
    (recalled : after.recall who = before.recall who ++ suffix) :
    after.network.nextSerial who =
        after.network.ledger.countP (fun message => message.sender = who) ↔
      app.submissionCount suffix = 0 := by
  rw [afterRecall who, recalled, app.submissionCount_append, ← beforeRecall who, ledger,
    ← settled]
  omega

end Interaction.ReactiveApplication
