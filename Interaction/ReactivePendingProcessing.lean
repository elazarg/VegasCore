/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveRounds

/-! # Processing a pending envelope without activating a player -/

noncomputable section

namespace Interaction.ReactiveApplication

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- Process the earliest pending envelope, or wait if none is pending. -/
def pendingHeadCommand (view : app.EnvironmentView) : app.Command :=
  match view.network.pending.head? with
  | none => .wait
  | some message => .include message.id

/-- One physical queue-processing step, including its scheduler recall. -/
def processPendingHead (execution : app.Execution) : app.Execution :=
  let command := app.pendingHeadCommand (execution.observeEnvironment app)
  let next := match execution.network.pending.head? with
    | none => execution
    | some message => execution.includePending app message.id
  { next with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, command⟩] }

theorem includePending_head (execution : app.Execution)
    (message : Message Principal app.Payload) (rest : List (Message Principal app.Payload))
    (pending : execution.network.pending = message :: rest) :
    (execution.includePending app message.id).network.pending = rest ∧
      (execution.includePending app message.id).network.ledger =
        execution.network.ledger ++ [message] ∧
      (execution.includePending app message.id).receipts = execution.receipts ++
        [(message.id, (app.handle execution.application message).isSome)] := by
  have found : execution.network.lookup message.id = some message := by
    simp [MessageNetwork.lookup, pending]
  simp [Execution.includePending, MessageNetwork.includePending, found, pending,
    MessagePool.removeFirst]

theorem processPendingHead_dispatch (players : Principal → app.Policy)
    (execution : app.Execution) :
    app.dispatch players (app.pendingHeadCommand (execution.observeEnvironment app)) execution =
      PMF.pure (app.processPendingHead execution) := by
  cases pending : execution.network.pending with
  | nil =>
      simp [pendingHeadCommand, processPendingHead, pending, dispatch, Execution.environmentStep,
        Command.actor?, resume, Execution.observeEnvironment, MessageNetwork.publicView]
  | cons message rest =>
      simp [pendingHeadCommand, processPendingHead, pending, dispatch, Execution.environmentStep,
        Command.actor?, resume, Execution.observeEnvironment, MessageNetwork.publicView]

theorem processPendingHead_recall (execution : app.Execution) :
    (app.processPendingHead execution).recall = execution.recall := by
  cases pending : execution.network.pending with
  | nil => simp [processPendingHead, pending]
  | cons message rest =>
      have found : execution.network.lookup message.id = some message := by
        simp [MessageNetwork.lookup, pending]
      simp [processPendingHead, pending, Execution.includePending, MessageNetwork.includePending,
        found]

theorem processPendingHead_environmentLength (execution : app.Execution) :
    (app.processPendingHead execution).environmentRecall.length =
      execution.environmentRecall.length + 1 := by
  simp [processPendingHead]

theorem processPendingHead_pending (execution : app.Execution) :
    (app.processPendingHead execution).network.pending = execution.network.pending.tail := by
  cases pending : execution.network.pending with
  | nil => simp [processPendingHead, pending]
  | cons message rest =>
      simp only [processPendingHead, pending, List.head?_cons, pendingHeadCommand]
      exact (app.includePending_head execution message rest pending).1

theorem processPendingHead_ledger (execution : app.Execution) :
    (app.processPendingHead execution).network.ledger = execution.network.ledger ++
      execution.network.pending.take 1 := by
  cases pending : execution.network.pending with
  | nil => simp [processPendingHead, pending]
  | cons message rest =>
      simpa only [processPendingHead, pending, List.head?_cons, List.take_succ_cons, List.take_zero]
        using (app.includePending_head execution message rest pending).2.1

/-- Iterating only the queue-processing command never consults player policies. -/
def processPendingBatch : Nat → app.Execution → app.Execution
  | 0, execution => execution
  | count + 1, execution => processPendingBatch count (app.processPendingHead execution)

theorem processPendingBatch_environmentLength (count : Nat) (execution : app.Execution) :
    (app.processPendingBatch count execution).environmentRecall.length =
      execution.environmentRecall.length + count := by
  induction count generalizing execution with
  | zero => simp [processPendingBatch]
  | succ count ih =>
      simp only [processPendingBatch, ih, processPendingHead_environmentLength]
      omega

theorem processPendingBatch_recall (count : Nat) (execution : app.Execution) :
    (app.processPendingBatch count execution).recall = execution.recall := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih => rw [processPendingBatch, ih, processPendingHead_recall]

theorem processPendingBatch_pending (count : Nat) (execution : app.Execution) :
    (app.processPendingBatch count execution).network.pending =
      execution.network.pending.drop count := by
  induction count generalizing execution with
  | zero => simp [processPendingBatch]
  | succ count ih =>
      rw [processPendingBatch, ih, processPendingHead_pending]
      cases execution.network.pending <;> simp

theorem processPendingBatch_ledger (count : Nat) (execution : app.Execution) :
    (app.processPendingBatch count execution).network.ledger = execution.network.ledger ++
      execution.network.pending.take count := by
  induction count generalizing execution with
  | zero => simp [processPendingBatch]
  | succ count ih =>
      rw [processPendingBatch, ih, processPendingHead_ledger, processPendingHead_pending]
      cases execution.network.pending <;> simp [List.append_assoc]

theorem processPendingHead_receipts_mono (execution : app.Execution) :
    execution.receipts ⊆ (app.processPendingHead execution).receipts := by
  cases pending : execution.network.pending with
  | nil => simp [processPendingHead, pending]
  | cons message rest =>
      simp only [processPendingHead, pending, List.head?_cons]
      rw [(app.includePending_head execution message rest pending).2.2]
      exact List.subset_append_left _ _

theorem processPendingBatch_receipts_mono (count : Nat) (execution : app.Execution) :
    execution.receipts ⊆ (app.processPendingBatch count execution).receipts := by
  induction count generalizing execution with
  | zero => exact List.Subset.refl _
  | succ count ih =>
      intro receipt present
      exact ih _ (app.processPendingHead_receipts_mono execution present)

/-- Every envelope removed by a processing batch has a real ledger receipt,
whether its application call succeeds or fails. -/
theorem processPendingBatch_receipt (count : Nat) (execution : app.Execution)
    (message : Message Principal app.Payload)
    (present : message ∈ execution.network.pending.take count) :
    ∃ accepted, (message.id, accepted) ∈ (app.processPendingBatch count execution).receipts := by
  induction count generalizing execution with
  | zero => simp at present
  | succ count ih =>
      cases pending : execution.network.pending with
      | nil => simp [pending] at present
      | cons first rest =>
          rw [pending, List.take_succ_cons, List.mem_cons] at present
          rcases present with same | later
          · subst message
            refine ⟨(app.handle execution.application first).isSome, ?_⟩
            apply app.processPendingBatch_receipts_mono count (app.processPendingHead execution)
            simp only [processPendingHead, pending, List.head?_cons]
            rw [(app.includePending_head execution first rest pending).2.2]
            simp
          · apply ih (app.processPendingHead execution)
            simpa only [processPendingHead_pending, pending, List.tail_cons] using later

end Interaction.ReactiveApplication
