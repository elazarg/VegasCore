/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveQuiescent
import Interaction.ReactiveRounds

/-! # Arbitrary response windows containing only published replays

This uses the existing round evaluator. At a checkpoint with no unpublished
pending envelope, any finite window of activations and waits preserves the
application and every player's current observation when responses are silence
or replay of a published identifier. The observation rule is unrestricted.

The conclusion retains no equality of private action recall, pending copies,
network inputs or scheduler history. Those records really do change. It is an
operational lemma for inserting communication opportunities, not an equilibrium
quotient or a claim that arbitrary schedulers ignore rebroadcasts.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- Silence and replay of already published traffic have the same immediate
application effect and current player observations, while preserving cleanliness. -/
theorem respond_published (execution : app.Execution) (who : Principal) (action : app.Action)
    (published : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (permitted : action = ⟨none⟩ ∨ ∃ id ∈ execution.network.ledger.map Message.id,
      action = ⟨some (.replay id)⟩) :
    (execution.respond app who action).application = execution.application ∧
      (execution.respond app who action).receipts = execution.receipts ∧
      (∀ observer, (execution.respond app who action).observe app observer =
        execution.observe app observer) ∧
      (∀ message ∈ (execution.respond app who action).network.pending,
        message.id ∈ (execution.respond app who action).network.ledger.map Message.id) := by
  rcases permitted with rfl | ⟨id, spent, rfl⟩
  · exact ⟨rfl, rfl, fun _ => rfl, published⟩
  · have clean := execution.network.replay_pending_published who id published spent
    refine ⟨?_, ?_, ?_, clean⟩
    · cases found : (execution.network.known who).find? (fun message => message.id = id) <;>
        simp only [Execution.respond, MessageNetwork.replay, found]
    · cases found : (execution.network.known who).find? (fun message => message.id = id) <;>
        simp only [Execution.respond, MessageNetwork.replay, found]
    · intro observer
      cases found : (execution.network.known who).find? (fun message => message.id = id) <;>
        simp only [Execution.respond, MessageNetwork.replay, found, Execution.observe,
          MessageNetwork.observe]

private theorem dispatch_published (players : Principal → app.Policy)
    (responses : ∀ who past view action, action ∈ (players who past view).support →
      action = ⟨none⟩ ∨ ∃ id ∈ view.messages.ledger.map Message.id,
        action = ⟨some (.replay id)⟩)
    (execution next : app.Execution) (command : app.Command)
    (published : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (permitted : command = .wait ∨ ∃ who, command = .activate who)
    (reached : next ∈ (app.dispatch players command execution).support) :
    next.application = execution.application ∧ next.receipts = execution.receipts ∧
      (∀ observer, next.observe app observer = execution.observe app observer) ∧
      (∀ message ∈ next.network.pending, message.id ∈ next.network.ledger.map Message.id) := by
  rcases permitted with rfl | ⟨who, rfl⟩
  · simp only [dispatch, Execution.environmentStep, FinDist.map_pure, FinDist.pure_bind,
      Command.actor?, resume] at reached
    cases FinDist.mem_support_pure.mp reached
    exact ⟨rfl, rfl, fun _ => rfl, published⟩
  · rw [dispatch, execution.activate_of_pending_published app who published] at reached
    simp only [FinDist.pure_bind, Command.actor?, resume, invoke] at reached
    obtain ⟨action, supported, rfl⟩ := FinDist.support_map .. ▸ reached
    exact app.respond_published _ who action published (responses who _ _ action supported)

/-- An arbitrary finite sequence of activation/wait choices preserves clean
application state and all current player views. The scheduler may adapt to the
actual replay input history, and every activation uses the original leak rule. -/
theorem runRounds_published (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (commands : ∀ past view command, command ∈ (scheduler past view).support →
      command = .wait ∨ ∃ who, command = .activate who)
    (responses : ∀ who past view action, action ∈ (players who past view).support →
      action = ⟨none⟩ ∨ ∃ id ∈ view.messages.ledger.map Message.id,
        action = ⟨some (.replay id)⟩)
    (count : Nat) (execution next : app.Execution)
    (published : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (reached : next ∈ (app.runRounds scheduler players count execution).support) :
    next.application = execution.application ∧ next.receipts = execution.receipts ∧
      (∀ observer, next.observe app observer = execution.observe app observer) ∧
      (∀ message ∈ next.network.pending, message.id ∈ next.network.ledger.map Message.id) := by
  induction count generalizing execution with
  | zero =>
      cases FinDist.mem_support_pure.mp reached
      exact ⟨rfl, rfl, fun _ => rfl, published⟩
  | succ count ih =>
      obtain ⟨middle, stepped, continued⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨command, selected, stepped⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ stepped)
      obtain ⟨stateEq, receiptsEq, observed, clean⟩ :=
        app.dispatch_published players responses execution middle command published
          (commands _ _ command selected) stepped
      obtain ⟨finalState, finalReceipts, finalObserved, finalClean⟩ :=
        ih middle clean continued
      exact ⟨finalState.trans stateEq, finalReceipts.trans receiptsEq,
        fun observer => (finalObserved observer).trans (observed observer), finalClean⟩

/-- In particular, adding such a window does not randomize the application
configuration. Private response recall and audit traffic are still retained. -/
theorem runRounds_published_application (scheduler : app.Scheduler)
    (players : Principal → app.Policy)
    (commands : ∀ past view command, command ∈ (scheduler past view).support →
      command = .wait ∨ ∃ who, command = .activate who)
    (responses : ∀ who past view action, action ∈ (players who past view).support →
      action = ⟨none⟩ ∨ ∃ id ∈ view.messages.ledger.map Message.id,
        action = ⟨some (.replay id)⟩)
    (count : Nat) (execution : app.Execution)
    (published : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id) :
    (app.runRounds scheduler players count execution).map Execution.application =
      FinDist.pure execution.application := by
  calc
    _ = (app.runRounds scheduler players count execution).map
        (fun _ => execution.application) := by
      apply FinDist.map_congr_of_eq_on_support
      intro next supported
      exact (app.runRounds_published scheduler players commands responses count
        execution next published supported).1
    _ = _ := FinDist.map_const _ _

end Interaction.ReactiveApplication
