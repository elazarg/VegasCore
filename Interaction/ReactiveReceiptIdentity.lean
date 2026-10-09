/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveReceipts
import Interaction.ReactiveMessageIdentity

/-! # A published identifier has one permanent receipt

Every raw execution aligns its public receipts with its ledger. Since ledger
identifiers are distinct, a rejected identifier cannot later become accepted.
The facts hold for arbitrary application handlers and schedulers.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem receipt_identifiers_history (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) :
    control.execution.receipts.map Prod.fst =
      control.execution.network.ledger.map Message.id := by
  have sound := (app.receiptServiceInvariant (fun _ => True) (fun _ => True)
    ⟨by intros; trivial, by intros; trivial, by intros; trivial⟩
    (by intros; trivial) scheduler).history initial horizon
      (fun state _ => ⟨trivial, app.receiptsSound_initial (fun _ => True) state⟩) trace
  have paired : List.Forall₂ (fun message receipt => message.id = receipt.1)
      control.execution.network.ledger control.execution.receipts :=
    sound.2.imp (fun _ _ related => related.1.symm)
  have mapped : List.Forall₂ Eq (control.execution.network.ledger.map Message.id)
      (control.execution.receipts.map Prod.fst) :=
    (List.forall₂_map_left_iff.trans List.forall₂_map_right_iff).mpr paired
  have equal : control.execution.network.ledger.map Message.id =
      control.execution.receipts.map Prod.fst := by
    simpa only [List.forall₂_eq_eq_eq] using mapped
  exact equal.symm

theorem receipt_identifiers_distinct_history (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) :
    (control.execution.receipts.map Prod.fst).Nodup := by
  rw [app.receipt_identifiers_history initial horizon scheduler control trace]
  exact app.publishedOnce_history scheduler initial horizon trace

/-- A false receipt remains incompatible with a true receipt for that same
identifier, including after arbitrary future submissions and observations. -/
theorem rejected_identifier_not_accepted (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (id : MessageId Principal) (rejected : (id, false) ∈ control.execution.receipts) :
    (id, true) ∉ control.execution.receipts := by
  intro accepted
  have equal := List.inj_on_of_nodup_map
    (app.receipt_identifiers_distinct_history initial horizon scheduler control trace)
    rejected accepted rfl
  have impossible : false = true := congrArg Prod.snd equal
  cases impossible

end Interaction.ReactiveApplication
