/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.PendingPriority

/-! # Why replay invariance needs candidate retention

One envelope is submitted and included; a second remains pending. Stable
identifier priorities prefer the removed envelope if it is rebroadcast.
A fresh submission does not have that priority. These are exact network
selection laws, not an application or proper-subgame counterexample.
-/

noncomputable section

namespace InteractionTests.PendingPriority

open Interaction GameTheory.Math.Probability

def eligible : Message Unit Nat → Bool := fun _ => true

abbrev priority : LinearOrder (MessageId Unit) :=
  LinearOrder.lift' Prod.snd (fun _ _ same => Prod.ext (Subsingleton.elim _ _) same)

def submitted : MessageNetwork Unit Nat := (MessageNetwork.empty.submit () 1).2
def removed : MessageNetwork Unit Nat := (submitted.includePending ((), 0)).2
def pending : MessageNetwork Unit Nat := (removed.submit () 2).2

theorem not_retained : ¬pending.RetainsEligible eligible := by
  intro retained
  have member := retained () ⟨((), 0), 1⟩ (by
    change (⟨((), 0), 1⟩ : Message Unit Nat) ∈
      [⟨((), 0), 1⟩, ⟨((), 1), 2⟩] ++ [] ++ [⟨((), 0), 1⟩]
    simp) rfl
  have absent : ((), 0) ∉ MessageNetwork.eligibleIds eligible pending.pending := by decide
  exact absent member

theorem old_selection :
    MessageNetwork.priorityPending (FinDist.pure priority) eligible pending.pending =
      FinDist.pure (some ((), 1)) := by
  have chosen : PriorityChoice.choose priority
      (MessageNetwork.eligibleIds eligible pending.pending) = some ((), 1) := by decide
  simp only [MessageNetwork.priorityPending, PriorityChoice.law, FinDist.map_pure, chosen]

theorem fresh_selection (value : Nat) :
    MessageNetwork.priorityPending (FinDist.pure priority) eligible
      (pending.submit () value).2.pending = FinDist.pure (some ((), 1)) := by
  have chosen : PriorityChoice.choose priority
      (MessageNetwork.eligibleIds eligible (pending.submit () value).2.pending) =
        some ((), 1) := by
    change PriorityChoice.choose priority {((), 1), ((), 2)} = some ((), 1)
    decide
  simp only [MessageNetwork.priorityPending, PriorityChoice.law, FinDist.map_pure, chosen]

theorem replay_selection :
    MessageNetwork.priorityPending (FinDist.pure priority) eligible
      (pending.replay () ((), 0)).2.pending = FinDist.pure (some ((), 0)) := by
  have chosen : PriorityChoice.choose priority
      (MessageNetwork.eligibleIds eligible (pending.replay () ((), 0)).2.pending) =
        some ((), 0) := by decide
  simp only [MessageNetwork.priorityPending, PriorityChoice.law, FinDist.map_pure, chosen]

end InteractionTests.PendingPriority
