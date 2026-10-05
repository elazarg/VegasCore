/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.PendingPriority

/-! # Priority selection after inclusion and a fresh submission

One envelope is submitted and included; a second remains pending. Stable
identifier priorities select the remaining envelope, and a fresh submission
does not take precedence over it. These are exact network selection laws, not
an application or proper-subgame counterexample.
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

theorem old_selection :
    MessageNetwork.priorityPending (PMF.pure priority) eligible pending.pending =
      PMF.pure (some ((), 1)) := by
  have chosen : PriorityChoice.choose priority
      (MessageNetwork.eligibleIds eligible pending.pending) = some ((), 1) := by decide
  simp only [MessageNetwork.priorityPending, PriorityChoice.law, PMF.pure_map, chosen]

theorem fresh_selection (value : Nat) :
    MessageNetwork.priorityPending (PMF.pure priority) eligible
      (pending.submit () value).2.pending = PMF.pure (some ((), 1)) := by
  have chosen : PriorityChoice.choose priority
      (MessageNetwork.eligibleIds eligible (pending.submit () value).2.pending) =
        some ((), 1) := by
    change PriorityChoice.choose priority {((), 1), ((), 2)} = some ((), 1)
    decide
  simp only [MessageNetwork.priorityPending, PriorityChoice.law, PMF.pure_map, chosen]

end InteractionTests.PendingPriority
