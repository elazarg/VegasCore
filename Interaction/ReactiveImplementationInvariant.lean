/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveImplementation
import Interaction.ReactiveServiceInvariant

/-! # Runtime invariants through actual private implementation runs

Unrestricted response obligations also apply to responses selected by a private
implementation. The actual joint evaluator carries its memory while preserving
the same service invariant at every supported execution, for arbitrary foreign
policies and the chosen observation-local scheduler.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  {Memory : Type} {predicate : app.Execution → Prop} {scheduler : app.Scheduler}

/-- One actual activation preserves unrestricted response invariants while
carrying the private implementation's real sampled memory. -/
theorem ServiceInvariant.implementation_resume
    (invariant : app.ServiceInvariant scheduler predicate)
    (implementation : app.Implementation Memory) (who : Principal)
    (players : Principal → app.Policy) (actor : Option Principal)
    (execution : app.Execution) (memory : Memory) (next : app.Execution × Memory)
    (valid : predicate execution)
    (reached : next ∈ (implementation.resume who players actor execution memory).support) :
    predicate next.1 := by
  cases actor with
  | none => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
  | some actor =>
      by_cases own : actor = who
      · subst actor
        simp only [Implementation.resume, ↓reduceIte] at reached
        obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ reached
        exact invariant.respond execution who response.1 valid
      · simp only [Implementation.resume, own, ↓reduceIte] at reached
        obtain ⟨updated, updatedMember, rfl⟩ := PMF.support_map .. ▸ reached
        obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ updatedMember
        exact invariant.respond execution actor response valid

/-- The original scheduler support and actual environment transition are
used before the implementation's activation; no replacement scheduler or
conditional invariant premise is introduced. -/
theorem ServiceInvariant.implementation_round
    (invariant : app.ServiceInvariant scheduler predicate)
    (implementation : app.Implementation Memory) (who : Principal)
    (players : Principal → app.Policy) (execution : app.Execution) (memory : Memory)
    (next : app.Execution × Memory) (valid : predicate execution)
    (reached : next ∈
      (implementation.round who players scheduler execution memory).support) :
    predicate next.1 := by
  obtain ⟨command, chosen, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  exact invariant.implementation_resume implementation who players _ middle memory next
    (invariant.environment execution middle command valid chosen moved) resumed

/-- Every prefix of the same private implementation's joint evaluator
preserves the invariant, including arbitrary continuations after a stopping
condition. Memory is carried by the actual evaluator rather than reselected. -/
theorem ServiceInvariant.implementation_runJoint
    (invariant : app.ServiceInvariant scheduler predicate)
    (implementation : app.Implementation Memory) (who : Principal)
    (players : Principal → app.Policy) (count : Nat) (execution : app.Execution) (memory : Memory)
    (next : app.Execution × Memory) (valid : predicate execution)
    (reached : next ∈
      (implementation.runJoint who players scheduler count execution memory).support) :
    predicate next.1 := by
  induction count generalizing execution memory with
  | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
  | succ count ih =>
      obtain ⟨middle, stepped, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact ih middle.1 middle.2
        (invariant.implementation_round implementation who players execution memory middle
          valid stepped) tail

end Interaction.ReactiveApplication
