/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveRounds

/-! # Service invariants along actual reactive rounds -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  {scheduler : app.Scheduler} {predicate : app.Execution → Prop}

namespace ServiceInvariant

theorem resume (invariant : app.ServiceInvariant scheduler predicate)
    (players : Principal → app.Policy) (actor : Option Principal) (execution next : app.Execution)
    (valid : predicate execution) (reached : next ∈ (app.resume players actor execution).support) :
    predicate next := by
  cases actor with
  | none =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | some who =>
      obtain ⟨action, _, rfl⟩ := PMF.support_map .. ▸ reached
      exact invariant.respond execution who action valid

theorem dispatch (invariant : app.ServiceInvariant scheduler predicate)
    (players : Principal → app.Policy) (command : app.Command) (execution next : app.Execution)
    (valid : predicate execution)
    (selected : command ∈ (scheduler execution.environmentRecall
      (execution.observeEnvironment app)).support)
    (reached : next ∈ (app.dispatch players command execution).support) : predicate next := by
  obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  exact invariant.resume players _ middle next
    (invariant.environment execution middle command valid selected moved) continued

theorem round (invariant : app.ServiceInvariant scheduler predicate)
    (players : Principal → app.Policy) (execution next : app.Execution)
    (valid : predicate execution)
    (reached : next ∈ (app.round scheduler players execution).support) :
    predicate next := by
  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  exact invariant.dispatch players command execution next valid selected moved

theorem runRounds (invariant : app.ServiceInvariant scheduler predicate)
    (players : Principal → app.Policy) (count : Nat) (execution next : app.Execution)
    (valid : predicate execution)
    (reached : next ∈ (app.runRounds scheduler players count execution).support) :
    predicate next := by
  induction count generalizing execution next with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | succ count ih =>
      obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact ih middle next (invariant.round players execution middle valid moved) continued

end ServiceInvariant
end Interaction.ReactiveApplication
