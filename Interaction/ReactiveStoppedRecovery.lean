module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveRecovery
public import Interaction.ReactiveMixtureRounds

@[expose] public section

/-! # Recovery policies through a stopping time -/

noncomputable section

namespace Interaction.ReactiveApplication

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}

/-- From consistent recall, attaching any recovery policy to each player preserves the
complete execution law stopped at any predicate. -/
theorem Policy.recover_runUntil (players recovery : Principal → app.Policy)
    (scheduler : app.Scheduler) (stop : app.Execution → Prop) [DecidablePred stop]
    (count : Nat) (execution : app.Execution)
    (valid : ∀ who, (players who).Consistent (execution.logs who)) :
    app.runUntil scheduler (fun who => (players who).recover (recovery who)) stop count execution =
      app.runUntil scheduler players stop count execution := by
  have invariant := consistentRecall_policyInvariant players
  symm
  apply app.runUntil_congr_of_agree scheduler players _ stop
    (fun current => ∀ who, (players who).Consistent (current.logs who)) _ _ count execution valid
  · intro current consistent _ command _ middle moved who _
    exact ((players who).recover_eq (recovery who) _ _
      (invariant.environment current middle command consistent moved who)).symm
  · intro current consistent _ next reached
    obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
    exact invariant.dispatch command current next consistent moved

end Interaction.ReactiveApplication
