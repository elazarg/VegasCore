/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveServiceMixture
import Interaction.ReactiveServiceRounds

/-! # Original scheduler support throughout supported round continuations -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal Seed : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}

/-- A continuation only narrows the original scheduler seed support. This is
pointwise along supported physical outcomes, without a conditional-prior premise. -/
theorem schedulerMixture_posterior_support_runRounds
    (prior : PMF Seed) (family : Seed → app.Scheduler) (players : Principal → app.Policy)
    (count : Nat) (before after : app.Execution)
    (reached : after ∈ (app.runRounds (app.schedulerMixture prior family).scheduler
      players count before).support) (seed : Seed)
    (supported : seed ∈ ((app.schedulerMixture prior family).posterior
      after.environmentRecall).support) :
    seed ∈ ((app.schedulerMixture prior family).posterior before.environmentRecall).support := by
  let predicate : Seed → app.Execution → Prop := fun original _ =>
    original ∈ ((app.schedulerMixture prior family).posterior before.environmentRecall).support
  have constant (original : Seed) : app.ServiceInvariant (family original)
      (predicate original) := {
    respond := fun _ _ _ valid => valid
    environment := fun _ _ _ valid _ _ => valid }
  have invariant := ServiceInvariant.schedulerMixture app prior family predicate constant
  exact invariant.runRounds players count before after (fun _ valid => valid)
    reached seed supported

end Interaction.ReactiveApplication
