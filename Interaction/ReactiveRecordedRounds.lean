/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSchedulerTranscript
import Interaction.ReactiveServiceRounds
import Interaction.ReactiveResponseAccounting

/-! # Recorded environment entries retain actual round-prefix witnesses -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal Seed : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- Every command recorded by a fixed original seed is consistent with that
seed at its complete actual earlier recall. -/
theorem deterministic_transcript_invariant
    (choose : Seed → List app.EnvironmentEntry → app.EnvironmentView → app.Command)
    (seed : Seed) : app.ServiceInvariant (fun past view => PMF.pure (choose seed past view))
      (fun execution => app.commandConsistentFrom choose seed [] execution.environmentRecall) where
  respond execution who action valid := by
    rw [app.respond_environmentRecall]
    exact valid
  environment execution next command valid selected reached := by
    rw [app.environmentStep_environmentRecall execution next command reached,
      app.commandConsistent_snoc]
    exact ⟨valid, ((PMF.mem_support_pure_iff _ _).mp selected).symm⟩

end Interaction.ReactiveApplication
