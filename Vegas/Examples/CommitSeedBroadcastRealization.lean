/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastBudget
import Interaction.ReactiveSchedulerSeedTrace

/-! # The original mixed service shares the checked raw completion bound -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction
open GameTheory.Math.Probability

/-- A genuine initialized mixed history is the identical physical control
under one supported seed from the original prior. -/
theorem raw_trace_fixed_seed (current : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some current)) :
    ∃ seed ∈ nativeSeedLaw.support,
      Nonempty ((app.protocol initial horizon (family seed)).Trace (some current)) := by
  exact app.schedulerMixture_trace_fixed_seed nativeSeedLaw family initial horizon current
    trace

/-- The actually installed scheduler completes all graph events under every
legal raw continuation before the environment horizon runs out. -/
theorem scheduler_completesPlay :
    PhaseService.CompletesPlay runtime leaks initial horizon scheduler := by
  intro current trace terminal
  obtain ⟨seed, _supported, original⟩ := raw_trace_fixed_seed current trace
  exact family_completesPlay seed current original.some terminal

end Vegas.Examples.CommitSeedBroadcast
