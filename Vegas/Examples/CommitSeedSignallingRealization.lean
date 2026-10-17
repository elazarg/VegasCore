/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingBudget
import Vegas.Examples.CommitSeedSignallingSeedTrace

/-! # Completion of the installed behavioral scheduler -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction

/-- The fixed native horizon completes every graph event for every raw legal
history under the scheduler actually installed in the runtime. -/
theorem scheduler_completesPlay :
    PhaseService.CompletesPlay runtime leaks initial horizon scheduler := by
  intro current trace terminal
  obtain ⟨seed, _supported, original⟩ := raw_trace_fixed_seed current trace
  exact family_completesPlay seed current original.some terminal

end Vegas.Examples.CommitSeedSignalling
