/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingRuntime
import Interaction.ReactiveSchedulerSeedTrace

/-! # Original supported scheduler seeds on every legal raw history -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- Every legal mixed-scheduler history, with arbitrary unbounded raw actions,
is the same physical control under an original supported scheduler seed.
The anchored response policy only witnesses this already recorded history. -/
theorem raw_trace_fixed_seed (current : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some current)) :
    ∃ seeds ∈ seedPrior.support,
      Nonempty ((app.protocol initial horizon (family seeds)).Trace (some current)) := by
  exact app.schedulerMixture_trace_fixed_seed seedPrior family initial horizon current trace

end Vegas.Examples.CommitSeedSignalling
