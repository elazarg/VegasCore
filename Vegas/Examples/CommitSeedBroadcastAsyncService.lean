/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOpportunity
import Vegas.Examples.CommitSeedBroadcastProtected
import Vegas.Examples.CommitSeedBroadcastRealization

/-! # The complete raw asynchronous contract of the concrete scheduler -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction

/-- Each original fixed-seed scheduler satisfies all three raw service
requirements on arbitrary legal submissions, with delay zero and bound five. -/
theorem family_asyncContract (seeds : Seeds) :
    PhaseService.AsyncContract runtime leaks initial horizon (family seeds)
      (fun _ => 0) (fun _ => 5) where
  opportunity := family_opportunity seeds
  inclusion := family_protected_inclusion seeds
  completes := family_completesPlay seeds

/-- The actual initialized behavioral scheduler has the same all-raw service
contract. Supported original seeds realize the same complete physical control. -/
theorem scheduler_asyncContract :
    PhaseService.AsyncContract runtime leaks initial horizon scheduler
      (fun _ => 0) (fun _ => 5) where
  opportunity := by
    intro current trace
    obtain ⟨seeds, _supported, fixed⟩ := raw_trace_fixed_seed current trace
    exact family_opportunity seeds current fixed.some
  inclusion := by
    intro current trace
    obtain ⟨seeds, _supported, fixed⟩ := raw_trace_fixed_seed current trace
    exact family_protected_inclusion seeds current fixed.some
  completes := scheduler_completesPlay

end Vegas.Examples.CommitSeedBroadcast
