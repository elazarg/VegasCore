/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeServiceOpportunity
import Vegas.Examples.LateOpeningRuntimeServiceReceipt
import Vegas.Examples.LateOpeningRuntimeServiceErasure
import Vegas.Examples.LateOpeningRuntimeCoverage
import Vegas.Game.AsyncServiceSpec

/-! # The actual public two-late builder meets the asynchronous service contract

The protected author service, recurring owner callbacks and forced expiry are
proved for every unrestricted raw history. The late lottery is also blind to
packet deletion and renaming over every public view, for every finite weight.
This service certificate does not itself assert sequential-equilibrium
preservation or exclusion.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeService

open LateOpeningRuntimeSource

/-- Every finite nonnegative lottery weight gives an actual public builder
with protected service, bounded reaction opportunities and complete play. -/
theorem contract (weight : ℝ) (nonnegative : 0 ≤ weight) :
    runtime.AsyncContract leaks initial horizon (scheduler weight nonnegative) delay bound :=
  ⟨opportunity weight nonnegative, inclusion weight nonnegative, completes weight nonnegative⟩

/-- The same actual builder simultaneously supplies the full raw-history
service certificate and the all-view late-packet blindness certificate. -/
theorem contract_and_blind (weight : ℝ) (nonnegative : 0 ≤ weight) :
    runtime.AsyncContract leaks initial horizon (scheduler weight nonnegative) delay bound ∧
      runtime.BlindToLatePackets leaks bound (scheduler weight nonnegative) :=
  ⟨contract weight nonnegative, LateOpeningRuntimeServiceErasure.scheduler_blind weight nonnegative⟩

/-- The compiled source and concrete public builder form an instance of the
existing asynchronous compiler interface, with all its side conditions proved. -/
def service (weight : ℝ) (nonnegative : 0 ≤ weight) : AsyncServiceSpec Player simpleExpr where
  setup := setup
  mode := .sequential
  deadline := deadline
  leaks := leaks
  bounds := bounds
  values := binding_values_covered
  initialValues := initial_values_covered
  capacity := candidate_capacity
  horizon := horizon
  scheduler := scheduler weight nonnegative
  delay := delay
  bound := bound
  contract := contract weight nonnegative
  timely := timely
  initialFinite := inferInstance
  leaksFinite := inferInstance
  schedulerFinite past view := stageChoice_support_finite weight nonnegative past.length view

end Vegas.Examples.LateOpeningRuntimeService
