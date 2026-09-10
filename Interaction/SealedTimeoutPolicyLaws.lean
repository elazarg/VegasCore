/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyLaws
import Interaction.SealedTimeoutApplication
import Interaction.SealedTimeoutLaws

/-! # Timed sealed policies on the shared message runner

The shared policy interface exposes receipts, the public clock and resolution,
wire observations, and each principal's own command history. The environment
cannot inspect the ideal commitment table. Its clock, delivery and inclusion
choices use that same runtime; no separate timed policy evaluator is defined.
-/

namespace Interaction.SealedTimeout

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- Every supported shared-policy outcome is exactly the timed native run of
its recorded actions. The trace is proof-facing, not an extra policy input. -/
theorem runPolicies_native_eq_run_trace
    (timed : SealedTimeout Principal)
    (players : Principal → (timed.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (timed.messageApplication (Value := Value)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (initial : State Principal Value)
    (execution : (timed.messageApplication (Value := Value)).PolicyExecution)
    (hmem : execution ∈ ((timed.messageApplication (Value := Value)).runPolicies
      players environment schedule
      (MessageApplication.PolicyExecution.initial _ (timed.toSharedState initial))).support) :
    execution.native = timed.toSharedState
      (timed.run initial (execution.nativeTrace.map (fromSharedAction timed))) := by
  have htrace := (timed.messageApplication (Value := Value)).runPolicies_initial_native_support
    players environment schedule (timed.toSharedState initial) execution hmem
  rw [run_shared_actions] at htrace
  exact FinDist.mem_support_pure.mp htrace

/-- An occupied ideal binding remains unchanged under every supported shared
policy execution, including expiration, malformed traffic, and replay. -/
theorem runPolicies_lookup_of_eq_some
    (timed : SealedTimeout Principal)
    (players : Principal → (timed.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (timed.messageApplication (Value := Value)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (initial : State Principal Value)
    (execution : (timed.messageApplication (Value := Value)).PolicyExecution)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (hlookup : initial.application.service.lookup handle = some value)
    (hmem : execution ∈ ((timed.messageApplication (Value := Value)).runPolicies
      players environment schedule
      (MessageApplication.PolicyExecution.initial _ (timed.toSharedState initial))).support) :
    execution.native.application.application.service.lookup handle = some value := by
  rw [runPolicies_native_eq_run_trace timed players environment schedule initial execution hmem]
  exact run_lookup_of_eq_some timed initial
    (execution.nativeTrace.map (fromSharedAction timed)) handle value hlookup

end Interaction.SealedTimeout
