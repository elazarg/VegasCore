/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.Publication

/-! # A settled guess bounds correctness throughout native continuations -/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

/-- After Carol's binding is settled, arbitrary further communication and
opening choices cannot increase its correctness. -/
theorem native_carol_continuation_bound (players : Player → nativeApp.Policy)
    (scheduler : nativeApp.Scheduler) (rounds : Nat) (execution : nativeApp.Execution)
    (valid : execution.application.Invariant nativeInputs) (guess : PublicationResult Bool)
    (stored : carolBindingRef.get? execution.application.config.store = some guess)
    (aliceResult : PublicationResult Bool) :
    expect (nativeApp.runRounds scheduler players rounds execution)
        (fun final => correctness aliceResult (nativeResults final.application.config).carol) ≤
      correctness aliceResult guess := by
  refine expect_le_const _ _ (payoffIntegrable_of_finite_summary _
    (fun final : nativeApp.Execution => (nativeResults final.application.config).carol)
    (correctness aliceResult)) _ fun final supported => ?_
  have invariant := (ReactiveApplication.Invariant.policyInvariant nativeApp
    (nativeRuntime.reactiveStateInvariant nativeLeaks nativeInputs) players).runRounds
      scheduler rounds execution final valid supported
  have fixed := (ReactiveApplication.Invariant.policyInvariant nativeApp
    (nativeRuntime.reactiveStoreInvariant nativeLeaks (.inr carolBinding) guess)
      players).runRounds scheduler rounds execution final stored supported
  change carolBindingRef.get? final.application.config.store = some guess at fixed
  have bound := native_publication_correctness_le final.application.config
    invariant.reachable carol aliceResult
  change correctness aliceResult (nativeResults final.application.config).carol ≤
    correctness aliceResult ((carolBindingRef.get? final.application.config.store).getD
      .failure) at bound
  simpa only [fixed, Option.getD_some] using bound

end Vegas.Examples.SelectiveAssociation
