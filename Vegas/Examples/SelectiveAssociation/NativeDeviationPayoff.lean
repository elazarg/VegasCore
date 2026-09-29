/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.NativeDeviation
import Vegas.Examples.SelectiveAssociation.GuessContinuation
import Vegas.Examples.SelectiveAssociation.Probability
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Expected utility of the actual selective-disclosure strategy

Carol's bound is unconditional in the opponents' raw behavioral policies.
Successful Alice and Bob publications are separate operational obligations;
the sequential-rationality argument supplies Bob's obligation.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open ReactiveAssociationEvidence

def nativeDeviationOutcomes (players : Player → nativeApp.Policy) (bit : Bool) :
    PMF Results :=
  ((players bob ((observed bit).recall bob) ((observed bit).observe nativeApp bob)).bind
    (nativeCarolPlay (nativeAliceProfile players) bit)).bind fun settled =>
      (nativeApp.runRounds nativeScheduler (nativeAliceProfile players) 76 settled).map
        (fun final => nativeResults final.application.config)

theorem native_deviation_outcome_law (players : Player → nativeApp.Policy) :
    (nativeApp.runRounds nativeScheduler (nativeAliceProfile players) nativeHorizon nativeRoot).map
        (fun final => nativeResults final.application.config) =
      (PMF.uniformOfFintype Bool).bind (nativeDeviationOutcomes players) := by
  change (nativeApp.runRounds nativeScheduler (nativeAliceProfile players) (13 + 76)
    nativeRoot).map _ = _
  rw [ReactiveApplication.runRounds_add, native_alice_thirteen_rounds,
    PMF.map_bind, PMF.bind_bind]
  rfl

theorem native_deviation_carol_bound (players : Player → nativeApp.Policy) (bit : Bool) :
    expect (nativeDeviationOutcomes players bit)
        (fun result => correctness (.success bit) result.carol) ≤
      expect (nativeCarolGuessLaw (nativeAliceProfile players)) (correctness (.success bit)) := by
  let changed := nativeAliceProfile players
  have each (prior : nativeApp.Action) :
      expect ((nativeCarolPlay changed bit prior).bind fun settled =>
        (nativeApp.runRounds nativeScheduler changed 76 settled).map
          (fun final => nativeResults final.application.config))
            (fun result => correctness (.success bit) result.carol) ≤
      expect (nativeCarolGuessLaw changed) (correctness (.success bit)) := by
    rw [FinDist.expect_bind]
    have bound : expect (nativeCarolPlay changed bit prior)
        (fun settled => expect ((nativeApp.runRounds nativeScheduler changed 76 settled).map
          (fun final => nativeResults final.application.config))
            (fun result => correctness (.success bit) result.carol)) ≤
      expect (nativeCarolPlay changed bit prior) (fun settled => correctness (.success bit)
        ((carolBindingRef.get? settled.application.config.store).getD .failure)) := by
      apply FinDist.expect_mono
      intro settled supported
      obtain ⟨response, _, settledMem⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨valid, guess, stored⟩ := native_carol_guess_stored changed bit prior response
        settled settledMem
      rw [expect_map, stored, Option.getD_some]
      exact native_carol_continuation_bound changed nativeScheduler 76 settled valid guess stored _
    apply bound.trans_eq
    rw [← expect_map]
    exact congrArg (fun law => expect law (correctness (.success bit)))
      (native_carol_common_law changed bit prior)
  unfold nativeDeviationOutcomes
  rw [PMF.bind_bind, FinDist.expect_bind]
  apply FinDist.expect_le_of_forall
  intro prior _
  exact each prior

theorem native_deviation_advantage (players : Player → nativeApp.Policy)
    (aliceSuccess : ∀ bit result, result ∈ (nativeDeviationOutcomes players bit).support →
      result.alice = .success bit)
    (bobSuccess : ∀ bit result, result ∈ (nativeDeviationOutcomes players bit).support →
      result.bob = .success bit) :
    1 / 2 ≤ expect (nativeApp.runRounds nativeScheduler (nativeAliceProfile players)
      nativeHorizon nativeRoot)
        (fun final => utility (nativeResults final.application.config) alice) := by
  have bound := selective_advantage (nativeDeviationOutcomes players)
    (nativeCarolGuessLaw (nativeAliceProfile players)) aliceSuccess bobSuccess
      (native_deviation_carol_bound players)
  have value := congrArg (fun law => expect law (fun result => utility result alice))
    (native_deviation_outcome_law players)
  rw [expect_map] at value
  exact value.symm ▸ bound

end Vegas.Examples.SelectiveAssociation
