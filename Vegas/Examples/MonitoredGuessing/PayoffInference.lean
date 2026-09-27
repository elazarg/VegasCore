/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.Payoffs
import Vegas.Examples.MonitoredGuessing.PayoffBounds
import GameTheoryExtensions.Analysis.EnforcementSynthesis

/-! # Computing a native disclosure charge from declared source payoffs

The finite integer return table supplies an executable sender payoff range.
The generic rational checker uses the native monitor's proved one-half
collection probability. Its inferred charge bounds every initial submission
and every raw continuation by the smallest declared sender payoff after opening.

This certifies the early-transmission comparison. A complete equilibrium
theorem additionally needs ordinary source choices to be rational, including
final opening and the receiver's decision. No such rationality is assumed or
claimed here.
-/

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory.Enforcement

def allResults : Finset Results :=
  (Finset.univ : Finset (PublicationResult Bool × PublicationResult Bool)).image
    (fun pair => ⟨pair.1, pair.2⟩)

theorem mem_allResults (result : Results) : result ∈ allResults := by
  exact Finset.mem_image.mpr ⟨(result.alice, result.bob), Finset.mem_univ _, rfl⟩

def senderValues (table : PayoffTable) : Finset Int :=
  allResults.image (fun result => table result alice)

theorem senderValues_nonempty (table : PayoffTable) : (senderValues table).Nonempty :=
  ⟨_, Finset.mem_image_of_mem _ (mem_allResults ⟨.failure, .failure⟩)⟩

def senderOpeningValues (table : PayoffTable) : Finset Int :=
  (Finset.univ : Finset (Bool × Bool)).image (fun pair =>
    table ⟨.success pair.1, if pair.2 then .success true else .failure⟩ alice)

theorem senderOpeningValues_nonempty (table : PayoffTable) :
    (senderOpeningValues table).Nonempty :=
  ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (false, false))⟩

def senderLower (table : PayoffTable) : Int :=
  (senderOpeningValues table).min' (senderOpeningValues_nonempty table)

def senderUpper (table : PayoffTable) : Int :=
  (senderValues table).max' (senderValues_nonempty table)

theorem senderLower_le (table : PayoffTable) (bit guess : Bool) :
    senderLower table ≤ table ⟨.success bit, if guess then .success true else .failure⟩ alice := by
  exact Finset.min'_le (senderOpeningValues table) _
    (Finset.mem_image_of_mem _ (Finset.mem_univ (bit, guess)))

theorem le_senderUpper (table : PayoffTable) (result : Results) :
    table result alice ≤ senderUpper table := by
  exact Finset.le_max' (senderValues table) _
    (Finset.mem_image_of_mem (fun result => table result alice) (mem_allResults result))

def inferredCharge (table : PayoffTable) : Option ℚ :=
  inferScalarDeposit {()} (fun _ => (senderUpper table - senderLower table : Int))
    (fun _ => 1 / 2)

theorem inferredCharge_returns (table : PayoffTable) :
    inferredCharge table = some (scalarDeposit {()}
      (fun _ => (senderUpper table - senderLower table : Int)) (fun _ => 1 / 2)) := by
  simp [inferredCharge, inferScalarDeposit]

theorem inferredCharge_bounds (table : PayoffTable) {charge : ℚ}
    (inferred : inferredCharge table = some charge) :
    (0 : ℝ) ≤ charge ∧ 2 * ((senderUpper table : ℝ) - senderLower table) ≤ charge := by
  obtain ⟨nonnegative, sound⟩ := inferred_deposit_sound {()}
    (fun _ => ((senderUpper table - senderLower table : Int) : ℚ)) (fun _ => 1 / 2)
    (by intros; norm_num) inferred
  have bound := sound () (Finset.mem_singleton_self ())
  push_cast at bound
  constructor
  · exact_mod_cast nonnegative
  · linarith

/-- This is a bound in the actual monitored native execution, not merely
soundness of the numerical certificate. -/
theorem inferredCharge_deters (table : PayoffTable) {charge : ℚ}
    (inferred : inferredCharge table = some charge)
    (bit : Bool) (submission : WitnessedSubmission nativeGraph)
    (players : Player → nativeApp.Policy) (plan : List (ServiceInstruction nativeGraph)) :
    ((monitoredPrefixLaw bit (submissionAction submission)).bind
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan)).expect
        (monitoredSettlement (fun result => table result alice) charge) ≤ senderLower table := by
  obtain ⟨nonnegative, sufficient⟩ := inferredCharge_bounds table inferred
  apply submission_deterred_by_range (fun result => table result alice)
    (senderLower table) (senderUpper table) charge _ nonnegative sufficient
  intro result
  exact_mod_cast le_senderUpper table result

/-- The bound is below every mixture of ordinary guesses followed by Alice's
opening, including a receiver policy chosen in response to the payoff table. -/
theorem inferredCharge_deters_against_opening (table : PayoffTable) {charge : ℚ}
    (inferred : inferredCharge table = some charge) (guesses : FinDist Bool)
    (bit : Bool) (submission : WitnessedSubmission nativeGraph)
    (players : Player → nativeApp.Policy) (plan : List (ServiceInstruction nativeGraph)) :
    ((monitoredPrefixLaw bit (submissionAction submission)).bind
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan)).expect
        (monitoredSettlement (fun result => table result alice) charge) ≤
      guesses.expect (fun guess =>
        (table ⟨.success bit, if guess then .success true else .failure⟩ alice : ℝ)) := by
  apply (inferredCharge_deters table inferred bit submission players plan).trans
  rw [← FinDist.expect_const guesses (senderLower table : ℝ)]
  apply FinDist.expect_mono
  intro guess _
  exact_mod_cast senderLower_le table bit guess

/-- The original correctness table recovers the native pilot's deposit two. -/
example : inferredCharge (fun result who =>
    if who = alice then match result.alice with
      | .failure => -4
      | .success bit => if bit = result.bob.isSuccess then 1 else 0
    else 0) = some 2 := by decide +kernel

end Vegas.Examples.MonitoredGuessing
