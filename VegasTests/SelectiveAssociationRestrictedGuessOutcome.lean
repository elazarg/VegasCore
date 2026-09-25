/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedOutcome
import VegasTests.SelectiveAssociationPayoffs

/-! # Binding rewards in the complete native continuation

At a guesser's binding decision, Alice's binding is already fixed. Prescribed
opening publishes it even under a whole-policy deviation by that guesser.
The deviator's payoff is bounded by the correctness of its irrevocable binding;
the prescribed successful binding and opening attain this bound.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

def hasAliceBit (bit : Bool) (state : app.ProtocolState) : Prop :=
  state.elim False (fun control =>
    aliceBindingRef.get? control.execution.application.config.store = some (.success bit))

open Classical in
def guessReward (guess : PublicationResult Bool) (state : app.ProtocolState) : ℝ :=
  match guess with
  | .failure => 0
  | .success bit => if hasAliceBit bit state then 1 else 0

theorem guessReward_nonneg (guess : PublicationResult Bool) (state : app.ProtocolState) :
    0 ≤ guessReward guess state := by
  classical
  cases guess <;> simp only [guessReward]
  · exact le_rfl
  · split <;> norm_num

theorem guessReward_le_one (guess : PublicationResult Bool) (state : app.ProtocolState) :
    guessReward guess state ≤ 1 := by
  classical
  cases guess <;> simp only [guessReward]
  · norm_num
  · split <;> norm_num

theorem guessReward_of_binding (control : app.Control) (value guess : PublicationResult Bool)
    (stored : aliceBindingRef.get? control.execution.application.config.store = some value) :
    guessReward guess (some control) = correctness value guess := by
  classical
  cases value <;> cases guess <;> simp [guessReward, hasAliceBit, stored, correctness]

theorem alice_binding_at_guess (who : Player) (guesser : who ≠ alice)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativeBindingEvent who)) :
    ∃ value, aliceBindingRef.get? control.execution.application.config.store = some value := by
  have complete := earlier_completed (nativeBindingEvent who) aliceBinding
    (by fin_cases who <;> first | exact False.elim (guesser rfl) | decide)
    control trace (by rwa [native_binding_owner]) granted
  have field := (control.execution.application.config.output_available aliceBinding).mpr complete
  exact Option.isSome_iff_exists.mp (aliceBindingRef.get?_isSome _ field)

theorem guesser_utility (result : Results) (who : Player) (guesser : who ≠ alice) :
    utility result who = correctness result.alice (resultFor result who) -
      openingPenalty (resultFor result who) := by
  fin_cases who
  · exact False.elim (guesser rfl)
  · exact utility_bob result
  · exact utility_carol result

theorem utility_le_binding_correctness (who : Player) (guesser : who ≠ alice)
    (control : app.Control) (trace : arena.Trace (some control)) :
    nativeUtility who (some control) ≤ correctness (publication alice (some control))
      (((nativeBindingRef who).get? control.execution.application.config.store).getD .failure) := by
  change utility (nativeResults control.execution.application.config) who ≤ _
  rw [guesser_utility _ who guesser, nativeResults_for]
  change correctness (publication alice (some control))
      (((nativePublicationRef who).get? control.execution.application.config.store).getD .failure) -
        openingPenalty (((nativePublicationRef who).get?
          control.execution.application.config.store).getD .failure) ≤ _
  cases stored : (nativePublicationRef who).get? control.execution.application.config.store with
  | none =>
      simp only [Option.getD_none, correctness_failure_right, openingPenalty_failure]
      linarith [correctness_nonneg (publication alice (some control))
        (((nativeBindingRef who).get? control.execution.application.config.store).getD .failure)]
  | some value =>
      cases value with
      | failure =>
          simp only [Option.getD_some, correctness_failure_right, openingPenalty_failure]
          linarith [correctness_nonneg (publication alice (some control))
            (((nativeBindingRef who).get?
              control.execution.application.config.store).getD .failure)]
      | success bit =>
          have bound := native_publication_binding _ (native_history_reachable control trace)
            who bit stored
          simp only [bound, Option.getD_some, openingPenalty_success, sub_zero, le_refl]

theorem guesser_continuation_bound (who : Player) (guesser : who ≠ alice)
    (players : Profile model.behavioralSignature) (opens : Opens players alice)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativeBindingEvent who))
    (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom players (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support) :
    ∃ result, final.state = some result ∧ nativeUtility who final.state ≤
      guessReward (((nativeBindingRef who).get? result.execution.application.config.store).getD
        .failure) (some control) := by
  obtain ⟨value, stored⟩ := alice_binding_at_guess who guesser control trace active granted
  obtain ⟨result, stateEq, _⟩ := (binding_invariant alice value).behavioral_continuation menu
    (FinDist.pure nativeInitial) nativeHorizon scheduler players _ control trace final stored
      supported
  have published := publication_from_earlier_binding players (nativeBindingEvent who) alice
    (by fin_cases who <;> decide) control trace (by rwa [native_binding_owner]) granted value
    stored opens final supported
  refine ⟨result, stateEq, ?_⟩
  rcases final with ⟨state, finalTrace⟩
  change state = some result at stateEq
  subst state
  rw [guessReward_of_binding control value _ stored]
  rw [← published]
  exact utility_le_binding_correctness who guesser result finalTrace

theorem profile_guesser_payoff (who : Player) (guesser : who ≠ alice)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativeBindingEvent who))
    (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support) :
    nativeUtility who final.state = guessReward
      (.success (publicGuess (control.execution.observe app who))) (some control) := by
  obtain ⟨value, stored⟩ := alice_binding_at_guess who guesser control trace active granted
  have alicePublished := publication_from_earlier_binding profile (nativeBindingEvent who) alice
    (by fin_cases who <;> decide) control trace (by rwa [native_binding_owner]) granted value
    stored (profile_Opens alice) final supported
  obtain ⟨result, stateEq, bound⟩ := profile_binding_success who control trace active granted
    (2 * nativeHorizon + 1) (full_enough control trace) final supported
  have bitEq : prescribedBit who (control.execution.observe app who) =
      publicGuess (control.execution.observe app who) := by simp [prescribedBit, guesser]
  rw [bitEq] at bound
  have published := final_binding_published profile (nativeBindingEvent who) who
    (by fin_cases who <;> decide) control trace (by rwa [native_binding_owner]) granted
    (profile_Opens who) final supported result stateEq _ bound
  rw [stateEq]
  change utility (nativeResults result.execution.application.config) who = _
  rw [guesser_utility _ who guesser, nativeResults_for]
  change correctness (publication alice (some result)) (publication who (some result)) -
    openingPenalty (publication who (some result)) = _
  rw [← stateEq, published, alicePublished, openingPenalty_success, sub_zero,
    guessReward_of_binding control value _ stored]

end VegasTests.SelectiveAssociation.Restricted
