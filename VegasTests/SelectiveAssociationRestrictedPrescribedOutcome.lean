/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedOutcome

/-! # Prescribed completion after Alice's binding response

Alice's fresh correction selects false even after an arbitrary prelude.
Sound evidence then excludes a true public guess at every later guesser
binding. All three prescribed bindings and publications consequently succeed
with false. This is an execution theorem, independent of beliefs.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

theorem profile_alice_binding_results_full (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some alice)
    (granted : control.execution.application.serviceGrant = some aliceBinding)
    (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support) :
    ∃ result, final.state = some result ∧ nativeResults result.execution.application.config =
      ⟨.success false, .success false, .success false⟩ := by
  obtain ⟨result, stateEq, aliceFalse⟩ := profile_binding_success alice control trace active granted
    _ (full_enough control trace) final supported
  change aliceBindingRef.get? result.execution.application.config.store = some (.success false)
    at aliceFalse
  have allBound : ∀ who : Player, (nativeBindingRef who).get?
      result.execution.application.config.store = some (.success false) := by
    intro who
    by_cases same : who = alice
    · subst who
      exact aliceFalse
    · have ordered : aliceBinding.val ≤ (nativeBindingEvent who).val := by fin_cases who <;> decide
      have short : decisionSteps aliceBinding (nativeBindingEvent who) ≤ 2 * nativeHorizon + 1 := by
        fin_cases who <;> decide
      have split := supported
      rw [← Nat.add_sub_of_le short, model.runBehavioralFrom_add] at split
      obtain ⟨later, laterMem, finalMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ split)
      obtain ⟨atBinding, bindingEq, ownerActive, ownerGrant⟩ := future_decision profile aliceBinding
        (nativeBindingEvent who) ordered control trace active granted later laterMem
      rw [native_binding_owner] at ownerActive
      rcases later with ⟨laterState, laterTrace⟩
      change laterState = some atBinding at bindingEq
      subst laterState
      have before : (nativeBindingEvent alice).val < (nativeBindingEvent who).val := by
        fin_cases who <;> first | exact (same rfl).elim | decide
      have fixed := binding_from_final profile (nativeBindingEvent who) alice before atBinding
        laterTrace (by rwa [native_binding_owner]) ownerGrant _ final finalMem result stateEq
          (.success false) aliceFalse
      have guess := publicGuess_false_of_alice_false who atBinding laterTrace ownerActive fixed
      have enough : app.rank nativeHorizon (some atBinding) ≤
          2 * nativeHorizon + 1 - decisionSteps aliceBinding (nativeBindingEvent who) := by
        rw [decision_rank (nativeBindingEvent who) atBinding laterTrace
          (by rwa [native_binding_owner]) ownerGrant]
        fin_cases who <;> decide
      obtain ⟨corrected, correctedEq, correctedBinding⟩ := profile_binding_success who atBinding
        laterTrace ownerActive ownerGrant _ enough final finalMem
      have identical : corrected = result := Option.some.inj (correctedEq.symm.trans stateEq)
      subst corrected
      simpa only [prescribedBit, ite_eq_right same, guess] using correctedBinding
  have allPublished : ∀ who : Player, publication who final.state = .success false := by
    intro who
    exact final_binding_published profile aliceBinding who (by fin_cases who <;> decide)
      control trace active granted (profile_Opens who) final supported result stateEq false
        (allBound who)
  refine ⟨result, stateEq, ?_⟩
  have aliceResult := allPublished alice
  have bobResult := allPublished bob
  have carolResult := allPublished carol
  simp only [publication, stateEq, Option.elim_some] at aliceResult bobResult carolResult
  change (alicePublicationRef.get? result.execution.application.config.store).getD .failure =
    .success false at aliceResult
  change (bobPublicationRef.get? result.execution.application.config.store).getD .failure =
    .success false at bobResult
  change (carolPublicationRef.get? result.execution.application.config.store).getD .failure =
    .success false at carolResult
  change Results.mk _ _ _ = _
  rw [aliceResult, bobResult, carolResult]

theorem profile_alice_binding_results (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some alice)
    (granted : control.execution.application.serviceGrant = some aliceBinding)
    (fuel : Nat) (enough : app.rank nativeHorizon (some control) ≤ fuel)
    (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom profile fuel ⟨some control, trace⟩).support) :
    ∃ result, final.state = some result ∧ nativeResults result.execution.application.config =
      ⟨.success false, .success false, .success false⟩ := by
  obtain ⟨other, otherMem, same⟩ := full_continuation_state profile control trace fuel enough final
    supported
  obtain ⟨result, stateEq, outcomes⟩ := profile_alice_binding_results_full control trace active
    granted other otherMem
  exact ⟨result, same.symm.trans stateEq, outcomes⟩

theorem profile_alice_binding_payoff (who : Player) (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some alice)
    (granted : control.execution.application.serviceGrant = some aliceBinding)
    (fuel : Nat) (enough : app.rank nativeHorizon (some control) ≤ fuel)
    (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom profile fuel ⟨some control, trace⟩).support) :
    nativeUtility who final.state = if who = alice then 0 else 1 := by
  obtain ⟨result, stateEq, outcomes⟩ := profile_alice_binding_results control trace active granted
    fuel enough final supported
  simp only [nativeUtility, stateEq, Option.elim_some, outcomes]
  fin_cases who <;> norm_num [utility, correctness, openingPenalty, alice, bob, carol]

theorem initialized_results (final : arena.History)
    (supported : final ∈ (model.runBehavioral profile (2 * nativeHorizon + 1)).support) :
    ∃ result, final.state = some result ∧ nativeResults result.execution.application.config =
      ⟨.success false, .success false, .success false⟩ := by
  change final ∈ (model.runBehavioralFrom profile (7 + 172) arena.initHistory).support at supported
  rw [model.runBehavioralFrom_add] at supported
  obtain ⟨later, laterMem, finalMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  have position := native_behavioral_position (observation := leaks) profile 7 arena.initHistory
    later laterMem
  have advance : nativeAdvancePosition^[7] (nativePosition arena.initHistory.state) =
      some (85, some alice, 4) := by decide
  rw [advance] at position
  rcases later with ⟨state, laterTrace⟩
  cases state with
  | none => cases position
  | some control =>
      have fields := Option.some.inj position
      have remaining := congrArg (fun value : Nat × Option Player × Nat => value.1) fields
      have active := congrArg (fun value : Nat × Option Player × Nat => value.2.1) fields
      have cursor := congrArg (fun value : Nat × Option Player × Nat => value.2.2) fields
      change control.remaining = 85 at remaining
      change control.actor = some alice at active
      change control.execution.environmentRecall.length = 4 at cursor
      have granted := native_grant_of_decision_cursor (observation := leaks) aliceBinding control
        laterTrace active cursor
      apply profile_alice_binding_results control laterTrace active granted 172 _ final finalMem
      change 2 * control.remaining + (if control.actor.isSome then 1 else 0) ≤ 172
      rw [remaining, active]
      decide

/-- Exact initialized utility law, for the utility returned by the shared
source program. This execution theorem does not assert sequential equilibrium. -/
theorem initialized_payoff_law (who : Player) :
    (model.runBehavioral profile (2 * nativeHorizon + 1)).map
      (fun history => nativeUtility who history.state) =
        FinDist.pure (if who = alice then 0 else 1) := by
  apply FinDist.eq_pure_of_support_subset_singleton
  intro value supported
  obtain ⟨final, finalMem, rfl⟩ := FinDist.support_map .. ▸ supported
  obtain ⟨result, stateEq, outcomes⟩ := initialized_results final finalMem
  simp only [nativeUtility, stateEq, Option.elim_some, outcomes]
  fin_cases who <;> norm_num [utility, correctness, openingPenalty, alice, bob, carol]

end VegasTests.SelectiveAssociation.Restricted
