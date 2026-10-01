/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.RestrictedGuessSegment
import Vegas.Examples.SelectiveAssociation.RestrictedPrelude

/-! # Alice cannot separate the prescribed guessers without a leak

The two prescribed guessers use the same public evidence. Carol's intervening
fresh binding adds no certificate, and Alice has no response between their
binding visits. Thus their final publications coincide under every complete
Alice policy, including policies that publish certificates in earlier packets.
Alice's reward is then at most zero, the prescribed continuation reward.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

theorem update_binds_other (who other : Player) (different : other ≠ who)
    (alternative : model.BehavioralPolicy who) (past : List app.PlayerEntry)
    (view : app.PlayerView)
    (granted : nativeTurnEvent? other past.length = some (nativeBindingEvent other)) :
    menu.decodeProfile (PMF.pure nativeInitial) nativeHorizon scheduler
      (Profile.update (sig := model.behavioralSignature) profile who alternative) other past view =
        PMF.pure (correctiveBinding other (nativeBindingEvent other)
          (prescribedBit other view) view) := by
  rw [menu.decodeProfile_update, Function.update_of_ne different, decode_profile]
  exact congrArg PMF.pure (response_binds other past view granted)

theorem alice_carol_payoff_bound (alternative : model.BehavioralPolicy alice)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some carol)
    (granted : NativeTurn carolBinding control)
    (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom
      (Profile.update (sig := model.behavioralSignature) profile alice alternative)
        (2 * nativeHorizon + 1) ⟨some control, trace⟩).support) :
    nativeUtility alice final.state ≤ 0 := by
  let players := Profile.update (sig := model.behavioralSignature) profile alice alternative
  let bit := publicGuess (control.execution.observe app carol)
  have chooses := update_binds_other alice carol (by decide) alternative
    (control.execution.recall carol) (control.execution.observe app carol)
    (granted.turnEvent?_of_active active)
  change menu.decodeProfile (PMF.pure nativeInitial) nativeHorizon scheduler players carol
    (control.execution.recall carol) (control.execution.observe app carol) =
      PMF.pure (correctiveBinding carol carolBinding bit
        (control.execution.observe app carol)) at chooses
  obtain ⟨result, stateEq, carolBound⟩ := binding_success players carol control trace active granted
    bit chooses _ (full_enough control trace) final supported
  have split := supported
  change final ∈ (model.runBehavioralFrom players (6 + 161) ⟨some control, trace⟩).support at split
  rw [model.runBehavioralFrom_add] at split
  obtain ⟨later, laterMem, finalMem⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ split)
  have exactLater := afterCarol_history players control trace active granted _ chooses later
    laterMem
  obtain ⟨bobControl, bobEq, bobActive, bobGrant⟩ := future_decision players carolBinding bobBinding
    (by decide) control trace active granted later laterMem
  change bobControl.actor = some bob at bobActive
  have exactControl := Option.some.inj (bobEq.symm.trans exactLater)
  have sameGuess : publicGuess (bobControl.execution.observe app bob) = bit := by
    rw [exactControl]
    exact afterCarol_guess control trace active granted bit
  rcases later with ⟨laterState, laterTrace⟩
  change laterState = some bobControl at bobEq
  subst laterState
  have bobChooses := update_binds_other alice bob (by decide) alternative
    (bobControl.execution.recall bob) (bobControl.execution.observe app bob)
    (bobGrant.turnEvent?_of_active bobActive)
  have prescribed : prescribedBit bob (bobControl.execution.observe app bob) = bit := by
    simpa only [prescribedBit, show bob ≠ alice by decide, ↓reduceIte] using sameGuess
  rw [prescribed] at bobChooses
  have enough : app.rank nativeHorizon (some bobControl) ≤ 161 := by
    rw [decision_rank bobBinding bobControl laterTrace bobActive bobGrant]
    decide
  obtain ⟨sameResult, sameEq, bobBound⟩ := binding_success players bob bobControl laterTrace
    bobActive bobGrant bit bobChooses 161 enough final finalMem
  have same : sameResult = result := Option.some.inj (sameEq.symm.trans stateEq)
  subst sameResult
  have carolPublished := final_binding_published players carolBinding carol (by decide)
    control trace active granted (update_opens_other alice carol (by decide) alternative)
      final supported result stateEq bit carolBound
  have bobPublished := final_binding_published players carolBinding bob (by decide)
    control trace active granted (update_opens_other alice bob (by decide) alternative)
      final supported result stateEq bit bobBound
  have equalResults : (nativeResults result.execution.application.config).bob =
      (nativeResults result.execution.application.config).carol := by
    change resultFor (nativeResults result.execution.application.config) bob =
      resultFor (nativeResults result.execution.application.config) carol
    rw [nativeResults_for, nativeResults_for]
    change publication bob (some result) = publication carol (some result)
    rw [← stateEq, bobPublished, carolPublished]
  rw [stateEq]
  change utility (nativeResults result.execution.application.config) alice ≤ 0
  rw [utility_alice, equalResults, sub_self]
  cases (nativeResults result.execution.application.config).alice <;> norm_num [openingPenalty]

theorem alice_binding_payoff_bound (alternative : model.BehavioralPolicy alice)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some alice)
    (granted : NativeTurn aliceBinding control)
    (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom
      (Profile.update (sig := model.behavioralSignature) profile alice alternative)
        (2 * nativeHorizon + 1) ⟨some control, trace⟩).support) :
    nativeUtility alice final.state ≤ 0 := by
  let players := Profile.update (sig := model.behavioralSignature) profile alice alternative
  change final ∈ (model.runBehavioralFrom players (5 + 162) ⟨some control, trace⟩).support
    at supported
  rw [model.runBehavioralFrom_add] at supported
  obtain ⟨later, laterMem, finalMem⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨atCarol, carolEq, carolActive, carolGrant⟩ := future_decision players aliceBinding
    carolBinding (by decide) control trace active granted later laterMem
  change atCarol.actor = some carol at carolActive
  rcases later with ⟨state, laterTrace⟩
  change state = some atCarol at carolEq
  subst state
  have enough : app.rank nativeHorizon (some atCarol) ≤ 162 := by
    rw [decision_rank carolBinding atCarol laterTrace carolActive carolGrant]
    decide
  obtain ⟨other, otherMem, same⟩ := full_continuation_state players atCarol laterTrace 162 enough
    final finalMem
  rw [← same]
  exact alice_carol_payoff_bound alternative atCarol laterTrace carolActive carolGrant other
    otherMem

theorem alice_prelude_payoff_bound (alternative : model.BehavioralPolicy alice)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some alice)
    (ambient : nativeTurnEvent? alice (control.execution.recall alice).length = none)
    (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom
      (Profile.update (sig := model.behavioralSignature) profile alice alternative)
        (2 * nativeHorizon + 1) ⟨some control, trace⟩).support) :
    nativeUtility alice final.state ≤ 0 := by
  let players := Profile.update (sig := model.behavioralSignature) profile alice alternative
  change final ∈ (model.runBehavioralFrom players (4 + 163) ⟨some control, trace⟩).support
    at supported
  rw [model.runBehavioralFrom_add] at supported
  obtain ⟨later, laterMem, finalMem⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨atBinding, bindingEq, ownerActive, ownerGrant⟩ := prelude_reaches_binding players alice
    control trace active ambient later laterMem
  rcases later with ⟨state, laterTrace⟩
  change state = some atBinding at bindingEq
  subst state
  have enough : app.rank nativeHorizon (some atBinding) ≤ 163 := by
    rw [decision_rank aliceBinding atBinding laterTrace ownerActive ownerGrant]
    decide
  obtain ⟨other, otherMem, same⟩ := full_continuation_state players atBinding laterTrace 163 enough
    final finalMem
  rw [← same]
  exact alice_binding_payoff_bound alternative atBinding laterTrace ownerActive ownerGrant other
    otherMem

theorem alice_early_rational (assessment : model.BehavioralAssessment)
    (strategy : assessment.strategy = profile) (site : model.InformationSite alice)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (information : site.1 = some (past, view))
    (early : nativeTurnEvent? alice past.length = none ∨
      nativeTurnEvent? alice past.length = some aliceBinding) :
    assessment.IsSequentiallyRationalAt site (assessment.truncatedContinuationContext site
      (fun history => nativeUtility alice history.state) (2 * nativeHorizon + 1)) := by
  refine (Context.isLocallyOptimal_iff_of_integrable
    (nativeUtility_continuation_integrable assessment site _ _)
      fun _ _ => nativeUtility_continuation_integrable assessment site _ _).mpr
        fun alternative _ => ?_
  simp only [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    expect_bind_of_finite, strategy, Profile.update_eq_self]
  refine expect_mono (fun history _ => ?_) (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)
  obtain ⟨control, stateEq, active, recalled, _⟩ :=
    information_control alice past view ⟨history.1, history.2.trans information⟩
  rcases history with ⟨⟨state, trace⟩, historyInfo⟩
  change state = some control at stateEq
  subst state
  have current : nativeTurnEvent? alice (control.execution.recall alice).length = none ∨
      NativeTurn aliceBinding control := by
    rw [← recalled] at early
    exact early.imp id (.of_turnEvent? active)
  have prescribed : expect (model.runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩) (fun final => nativeUtility alice final.state) = 0 := by
    refine (expect_congr_on_support (g := fun _ => (0 : ℝ)) ?_).trans
      (expect_constant _ 0)
    intro final finalMem
    rcases current with ambient | granted
    · obtain ⟨result, finalEq, outcomes⟩ := prescribed_prelude_results alice control trace active
        ambient final finalMem
      simp [nativeUtility, finalEq, outcomes, utility_alice, correctness]
    · exact profile_alice_binding_payoff alice control trace active granted _
        (full_enough control trace) final finalMem
  rw [prescribed]
  refine expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun final finalMem => ?_
  rcases current with ambient | granted
  · exact alice_prelude_payoff_bound alternative control trace active ambient final finalMem
  · exact alice_binding_payoff_bound alternative control trace active granted final finalMem

end Vegas.Examples.SelectiveAssociation.Restricted
