/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.RestrictedPrescribedOutcome

/-! # Prelude continuations in the complete native game

Neither initial ambient response removes the later fresh binding correction.
The prescribed continuation from every legal prelude history publishes three
false values. Bob consequently reaches the maximum possible payoff there,
independently of the posterior and of Alice's earlier raw response.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

theorem prelude_position (who : Player) (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some who)
    (ambient : nativeTurnEvent? who (control.execution.recall who).length = none) :
    (who = alice ∧ control.remaining = 82 ∧ control.execution.environmentRecall.length = 1) ∨
      (who = bob ∧ control.remaining = 81 ∧ control.execution.environmentRecall.length = 2) := by
  obtain ⟨accounted, supported⟩ := menu.roundSupported_uniform (PMF.pure nativeInitial)
    nativeHorizon scheduler trace
  rw [active] at supported
  obtain ⟨count, prior, command, position, priorMem, commandMem, actor, observed⟩ := supported
  have cursor := app.roundsFrom_recall (PMF.pure nativeInitial) scheduler
    menu.uniformResponses count prior priorMem
  have bounded : count < nativePlan.length := by
    change _ + _ = nativePlan.length at accounted
    omega
  have selected : (nativePlan[count]?).bind nativeInstructionPlayer = some who := by
    simp only [serviceScheduler, cursor] at commandMem
    cases found : nativePlan[count]? with
    | none =>
        simp only [found, PMF.mem_support_pure_iff _ _] at commandMem
        subst command
        cases actor
    | some instruction =>
        rw [found] at commandMem
        simp only [Option.bind_some]
        exact (native_instruction_actor instruction _ _ command commandMem).symm.trans actor
  have positions : (count = 0 ∧ who = alice) ∨ (count = 1 ∧ who = bob) ∨
      ∃ event : nativeGraph.EventId,
        count = (nativeBeforeResponse event).length ∧ who = nativeOwner event := by
    have all : ∀ index : Fin nativePlan.length, ∀ player : Player,
        (nativePlan[index.val]?).bind nativeInstructionPlayer = some player →
          (index.val = 0 ∧ player = alice) ∨ (index.val = 1 ∧ player = bob) ∨
            ∃ event : nativeGraph.EventId,
              index.val = (nativeBeforeResponse event).length ∧ player = nativeOwner event := by
      decide
    exact all ⟨count, bounded⟩ who selected
  rcases positions with ⟨early, owner⟩ | ⟨early, owner⟩ | ⟨event, same, owner⟩
  · rw [native_horizon] at accounted
    exact Or.inl ⟨owner, by omega, by omega⟩
  · rw [native_horizon] at accounted
    exact Or.inr ⟨owner, by omega, by omega⟩
  · have turn := native_turn_of_decision_cursor (observation := leaks) event control trace
      (owner ▸ active) (same ▸ position)
    rw [turn.turnEvent?_of_active active] at ambient
    cases ambient

def preludeSteps (who : Player) : Nat := if who = alice then 4 else 2

theorem prelude_reaches_binding (players : Profile model.behavioralSignature) (who : Player)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some who)
    (ambient : nativeTurnEvent? who (control.execution.recall who).length = none)
    (later : arena.History)
    (supported : later ∈ (model.runBehavioralFrom players (preludeSteps who)
      ⟨some control, trace⟩).support) :
    ∃ result, later.state = some result ∧ result.actor = some alice ∧
      NativeTurn aliceBinding result := by
  have computed := native_behavioral_position (observation := leaks) players (preludeSteps who)
    ⟨some control, trace⟩ later supported
  change nativePosition later.state = nativeAdvancePosition^[preludeSteps who]
    (some (control.remaining, control.actor, control.execution.environmentRecall.length))
      at computed
  obtain ⟨rfl, remaining, cursor⟩ | ⟨rfl, remaining, cursor⟩ :=
    prelude_position who control trace active ambient
  all_goals
    rw [remaining, active, cursor] at computed
    change nativePosition later.state = some (80, some alice, 3) at computed
    rcases later with ⟨state, laterTrace⟩
    cases state with
    | none => cases computed
    | some result =>
        have fields := Option.some.inj computed
        have actor := congrArg (fun value : Nat × Option Player × Nat => value.2.1) fields
        have position := congrArg (fun value : Nat × Option Player × Nat => value.2.2) fields
        exact ⟨result, rfl, actor, native_turn_of_decision_cursor (observation := leaks)
          aliceBinding result laterTrace actor position⟩

theorem prescribed_prelude_results (who : Player) (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some who)
    (ambient : nativeTurnEvent? who (control.execution.recall who).length = none)
    (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support) :
    ∃ result, final.state = some result ∧ nativeResults result.execution.application.config =
      ⟨.success false, .success false, .success false⟩ := by
  have short : preludeSteps who ≤ 2 * nativeHorizon + 1 := by fin_cases who <;> decide
  rw [← Nat.add_sub_of_le short, model.runBehavioralFrom_add] at supported
  obtain ⟨later, laterMem, finalMem⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨atBinding, bindingEq, ownerActive, ownerGrant⟩ := prelude_reaches_binding profile who
    control trace active ambient later laterMem
  rcases later with ⟨state, laterTrace⟩
  change state = some atBinding at bindingEq
  subst state
  apply profile_alice_binding_results atBinding laterTrace ownerActive ownerGrant _ _ final finalMem
  rw [decision_rank aliceBinding atBinding laterTrace ownerActive ownerGrant]
  fin_cases who <;> decide

theorem bob_prelude_rational (assessment : model.BehavioralAssessment)
    (strategy : assessment.strategy = profile) (site : model.InformationSite bob)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (information : site.1 = some (past, view))
    (ambient : nativeTurnEvent? bob past.length = none) :
    assessment.IsSequentiallyRationalAt site (assessment.truncatedContinuationContext site
      (fun history => nativeUtility bob history.state) (2 * nativeHorizon + 1)) := by
  refine (Context.isLocallyOptimal_iff_of_integrable
    (nativeUtility_continuation_integrable assessment site _ _)
      fun _ _ => nativeUtility_continuation_integrable assessment site _ _).mpr
        fun alternative _ => ?_
  simp only [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    expect_bind_of_finite, strategy, Profile.update_eq_self]
  refine expect_mono (fun history _ => ?_) (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)
  obtain ⟨control, stateEq, active, recalled, _⟩ :=
    information_control bob past view ⟨history.1, history.2.trans information⟩
  rcases history with ⟨⟨state, trace⟩, historyInfo⟩
  change state = some control at stateEq
  subst state
  have controlAmbient : nativeTurnEvent? bob (control.execution.recall bob).length = none := by
    rw [recalled]
    exact ambient
  have prescribed : expect (model.runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩) (fun final => nativeUtility bob final.state) = 1 := by
    refine (expect_congr_on_support (g := fun _ => (1 : ℝ)) ?_).trans
      (expect_constant _ 1)
    intro final finalMem
    obtain ⟨result, finalEq, outcomes⟩ := prescribed_prelude_results bob control trace active
      controlAmbient final finalMem
    simp [nativeUtility, finalEq, outcomes, utility_bob, correctness]
  rw [prescribed]
  refine expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun final _ => ?_
  cases final.state with
  | none => change (0 : ℝ) ≤ 1; norm_num
  | some result => exact (utility_bob_bounds (nativeResults result.execution.application.config)).2

end Vegas.Examples.SelectiveAssociation.Restricted
