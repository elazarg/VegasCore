/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedPrescribedOutcome

/-! # Prelude continuations in the complete native game

Neither initial ambient response removes the later fresh binding correction.
The prescribed continuation from every legal prelude history publishes three
false values. Bob consequently reaches the maximum possible payoff there,
independently of the posterior and of Alice's earlier raw response.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

theorem prelude_position (who : Player) (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some who)
    (ambient : control.execution.application.serviceGrant = none) :
    (who = alice ∧ control.remaining = 88 ∧ control.execution.environmentRecall.length = 1) ∨
      (who = bob ∧ control.remaining = 87 ∧ control.execution.environmentRecall.length = 2) := by
  obtain ⟨accounted, supported⟩ := menu.roundSupported_uniform (FinDist.pure nativeInitial)
    nativeHorizon scheduler trace
  rw [active] at supported
  obtain ⟨count, prior, command, position, priorMem, commandMem, actor, observed⟩ := supported
  have cursor := app.roundsFrom_recall (FinDist.pure nativeInitial) scheduler
    menu.uniformResponses count prior priorMem
  have bounded : count < nativePlan.length := by
    change _ + _ = nativePlan.length at accounted
    omega
  have selected : (nativePlan[count]?).bind nativeInstructionPlayer = some who := by
    simp only [serviceScheduler, cursor] at commandMem
    cases found : nativePlan[count]? with
    | none =>
        simp only [found, FinDist.mem_support_pure] at commandMem
        subst command
        cases actor
    | some instruction =>
        rw [found] at commandMem
        simp only [Option.bind_some]
        exact (native_instruction_actor instruction _ _ command commandMem).symm.trans actor
  have positions : (count = 0 ∧ who = alice) ∨ (count = 1 ∧ who = bob) ∨
      ∃ event : nativeGraph.EventId, count = (nativeBeforeResponse event).length := by
    have all : ∀ index : Fin nativePlan.length, ∀ player : Player,
        (nativePlan[index.val]?).bind nativeInstructionPlayer = some player →
          (index.val = 0 ∧ player = alice) ∨ (index.val = 1 ∧ player = bob) ∨
            ∃ event : nativeGraph.EventId, index.val = (nativeBeforeResponse event).length := by
      decide
    exact all ⟨count, bounded⟩ who selected
  rcases positions with ⟨early, owner⟩ | ⟨early, owner⟩ | ⟨event, same⟩
  · rw [native_horizon] at accounted
    exact Or.inl ⟨owner, by omega, by omega⟩
  · rw [native_horizon] at accounted
    exact Or.inr ⟨owner, by omega, by omega⟩
  · have evaluated := priorMem
    rw [same, native_roundsFrom_prefix menu.uniformResponses (nativeBeforeResponse event)
      (.player (nativeOwner event) :: nativeAfterResponse event)
        (native_response_split event)] at evaluated
    have grant := native_response_prefix_grant menu.uniformResponses event prior evaluated
    have sameGrant := native_activation_grant prior control.execution who (by
      cases command <;> simp only [ReactiveApplication.Command.actor?] at actor <;>
        try cases actor
      exact observed)
    rw [sameGrant, grant] at ambient
    cases ambient

def preludeSteps (who : Player) : Nat := if who = alice then 5 else 3

theorem prelude_reaches_binding (players : Profile model.behavioralSignature) (who : Player)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some who)
    (ambient : control.execution.application.serviceGrant = none)
    (later : arena.History)
    (supported : later ∈ (model.runBehavioralFrom players (preludeSteps who)
      ⟨some control, trace⟩).support) :
    ∃ result, later.state = some result ∧ result.actor = some alice ∧
      result.execution.application.serviceGrant = some aliceBinding := by
  have computed := native_behavioral_position (observation := leaks) players (preludeSteps who)
    ⟨some control, trace⟩ later supported
  change nativePosition later.state = nativeAdvancePosition^[preludeSteps who]
    (some (control.remaining, control.actor, control.execution.environmentRecall.length))
      at computed
  obtain ⟨rfl, remaining, cursor⟩ | ⟨rfl, remaining, cursor⟩ :=
    prelude_position who control trace active ambient
  all_goals
    rw [remaining, active, cursor] at computed
    change nativePosition later.state = some (85, some alice, 4) at computed
    rcases later with ⟨state, laterTrace⟩
    cases state with
    | none => cases computed
    | some result =>
        have fields := Option.some.inj computed
        have actor := congrArg (fun value : Nat × Option Player × Nat => value.2.1) fields
        have position := congrArg (fun value : Nat × Option Player × Nat => value.2.2) fields
        exact ⟨result, rfl, actor, native_grant_of_decision_cursor (observation := leaks)
          aliceBinding result laterTrace actor position⟩

theorem prescribed_prelude_results (who : Player) (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some who)
    (ambient : control.execution.application.serviceGrant = none) (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support) :
    ∃ result, final.state = some result ∧ nativeResults result.execution.application.config =
      ⟨.success false, .success false, .success false⟩ := by
  have short : preludeSteps who ≤ 2 * nativeHorizon + 1 := by fin_cases who <;> decide
  rw [← Nat.add_sub_of_le short, model.runBehavioralFrom_add] at supported
  obtain ⟨later, laterMem, finalMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
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
    (ambient : view.application.publicView.serviceGrant = none) :
    assessment.IsSequentiallyRationalAt site (assessment.continuationContext site
      (fun history => nativeUtility bob history.state) (2 * nativeHorizon + 1)) := by
  intro alternative _
  simp only [InformationModel.BehavioralAssessment.continuationContext_value,
    FinDist.expect_bind, strategy, Profile.update_eq_self]
  apply FinDist.expect_mono
  intro history _
  obtain ⟨control, stateEq, active, _, observed⟩ :=
    information_control bob past view ⟨history.1, history.2.trans information⟩
  rcases history with ⟨⟨state, trace⟩, historyInfo⟩
  change state = some control at stateEq
  subst state
  have controlAmbient : control.execution.application.serviceGrant = none := by
    rw [← observed] at ambient
    exact ambient
  have prescribed : (model.runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).expect (fun final => nativeUtility bob final.state) = 1 := by
    refine (FinDist.expect_congr (v := fun _ => (1 : ℝ)) ?_).trans
      (FinDist.expect_const _ 1)
    intro final finalMem
    obtain ⟨result, finalEq, outcomes⟩ := prescribed_prelude_results bob control trace active
      controlAmbient final finalMem
    simp [nativeUtility, finalEq, outcomes, utility_bob, correctness]
  rw [prescribed]
  apply FinDist.expect_le_of_forall
  intro final _
  cases final.state with
  | none => change (0 : ℝ) ≤ 1; norm_num
  | some result => exact (utility_bob_bounds (nativeResults result.execution.application.config)).2

end VegasTests.SelectiveAssociation.Restricted
