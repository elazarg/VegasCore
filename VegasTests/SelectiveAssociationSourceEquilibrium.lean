/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceOpeningEquilibrium
import VegasTests.SelectiveAssociationSourcePreludeControls
import VegasTests.SelectiveAssociationSourceAliceValues
import VegasTests.SelectiveAssociationSourceBobPrelude
import VegasTests.SelectiveAssociationSourceInitialLaw

/-! # A sequential equilibrium of the named-evidence source interface

The source interface admits every finite claim, every currently available
named certificate, and every known replay. Sequential rationality compares
whole behavioral continuation policies at all eight response opportunities.
One common fully mixed sequence supplies the consistent beliefs.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability

theorem site_observation (Claim : Type) [Fintype Claim] (who : Player)
    (site : (model Claim).InformationSite who) :
    ∃ past view, site.1 = some (past, view) := by
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active (model Claim) site history
  have seen := history.2
  rw [history_observe] at seen
  change (application Claim).actor history.1.state = some who at active
  cases stateEq : history.1.state with
  | none => rw [stateEq] at active; cases active
  | some control =>
      change history.1.state.bind ReactiveApplication.Control.actor = some who at active
      rw [stateEq] at active seen
      change control.actor = some who at active
      refine ⟨control.execution.recall who, control.execution.observe (application Claim) who, ?_⟩
      simpa only [ReactiveApplication.observe, active, ↓reduceIte] using seen.symm

theorem site_granted_owner (Claim : Type) [Fintype Claim] (who : Player)
    (site : (model Claim).InformationSite who)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (observed : site.1 = some (past, view)) (event : Event)
    (granted : view.application.visit = some event) : who = eventOwner event := by
  obtain ⟨history, _, _⟩ := site.2
  obtain ⟨control, same, active, _, viewed⟩ := information_control Claim who past view
    ⟨history.1, history.2.trans observed⟩
  rcases history with ⟨⟨state, trace⟩, seen⟩
  change state = some control at same
  subst state
  exact (decision_cursor Claim event control trace who active
    ((congrArg (fun localView : (application Claim).PlayerView =>
      localView.application.visit) viewed).trans granted)).1

theorem site_ambient_owner (Claim : Type) [Fintype Claim] (who : Player)
    (site : (model Claim).InformationSite who)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (observed : site.1 = some (past, view)) (ambient : view.application.visit = none) :
    who = alice ∨ who = bob := by
  obtain ⟨history, _, _⟩ := site.2
  obtain ⟨control, same, active, _, viewed⟩ := information_control Claim who past view
    ⟨history.1, history.2.trans observed⟩
  rcases history with ⟨⟨state, trace⟩, seen⟩
  change state = some control at same
  subst state
  rcases ambient_decision_representation Claim control trace who active
    ((congrArg (fun localView : (application Claim).PlayerView =>
      localView.application.visit) viewed).trans ambient) with left | right
  · exact Or.inl left.1
  · exact Or.inr right.1

theorem alice_binding_decision_core (Claim : Type) [Fintype Claim]
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some alice)
    (granted : control.execution.application.visit = some 0) :
    control.execution.application.core = initialCore := by
  obtain ⟨prior, priorMem, same⟩ := decision_predecessor Claim 0 control trace active granted
  change prior ∈ (runInstructions (menu Claim).uniformResponses
    [.player alice, .player bob, .application (.grant 0)] (root Claim)).support at priorMem
  simp only [runInstructions_player, runInstructions_application, runInstructions_nil] at priorMem
  obtain ⟨first, _, afterFirst⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ priorMem)
  obtain ⟨second, _, afterSecond⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ afterFirst)
  cases FinDist.mem_support_pure.mp afterSecond
  rw [same]
  exact aliceInput_core first second

theorem control_serials (Claim : Type) [Fintype Claim]
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control)) :
    control.execution.network.SerialsBeforeNext :=
  (application Claim).serialsBeforeNext_history (scheduler Claim) (FinDist.pure initial) horizon
    ((menu Claim).toRawTrace (FinDist.pure initial) horizon (scheduler Claim) trace)

theorem alice_early_information_optimal (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (early : view.application.visit = none ∨ view.application.visit = some 0)
    (alternative : (application Claim).Policy)
    (history : (model Claim).InformationHistory alice (some (past, view))) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
      (Function.update (policy Claim defaultClaim) alice alternative) history.1.state).expect
        (fun state => utility (protocolResults state) alice) ≤
      ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
        (policy Claim defaultClaim) history.1.state).expect
          (fun state => utility (protocolResults state) alice) := by
  obtain ⟨control, same, active, _, viewed⟩ := information_control Claim alice past view history
  rcases history with ⟨⟨state, trace⟩, observed⟩
  change state = some control at same
  subst state
  have visitSame := congrArg (fun localView : (application Claim).PlayerView =>
    localView.application.visit) viewed
  rcases early with ambient | granted
  · have isAmbient : control.execution.application.visit = none := visitSame.trans ambient
    obtain ⟨remaining, execution⟩ :=
      alice_ambient_representation Claim control trace active isAmbient
    have bound := finish_alice_ambient_payoff_le defaultClaim
      (Function.update (policy Claim defaultClaim) alice alternative)
      (Function.update_of_ne (by decide : carol ≠ alice) _ _)
      (Function.update_of_ne (by decide : bob ≠ alice) _ _) control active remaining execution
    exact bound.trans_eq
      (finish_alice_prescribed_ambient Claim defaultClaim control active remaining execution).symm
  · have visited : control.execution.application.visit = some 0 := visitSame.trans granted
    have core := alice_binding_decision_core Claim control trace active visited
    obtain ⟨remaining, position⟩ := decision_remaining Claim 0 control trace active visited
    have serials := control_serials Claim control trace
    have bound := finish_alice_binding_payoff_le defaultClaim
      (Function.update (policy Claim defaultClaim) alice alternative)
      (Function.update_of_ne (by decide : carol ≠ alice) _ _)
      (Function.update_of_ne (by decide : bob ≠ alice) _ _) control core visited serials
      active remaining position
    exact bound.trans_eq (finish_alice_prescribed_binding Claim defaultClaim control core
      visited serials active remaining position).symm

theorem alice_early_sequentiallyRational (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (assessment : (model Claim).BehavioralAssessment)
    (strategy : assessment.strategy = profile Claim defaultClaim)
    (site : (model Claim).InformationSite alice)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (observed : site.1 = some (past, view))
    (early : view.application.visit = none ∨ view.application.visit = some 0)
    (alternative : (model Claim).BehavioralPolicy alice) :
    (assessment.continuationContext site (payoff alice) (2 * horizon + 1)).value alternative ≤
      (assessment.continuationContext site (payoff alice) (2 * horizon + 1)).value
        (assessment.strategy alice) := by
  rw [prescribed_context_value_finish Claim defaultClaim assessment strategy,
    prescribed_context_baseline Claim defaultClaim assessment strategy]
  exact FinDist.expect_mono (fun history _ => alice_early_information_optimal Claim defaultClaim
    past view early (decodedAlternative Claim alice alternative)
    ⟨history.1, history.2.trans observed⟩)

theorem prescribed_sequentiallyRational (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (assessment : (model Claim).BehavioralAssessment)
    (strategy : assessment.strategy = profile Claim defaultClaim)
    (fair : FairGuessBeliefs Claim assessment) :
    assessment.IsSequentiallyRationalWithin payoff (2 * horizon + 1) := by
  intro who site
  obtain ⟨past, view, observed⟩ := site_observation Claim who site
  cases visited : view.application.visit with
  | none =>
      rcases site_ambient_owner Claim who site past view observed visited with rfl | rfl
      · intro alternative _
        exact alice_early_sequentiallyRational Claim defaultClaim assessment strategy site
          past view observed (Or.inl visited) alternative
      · exact bob_ambient_sequentially_rational Claim defaultClaim assessment strategy site
          past view observed visited
  | some event =>
      have owner := site_granted_owner Claim who site past view observed event visited
      subst who
      intro alternative _
      fin_cases event
      · exact alice_early_sequentiallyRational Claim defaultClaim assessment strategy site
          past view observed (Or.inr visited) alternative
      · exact guess_sequentiallyRational Claim defaultClaim assessment strategy fair 1 (Or.inl rfl)
          site past view observed visited alternative
      · exact guess_sequentiallyRational Claim defaultClaim assessment strategy fair 2 (Or.inr rfl)
          site past view observed visited alternative
      · exact opening_sequentiallyRational Claim defaultClaim assessment strategy 3 (by decide)
          site past view observed visited alternative
      · exact opening_sequentiallyRational Claim defaultClaim assessment strategy 4 (by decide)
          site past view observed visited alternative
      · exact opening_sequentiallyRational Claim defaultClaim assessment strategy 5 (by decide)
          site past view observed visited alternative

/-- A genuine sequential equilibrium, with its initialized public-result law.
Alice's successful binding is fair; both successful guesses equal false.
The source game is the actual six-event program with the stated communication
interface and calendar, for an arbitrary finite claim alphabet. -/
theorem exists_sequentialEquilibrium (Claim : Type) [Fintype Claim] (defaultClaim : Claim) :
    ∃ assessment : (model Claim).BehavioralAssessment,
      assessment.strategy = profile Claim defaultClaim ∧
      assessment.IsSequentialEquilibriumFor
        ((menu Claim).decisionInformationAntichain (FinDist.pure initial)
          horizon (scheduler Claim))
        (fun who site => assessment.continuationContext site (payoff who) (2 * horizon + 1)) ∧
      (((model Claim).runBehavioral assessment.strategy (2 * horizon + 1)).map
        (fun history => protocolResults history.state)) =
        (FinDist.uniformOfFintype (α := Bool)).map (fun bit =>
          (⟨.success bit, .success false, .success false⟩ : Results)) := by
  obtain ⟨assessment, strategy, consistent, fair⟩ :=
    exists_consistent_fair_assessment Claim defaultClaim
  refine ⟨assessment, strategy,
    ⟨prescribed_sequentiallyRational Claim defaultClaim assessment strategy fair, consistent⟩, ?_⟩
  rw [strategy]
  exact prescribed_initial_results Claim defaultClaim

end VegasTests.SelectiveAssociation.NamedSource
