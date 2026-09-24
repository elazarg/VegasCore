/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceAssessmentValues
import VegasTests.SelectiveAssociationSourceGuessPayoffs

/-! # Sequential rationality at the two source guessing sites

The comparison permits every whole continuation policy. Conditional optimality
uses all compatible histories, including histories of zero limiting belief.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability

theorem guess_information_finish_le (Claim : Type) [Fintype Claim]
    (players : Player → (application Claim).Policy) (event : Event)
    (guessSite : event = 1 ∨ event = 2)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (granted : view.application.visit = some event)
    (history : (model Claim).InformationHistory (eventOwner event) (some (past, view))) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      history.1.state).expect (fun state => utility (protocolResults state) (eventOwner event)) ≤
        (players (eventOwner event) past view).expect
          (fun response => bindingReward (selectedBinding event response) history.1.state) := by
  obtain ⟨control, same, active, recalled, viewed⟩ :=
    information_control Claim (eventOwner event) past view history
  rcases history with ⟨⟨state, trace⟩, observed⟩
  change state = some control at same
  subst state
  have visited : control.execution.application.visit = some event :=
    (congrArg (fun localView : (application Claim).PlayerView =>
      localView.application.visit) viewed).trans granted
  obtain ⟨remaining, position⟩ := decision_remaining Claim event control trace active visited
  rcases guessSite with rfl | rfl
  · obtain ⟨sample, _, execution⟩ :=
      carol_decision_representation Claim control trace active visited
    have core := congrArg (fun execution : (application Claim).Execution =>
      execution.application.core) execution
    rw [carolInput_core] at core
    have bound := finish_carol_guess_payoff_le players control _ core
      visited active remaining position
    change control.execution.recall carol = past at recalled
    change control.execution.observe (application Claim) carol = view at viewed
    rw [recalled, viewed] at bound
    exact bound.trans_eq (FinDist.expect_congr (fun response _ =>
      (bindingReward_of_alice control _ core (selectedBinding 1 response)).symm))
  · obtain ⟨sample, _, execution⟩ :=
      bob_decision_representation Claim control trace active visited
    have core := congrArg (fun execution : (application Claim).Execution =>
      execution.application.core) execution
    rw [bobInput_core] at core
    have bound := finish_bob_guess_payoff_le players control _ _ core
      visited active remaining position
    change control.execution.recall bob = past at recalled
    change control.execution.observe (application Claim) bob = view at viewed
    rw [recalled, viewed] at bound
    exact bound.trans_eq (FinDist.expect_congr (fun response _ =>
      (bindingReward_of_carol control _ _ core (selectedBinding 2 response)).symm))

theorem guess_information_baseline (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (event : Event) (guessSite : event = 1 ∨ event = 2)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (granted : view.application.visit = some event)
    (history : (model Claim).InformationHistory (eventOwner event) (some (past, view))) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
      (policy Claim defaultClaim) history.1.state).expect
        (fun state => utility (protocolResults state) (eventOwner event)) =
      bindingReward (.success (publicGuess view)) history.1.state := by
  obtain ⟨control, same, active, recalled, viewed⟩ :=
    information_control Claim (eventOwner event) past view history
  rcases history with ⟨⟨state, trace⟩, observed⟩
  change state = some control at same
  subst state
  have visited : control.execution.application.visit = some event :=
    (congrArg (fun localView : (application Claim).PlayerView =>
      localView.application.visit) viewed).trans granted
  obtain ⟨remaining, position⟩ := decision_remaining Claim event control trace active visited
  rcases guessSite with rfl | rfl
  · obtain ⟨sample, _, execution⟩ :=
      carol_decision_representation Claim control trace active visited
    have core := congrArg (fun execution : (application Claim).Execution =>
      execution.application.core) execution
    rw [carolInput_core] at core
    have value := finish_carol_prescribed_guess Claim defaultClaim control _ core
      visited active remaining position
    change control.execution.observe (application Claim) carol = view at viewed
    rw [viewed] at value
    exact value.trans (by simpa only [openingPenalty_success, sub_zero] using
      (bindingReward_of_alice control _ core (.success (publicGuess view))).symm)
  · obtain ⟨sample, _, execution⟩ :=
      bob_decision_representation Claim control trace active visited
    have core := congrArg (fun execution : (application Claim).Execution =>
      execution.application.core) execution
    rw [bobInput_core] at core
    have value := finish_bob_prescribed_guess Claim defaultClaim control _ _ core
      visited active remaining position
    change control.execution.observe (application Claim) bob = view at viewed
    rw [viewed] at value
    exact value.trans (by simpa only [openingPenalty_success, sub_zero] using
      (bindingReward_of_carol control _ _ core (.success (publicGuess view))).symm)

theorem guess_sequentiallyRational (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (assessment : (model Claim).BehavioralAssessment)
    (strategy : assessment.strategy = profile Claim defaultClaim)
    (fair : FairGuessBeliefs Claim assessment) (event : Event) (guessSite : event = 1 ∨ event = 2)
    (site : (model Claim).InformationSite (eventOwner event))
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (observed : site.1 = some (past, view)) (granted : view.application.visit = some event)
    (alternative : (model Claim).BehavioralPolicy (eventOwner event)) :
    (assessment.continuationContext site (payoff (eventOwner event))
      (2 * horizon + 1)).value alternative ≤
        (assessment.continuationContext site (payoff (eventOwner event))
          (2 * horizon + 1)).value (assessment.strategy (eventOwner event)) := by
  rw [prescribed_context_value_finish Claim defaultClaim assessment strategy,
    prescribed_context_baseline Claim defaultClaim assessment strategy]
  let responses := decodedAlternative Claim (eventOwner event) alternative past view
  calc
    _ ≤ (assessment.belief (eventOwner event) site).expect (fun history =>
        responses.expect (fun response =>
          bindingReward (selectedBinding event response) history.1.state)) := by
      apply FinDist.expect_mono
      intro history _
      have bound := guess_information_finish_le Claim
        (Function.update (policy Claim defaultClaim) (eventOwner event)
          (decodedAlternative Claim (eventOwner event) alternative)) event guessSite past view
            granted ⟨history.1, history.2.trans observed⟩
      simpa only [Function.update_self] using bound
    _ = (assessment.belief (eventOwner event) site).expect (fun history =>
        (responses.map (selectedBinding event)).expect (fun guess =>
          bindingReward guess history.1.state)) := by
      simp only [FinDist.expect_map]
    _ ≤ (assessment.belief (eventOwner event) site).expect (fun history =>
        bindingReward (.success (publicGuess view)) history.1.state) :=
      prescribed_mixed_guess_optimal Claim assessment fair (eventOwner event) site
        past view observed (by
          rcases guessSite with rfl | rfl
          · exact Or.inl ⟨rfl, granted⟩
          · exact Or.inr ⟨rfl, granted⟩) _
    _ = _ := by
      apply FinDist.expect_congr
      intro history _
      exact (guess_information_baseline Claim defaultClaim event guessSite past view granted
        ⟨history.1, history.2.trans observed⟩).symm

end VegasTests.SelectiveAssociation.NamedSource
