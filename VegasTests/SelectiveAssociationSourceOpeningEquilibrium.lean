/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceOpeningCursor

/-! # Sequential rationality at all source opening decisions

Ordinary opening weakly dominates every whole continuation deviation at every
compatible concrete history. Consequently this argument works for any beliefs.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability

theorem opensAt_update_other (Claim : Type) (defaultClaim : Claim) (who : Player)
    (alternative : (application Claim).Policy) (event : Event) (opening : 3 ≤ event.val)
    (other : eventOwner event ≠ who) :
    OpensAt (Function.update (policy Claim defaultClaim) who alternative) event := by
  intro past view visited response supported
  rw [Function.update_of_ne other] at supported
  exact policy_discloses Claim defaultClaim event opening past view visited response supported

theorem opening_information_optimal (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (event : Event) (opening : 3 ≤ event.val)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (granted : view.application.visit = some event) (alternative : (application Claim).Policy)
    (history : (model Claim).InformationHistory (eventOwner event) (some (past, view))) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
      (Function.update (policy Claim defaultClaim) (eventOwner event) alternative)
        history.1.state).expect (fun state => utility (protocolResults state) (eventOwner event)) ≤
      ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
        (policy Claim defaultClaim) history.1.state).expect
          (fun state => utility (protocolResults state) (eventOwner event)) := by
  obtain ⟨control, same, active, recalled, viewed⟩ :=
    information_control Claim (eventOwner event) past view history
  rcases history with ⟨⟨state, trace⟩, observed⟩
  change state = some control at same
  subst state
  have visited : control.execution.application.visit = some event :=
    (congrArg (fun localView : (application Claim).PlayerView =>
      localView.application.visit) viewed).trans granted
  obtain ⟨remaining, position⟩ := decision_remaining Claim event control trace active visited
  have casesEvent : event = 3 ∨ event = 4 ∨ event = 5 := by
    fin_cases event <;> simp_all
  rcases casesEvent with rfl | rfl | rfl
  · obtain ⟨a, c, b, core⟩ := alice_opening_decision_core Claim control trace active visited
    have bound := finish_alice_payoff_le
      (Function.update (policy Claim defaultClaim) alice alternative) control a c b core
      visited active remaining position
      (opensAt_update_other Claim defaultClaim alice alternative 4 (by decide) (by decide))
      (opensAt_update_other Claim defaultClaim alice alternative 5 (by decide) (by decide))
    have baseline := congrArg (fun law : FinDist Results => law.expect (fun result =>
      utility result alice)) (finish_alice_opening_law (policy Claim defaultClaim) control a c b
        core visited active remaining position
        (policy_opensAt Claim defaultClaim 3 (by decide))
        (policy_opensAt Claim defaultClaim 4 (by decide))
        (policy_opensAt Claim defaultClaim 5 (by decide)))
    rw [FinDist.expect_map, FinDist.expect_pure] at baseline
    exact bound.trans_eq baseline.symm
  · obtain ⟨a, c, b, first, core⟩ := carol_opening_decision_core Claim control trace active visited
    have bound := finish_carol_payoff_le
      (Function.update (policy Claim defaultClaim) carol alternative) control a c b first core
      visited active remaining position
      (opensAt_update_other Claim defaultClaim carol alternative 5 (by decide) (by decide))
    have baseline := congrArg (fun law : FinDist Results => law.expect (fun result =>
      utility result carol)) (finish_carol_opening_law (policy Claim defaultClaim)
        control a c b first
        core visited active remaining position
        (policy_opensAt Claim defaultClaim 4 (by decide))
        (policy_opensAt Claim defaultClaim 5 (by decide)))
    rw [FinDist.expect_map, FinDist.expect_pure] at baseline
    exact bound.trans_eq baseline.symm
  · obtain ⟨a, c, b, first, second, core⟩ :=
      bob_opening_decision_core Claim control trace active visited
    have bound := finish_bob_payoff_le
      (Function.update (policy Claim defaultClaim) bob alternative) control a c b first second core
      visited active remaining position
    have baseline := congrArg (fun law : FinDist Results => law.expect (fun result =>
      utility result bob)) (finish_bob_opening_law (policy Claim defaultClaim) control a c b first
        second core visited active remaining position
        (policy_opensAt Claim defaultClaim 5 (by decide)))
    rw [FinDist.expect_map, FinDist.expect_pure] at baseline
    exact bound.trans_eq baseline.symm

theorem opening_sequentiallyRational (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (assessment : (model Claim).BehavioralAssessment)
    (strategy : assessment.strategy = profile Claim defaultClaim)
    (event : Event) (opening : 3 ≤ event.val)
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
  exact FinDist.expect_mono (fun history _ =>
    opening_information_optimal Claim defaultClaim event opening past view granted
      (decodedAlternative Claim (eventOwner event) alternative)
      ⟨history.1, history.2.trans observed⟩)

end VegasTests.SelectiveAssociation.NamedSource
