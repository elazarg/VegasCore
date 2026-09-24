/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourcePreludeControls
import VegasTests.SelectiveAssociationSourceGuessPayoffs
import VegasTests.SelectiveAssociationProbability

/-! # Bob cannot gain by an ambient response before Alice's fresh binding -/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability

theorem playing_no_certificate (Claim : Type) (defaultClaim : Claim)
    (first second : (application Claim).Action) (bit : Bool) :
    bindingCertificates first second (playing Claim defaultClaim 0 (.success bit)) = ∅ := by
  simp only [bindingCertificates, playing, show (0 : Event).val < 3 by decide, ↓reduceIte,
    certificates, Option.toFinset_none, Finset.filter_empty, reduceCtorEq,
    Finset.union_self]

theorem prescribed_carol_input_same (Claim : Type) (defaultClaim : Claim)
    (first second : (application Claim).Action) (bit : Bool) :
    ((carolInput first second (playing Claim defaultClaim 0 (.success bit))).recall carol,
      (carolInput first second (playing Claim defaultClaim 0 (.success bit))).observe
        (application Claim) carol) =
    ((carolInput first second (playing Claim defaultClaim 0 (.success false))).recall carol,
      (carolInput first second (playing Claim defaultClaim 0 (.success false))).observe
        (application Claim) carol) := by
  cases bit with
  | false => rfl
  | true =>
      exact carolInput_information_flip first second (playing Claim defaultClaim 0 (.success false))
        (playing_no_certificate Claim defaultClaim first second false)

theorem prescribed_bob_input_same (Claim : Type) (defaultClaim : Claim)
    (first second guess : (application Claim).Action) (bit : Bool) :
    ((bobInput first second (playing Claim defaultClaim 0 (.success bit)) guess).recall bob,
      (bobInput first second (playing Claim defaultClaim 0 (.success bit)) guess).observe
        (application Claim) bob) =
    ((bobInput first second (playing Claim defaultClaim 0 (.success false)) guess).recall bob,
      (bobInput first second (playing Claim defaultClaim 0 (.success false)) guess).observe
        (application Claim) bob) := by
  cases bit with
  | false => rfl
  | true =>
      exact bobInput_information_flip first second (playing Claim defaultClaim 0 (.success false))
        guess (playing_no_certificate Claim defaultClaim first second false)

theorem after_prelude_law {Claim : Type} (players : Player → (application Claim).Policy)
    (first second : (application Claim).Action) :
    runInstructions players ((List.finRange 6).flatMap visit) (prelude first second) =
      (chooseAt players alice (aliceInput first second)).bind fun binding =>
        (chooseAt players carol (carolInput first second binding)).bind fun guess =>
          (chooseAt players bob (bobInput first second binding guess)).bind fun response =>
            runInstructions players (afterResponse 2)
              ((bobInput first second binding guess).respond (application Claim) bob response) := by
  change runInstructions players (visit 0 ++ (visit 1 ++
    [.application (.grant 2), .player bob] ++ afterResponse 2)) (prelude first second) = _
  rw [runInstructions_visit]
  apply FinDist.bind_congr
  intro binding _
  rw [List.append_assoc, runInstructions_visit]
  apply FinDist.bind_congr
  intro guess _
  rw [List.cons_append, List.cons_append, List.nil_append, runInstructions_application,
    runInstructions_player]
  rfl

theorem after_prelude_bob_bound (Claim : Type) (defaultClaim : Claim)
    (players : Player → (application Claim).Policy)
    (alicePolicy : players alice = policy Claim defaultClaim alice)
    (first second : (application Claim).Action) :
    (runInstructions players ((List.finRange 6).flatMap visit) (prelude first second)).expect
      (fun final => utility (results final.application) bob) ≤ 1 / 2 := by
  have aliceLaw : chooseAt players alice (aliceInput first second) =
      (FinDist.uniformOfFintype (α := Bool)).map
        (fun bit => playing Claim defaultClaim 0 (.success bit)) := by
    simp only [chooseAt, alicePolicy, policy]
    rfl
  have carolLaw (bit : Bool) : chooseAt players carol
      (carolInput first second (playing Claim defaultClaim 0 (.success bit))) =
      chooseAt players carol
        (carolInput first second (playing Claim defaultClaim 0 (.success false))) := by
    have same := prescribed_carol_input_same Claim defaultClaim first second bit
    exact congrArg (fun info => players carol info.1 info.2) same
  have bobLaw (guess : (application Claim).Action) (bit : Bool) : chooseAt players bob
      (bobInput first second (playing Claim defaultClaim 0 (.success bit)) guess) =
      chooseAt players bob
        (bobInput first second (playing Claim defaultClaim 0 (.success false)) guess) := by
    have same := prescribed_bob_input_same Claim defaultClaim first second guess bit
    exact congrArg (fun info => players bob info.1 info.2) same
  rw [after_prelude_law, aliceLaw, FinDist.expect_bind, FinDist.expect_map]
  calc
    _ ≤ (FinDist.uniformOfFintype (α := Bool)).expect (fun bit =>
        (chooseAt players carol
          (carolInput first second (playing Claim defaultClaim 0 (.success false)))).expect
            (fun guess => (chooseAt players bob
              (bobInput first second (playing Claim defaultClaim 0 (.success false)) guess)).expect
                (fun response => correctness (.success bit) (selectedBinding 2 response)))) := by
      apply FinDist.expect_mono
      intro bit _
      rw [FinDist.expect_bind, carolLaw bit]
      apply FinDist.expect_mono
      intro guess _
      rw [FinDist.expect_bind, bobLaw guess bit]
      apply FinDist.expect_mono
      intro response _
      apply FinDist.expect_le_of_forall
      intro final supported
      have bound := bob_guess_response_payoff_le players _ final response
        (.success bit) (selectedBinding 1 guess) (by
          rw [bobInput_core]
          simp [selectedBinding, playing]) (bobInput_visit ..) supported
      have penalty : 0 ≤ openingPenalty (selectedBinding 2 response) := by
        cases selectedBinding 2 response <;> norm_num [openingPenalty]
      linarith
    _ = (chooseAt players carol
        (carolInput first second (playing Claim defaultClaim 0 (.success false)))).expect
          (fun guess => (FinDist.uniformOfFintype (α := Bool)).expect
            (fun bit => (chooseAt players bob
              (bobInput first second (playing Claim defaultClaim 0 (.success false)) guess)).expect
                (fun response => correctness (.success bit) (selectedBinding 2 response)))) :=
      FinDist.expect_comm _ _ _
    _ ≤ 1 / 2 := by
      apply FinDist.expect_le_of_forall
      intro guess _
      have bound := fair_guess_le_half ((chooseAt players bob
        (bobInput first second (playing Claim defaultClaim 0 (.success false)) guess)).map
          (selectedBinding 2))
      simpa only [FinDist.expect_map] using bound

theorem after_prelude_bob_prescribed (Claim : Type) (defaultClaim : Claim)
    (first second : (application Claim).Action) :
    (runInstructions (policy Claim defaultClaim) ((List.finRange 6).flatMap visit)
      (prelude first second)).expect (fun final => utility (results final.application) bob) =
        1 / 2 := by
  let players := policy Claim defaultClaim
  let binding := fun bit => playing Claim defaultClaim 0 (.success bit)
  let input := fun guess => bobInput first second (binding false) guess
  let target := fun guess => publicGuess ((input guess).observe (application Claim) bob)
  have aliceLaw : chooseAt players alice (aliceInput first second) =
      (FinDist.uniformOfFintype (α := Bool)).map binding := by
    simp only [chooseAt, players, policy]
    rfl
  have carolLaw (bit : Bool) : chooseAt players carol (carolInput first second (binding bit)) =
      chooseAt players carol (carolInput first second (binding false)) := by
    have same := prescribed_carol_input_same Claim defaultClaim first second bit
    exact congrArg (fun info => players carol info.1 info.2) same
  have bobLaw (guess : (application Claim).Action) (bit : Bool) :
      chooseAt players bob (bobInput first second (binding bit) guess) =
        FinDist.pure (playing Claim defaultClaim 2 (.success (target guess))) := by
    have same := prescribed_bob_input_same Claim defaultClaim first second guess bit
    have sameLaw := congrArg (fun info => players bob info.1 info.2) same
    change chooseAt players bob (bobInput first second (binding bit) guess) =
      chooseAt players bob (input guess) at sameLaw
    rw [sameLaw]
    dsimp only [chooseAt, players]
    simp only [policy]
    rfl
  rw [after_prelude_law, aliceLaw, FinDist.expect_bind, FinDist.expect_map]
  calc
    _ = (FinDist.uniformOfFintype (α := Bool)).expect (fun bit =>
        (chooseAt players carol (carolInput first second (binding false))).expect
          (fun guess => correctness (.success bit) (.success (target guess)))) := by
      apply FinDist.expect_congr
      intro bit _
      rw [FinDist.expect_bind, carolLaw bit]
      apply FinDist.expect_congr
      intro guess _
      rw [FinDist.expect_bind, bobLaw guess bit, FinDist.expect_pure]
      calc
        _ = (runInstructions players (afterResponse 2)
            ((bobInput first second (binding bit) guess).respond (application Claim) bob
              (playing Claim defaultClaim 2 (.success (target guess))))).expect
                (fun _ => correctness (.success bit) (.success (target guess))) := by
          apply FinDist.expect_congr
          intro final supported
          apply bob_guess_response_payoff_eq players
            (bobInput first second (binding bit) guess) final
            (playing Claim defaultClaim 2 (.success (target guess))) (.success bit)
            (selectedBinding 1 guess) (target guess)
          · rw [bobInput_core]
            simp [binding, selectedBinding, playing]
          · exact bobInput_visit ..
          · simp [selectedBinding, playing]
          · exact policy_opensAt Claim defaultClaim 3 (by decide)
          · exact policy_opensAt Claim defaultClaim 5 (by decide)
          · exact supported
        _ = _ := FinDist.expect_const ..
    _ = (chooseAt players carol (carolInput first second (binding false))).expect
        (fun guess => (FinDist.uniformOfFintype (α := Bool)).expect
          (fun bit => correctness (.success bit) (.success (target guess)))) :=
      FinDist.expect_comm _ _ _
    _ = 1 / 2 := by
      have fair (guess : (application Claim).Action) :
          (FinDist.uniformOfFintype (α := Bool)).expect
            (fun bit => correctness (.success bit) (.success (target guess))) = 1 / 2 := by
        rw [FinDist.expect_eq_sum]
        simp only [FinDist.prob_uniformOfFintype, Fintype.card_bool, Nat.cast_ofNat,
          Fintype.sum_bool]
        cases target guess <;> norm_num [correctness]
      simp_rw [fair]
      exact FinDist.expect_const ..

theorem finish_bob_ambient_bound (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (players : Player → (application Claim).Policy)
    (alicePolicy : players alice = policy Claim defaultClaim alice)
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some bob) (ambient : control.execution.application.visit = none) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      (some control)).expect (fun state => utility (protocolResults state) bob) ≤ 1 / 2 := by
  obtain ⟨remaining, first, execution⟩ :=
    bob_ambient_representation Claim control trace active ambient
  have position : control.execution.environmentRecall.length = 2 := by
    rw [execution]
    rfl
  rw [finish_ambient_law players 2 (by decide) bob control active remaining position,
    FinDist.expect_map, FinDist.expect_bind]
  apply FinDist.expect_le_of_forall
  intro response _
  change (runInstructions players (calendar.drop 2)
    (control.execution.respond (application Claim) bob response)).expect
      (fun final => utility (results final.application) bob) ≤ 1 / 2
  rw [execution]
  exact after_prelude_bob_bound Claim defaultClaim players alicePolicy first response

theorem finish_bob_ambient_prescribed (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some bob) (ambient : control.execution.application.visit = none) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
      (policy Claim defaultClaim) (some control)).expect
        (fun state => utility (protocolResults state) bob) = 1 / 2 := by
  obtain ⟨remaining, first, execution⟩ :=
    bob_ambient_representation Claim control trace active ambient
  have position : control.execution.environmentRecall.length = 2 := by rw [execution]; rfl
  rw [finish_ambient_law (policy Claim defaultClaim) 2 (by decide) bob control active remaining
    position, FinDist.expect_map, FinDist.expect_bind]
  calc
    _ = (policy Claim defaultClaim bob (control.execution.recall bob)
        (control.execution.observe (application Claim) bob)).expect (fun _ => 1 / 2) := by
      apply FinDist.expect_congr
      intro response _
      change (runInstructions (policy Claim defaultClaim) (calendar.drop 2)
        (control.execution.respond (application Claim) bob response)).expect
          (fun final => utility (results final.application) bob) = 1 / 2
      rw [execution]
      exact after_prelude_bob_prescribed Claim defaultClaim first response
    _ = _ := FinDist.expect_const ..

open Classical in
/-- At Bob's ambient information sets, every whole continuation policy earns
at most the prescribed half. No restriction on the site's belief is needed. -/
theorem bob_ambient_sequentially_rational (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (assessment : (model Claim).BehavioralAssessment)
    (strategy : assessment.strategy = profile Claim defaultClaim)
    (site : (model Claim).InformationSite bob)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (siteEq : site.1 = some (past, view)) (ambient : view.application.visit = none) :
    assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site (payoff bob) (2 * horizon + 1)) := by
  intro alternative _
  rw [prescribed_context_value_finish Claim defaultClaim assessment strategy,
    prescribed_context_baseline Claim defaultClaim assessment strategy]
  have bound : (assessment.belief bob site).expect (fun history =>
      ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
        (Function.update (policy Claim defaultClaim) bob
          (decodedAlternative Claim bob alternative)) history.1.state).expect
            (fun state => utility (protocolResults state) bob)) ≤ 1 / 2 := by
      apply FinDist.expect_le_of_forall
      intro history _
      obtain ⟨control, stateEq, active, _, observed⟩ := information_control Claim bob past view
        ⟨history.1, history.2.trans siteEq⟩
      rcases history with ⟨⟨state, trace⟩, information⟩
      change state = some control at stateEq
      subst state
      apply finish_bob_ambient_bound Claim defaultClaim
        (Function.update (policy Claim defaultClaim) bob
          (decodedAlternative Claim bob alternative))
        (Function.update_of_ne (by decide : alice ≠ bob) _ _) control trace active
      rw [← observed] at ambient
      exact ambient
  have baseline : (assessment.belief bob site).expect (fun history =>
      ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
        (policy Claim defaultClaim) history.1.state).expect
          (fun state => utility (protocolResults state) bob)) = 1 / 2 := by
      calc
        _ = (assessment.belief bob site).expect (fun _ => 1 / 2) := by
          apply FinDist.expect_congr
          intro history _
          obtain ⟨control, stateEq, active, _, observed⟩ := information_control Claim bob past view
            ⟨history.1, history.2.trans siteEq⟩
          rcases history with ⟨⟨state, trace⟩, information⟩
          change state = some control at stateEq
          subst state
          apply finish_bob_ambient_prescribed Claim defaultClaim control trace active
          rw [← observed] at ambient
          exact ambient
        _ = _ := FinDist.expect_const ..
  exact bound.trans_eq baseline.symm

end VegasTests.SelectiveAssociation.NamedSource
