/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.SourcePreludeControls
import Vegas.Examples.SelectiveAssociation.SourceGuessPayoffs
import Vegas.Examples.SelectiveAssociation.Probability
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Bob cannot gain by an ambient response before Alice's fresh binding -/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability

private theorem bob_utility_integrable {α : Type*} (μ : PMF α) (summary : α → Results) :
    PayoffIntegrable μ (fun a => utility (summary a) bob) :=
  payoffIntegrable_of_finite_summary μ summary (fun result => utility result bob)

private theorem correctness_abs_le (value guess : PublicationResult Bool) :
    |correctness value guess| ≤ 1 := by
  cases value <;> cases guess <;> simp only [correctness] <;>
    first | (split_ifs <;> norm_num) | norm_num

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
  apply bind_congr_on_support _
  intro binding _
  rw [List.append_assoc, runInstructions_visit]
  apply bind_congr_on_support _
  intro guess _
  rw [List.cons_append, List.cons_append, List.nil_append, runInstructions_application,
    runInstructions_player]
  rfl

theorem after_prelude_bob_bound (Claim : Type) (defaultClaim : Claim)
    (players : Player → (application Claim).Policy)
    (alicePolicy : players alice = policy Claim defaultClaim alice)
    (first second : (application Claim).Action) :
    expect (runInstructions players ((List.finRange 6).flatMap visit) (prelude first second))
      (fun final => utility (results final.application) bob) ≤ 1 / 2 := by
  have aliceLaw : chooseAt players alice (aliceInput first second) =
      (PMF.uniformOfFintype Bool).map
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
  rw [after_prelude_law, aliceLaw, expect_bind_tower _ _ _ (bob_utility_integrable _ _),
    expect_map]
  calc
    _ ≤ expect (PMF.uniformOfFintype Bool) (fun bit =>
        expect (chooseAt players carol
          (carolInput first second (playing Claim defaultClaim 0 (.success false))))
            (fun guess => expect (chooseAt players bob
              (bobInput first second (playing Claim defaultClaim 0 (.success false)) guess))
                (fun response => correctness (.success bit) (selectedBinding 2 response)))) := by
      refine expect_mono (fun bit _ => ?_) (payoffIntegrable_of_finite _ _)
        (payoffIntegrable_of_finite _ _)
      dsimp only [Function.comp_apply]
      rw [expect_bind_tower _ _ _ (bob_utility_integrable _ _), carolLaw bit]
      refine expect_mono (fun guess _ => ?_)
        (payoffIntegrable_expect_of_finite_summary _ _ _
          (fun result => utility result bob))
        (payoffIntegrable_of_bounded _ _ (C := 1) fun _ =>
          expect_abs_le_of_bounded zero_le_one fun _ => correctness_abs_le _ _)
      rw [expect_bind_tower _ _ _ (bob_utility_integrable _ _), bobLaw guess bit]
      refine expect_mono (fun response _ => ?_)
        (payoffIntegrable_expect_of_finite_summary _ _ _
          (fun result => utility result bob))
        (payoffIntegrable_of_finite_summary _ (selectedBinding 2) (correctness (.success bit)))
      refine expect_le_const _ _ (bob_utility_integrable _ _)
        _ fun final supported => ?_
      have bound := bob_guess_response_payoff_le players _ final response
        (.success bit) (selectedBinding 1 guess) (by
          rw [bobInput_core]
          simp [selectedBinding, playing]) (bobInput_visit ..) supported
      have penalty : 0 ≤ openingPenalty (selectedBinding 2 response) := by
        cases selectedBinding 2 response <;> norm_num [openingPenalty]
      linarith
    _ = expect (chooseAt players carol
        (carolInput first second (playing Claim defaultClaim 0 (.success false))))
          (fun guess => expect (PMF.uniformOfFintype Bool)
            (fun bit => expect (chooseAt players bob
              (bobInput first second (playing Claim defaultClaim 0 (.success false)) guess))
                (fun response => correctness (.success bit) (selectedBinding 2 response)))) :=
      expect_comm_of_support_finite_left _ _ (Set.toFinite _) _ fun bit _ =>
        payoffIntegrable_expect_of_finite_summary _ _ (selectedBinding 2)
          (correctness (.success bit))
    _ ≤ 1 / 2 := by
      refine expect_le_const _ _ (payoffIntegrable_of_bounded _ _ (C := 1) fun _ =>
        expect_abs_le_of_bounded zero_le_one fun _ =>
          expect_abs_le_of_bounded zero_le_one fun _ => correctness_abs_le _ _) _ fun guess _ => ?_
      have bound := fair_guess_le_half ((chooseAt players bob
        (bobInput first second (playing Claim defaultClaim 0 (.success false)) guess)).map
          (selectedBinding 2))
      simpa only [expect_map, Function.comp_def] using bound

theorem after_prelude_bob_prescribed (Claim : Type) (defaultClaim : Claim)
    (first second : (application Claim).Action) :
    expect (runInstructions (policy Claim defaultClaim) ((List.finRange 6).flatMap visit)
      (prelude first second)) (fun final => utility (results final.application) bob) =
        1 / 2 := by
  let players := policy Claim defaultClaim
  let binding := fun bit => playing Claim defaultClaim 0 (.success bit)
  let input := fun guess => bobInput first second (binding false) guess
  let target := fun guess => publicGuess ((input guess).observe (application Claim) bob)
  have aliceLaw : chooseAt players alice (aliceInput first second) =
      (PMF.uniformOfFintype Bool).map binding := by
    simp only [chooseAt, players, policy]
    rfl
  have carolLaw (bit : Bool) : chooseAt players carol (carolInput first second (binding bit)) =
      chooseAt players carol (carolInput first second (binding false)) := by
    have same := prescribed_carol_input_same Claim defaultClaim first second bit
    exact congrArg (fun info => players carol info.1 info.2) same
  have bobLaw (guess : (application Claim).Action) (bit : Bool) :
      chooseAt players bob (bobInput first second (binding bit) guess) =
        PMF.pure (playing Claim defaultClaim 2 (.success (target guess))) := by
    have same := prescribed_bob_input_same Claim defaultClaim first second guess bit
    have sameLaw := congrArg (fun info => players bob info.1 info.2) same
    change chooseAt players bob (bobInput first second (binding bit) guess) =
      chooseAt players bob (input guess) at sameLaw
    rw [sameLaw]
    dsimp only [chooseAt, players]
    simp only [policy]
    rfl
  rw [after_prelude_law, aliceLaw, expect_bind_tower _ _ _ (bob_utility_integrable _ _),
    expect_map]
  calc
    _ = expect (PMF.uniformOfFintype Bool) (fun bit =>
        expect (chooseAt players carol (carolInput first second (binding false)))
          (fun guess => correctness (.success bit) (.success (target guess)))) := by
      apply expect_congr_on_support
      intro bit _
      dsimp only [Function.comp_apply]
      rw [expect_bind_tower _ _ _ (bob_utility_integrable _ _), carolLaw bit]
      apply expect_congr_on_support
      intro guess _
      rw [expect_bind_tower _ _ _ (bob_utility_integrable _ _), bobLaw guess bit,
        expect_pure]
      calc
        _ = expect (runInstructions players (afterResponse 2)
            ((bobInput first second (binding bit) guess).respond (application Claim) bob
              (playing Claim defaultClaim 2 (.success (target guess)))))
                (fun _ => correctness (.success bit) (.success (target guess))) := by
          apply expect_congr_on_support
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
        _ = _ := expect_constant ..
    _ = expect (chooseAt players carol (carolInput first second (binding false)))
        (fun guess => expect (PMF.uniformOfFintype Bool)
          (fun bit => correctness (.success bit) (.success (target guess)))) :=
      expect_comm_of_support_finite_left _ _ (Set.toFinite _) _ fun bit _ =>
        payoffIntegrable_of_finite_summary _ target
          (fun guess => correctness (.success bit) (.success guess))
    _ = 1 / 2 := by
      have fair (guess : (application Claim).Action) :
          expect (PMF.uniformOfFintype Bool)
            (fun bit => correctness (.success bit) (.success (target guess))) = 1 / 2 := by
        rw [expect_eq_sum]
        simp only [toReal_uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat,
          Fintype.sum_bool]
        cases target guess <;> norm_num [correctness]
      simp_rw [fair]
      exact expect_constant ..

theorem finish_bob_ambient_bound (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (players : Player → (application Claim).Policy)
    (alicePolicy : players alice = policy Claim defaultClaim alice)
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some bob) (ambient : control.execution.application.visit = none) :
    expect ((application Claim).finish (PMF.pure initial) horizon (scheduler Claim) players
      (some control)) (fun state => utility (protocolResults state) bob) ≤ 1 / 2 := by
  obtain ⟨remaining, first, execution⟩ :=
    bob_ambient_representation Claim control trace active ambient
  have position : control.execution.environmentRecall.length = 2 := by
    rw [execution]
    rfl
  rw [finish_ambient_law players 2 (by decide) bob control active remaining position,
    expect_map]
  simp only [Function.comp_def]
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_finite_summary _ _
      (fun result => utility result bob))]
  refine expect_le_const _ _ (payoffIntegrable_expect_of_finite_summary _ _ _
    (fun result => utility result bob)) _ fun response _ => ?_
  change expect (runInstructions players (calendar.drop 2)
    (control.execution.respond (application Claim) bob response))
      (fun final => utility (results final.application) bob) ≤ 1 / 2
  rw [execution]
  exact after_prelude_bob_bound Claim defaultClaim players alicePolicy first response

theorem finish_bob_ambient_prescribed (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some bob) (ambient : control.execution.application.visit = none) :
    expect ((application Claim).finish (PMF.pure initial) horizon (scheduler Claim)
      (policy Claim defaultClaim) (some control))
        (fun state => utility (protocolResults state) bob) = 1 / 2 := by
  obtain ⟨remaining, first, execution⟩ :=
    bob_ambient_representation Claim control trace active ambient
  have position : control.execution.environmentRecall.length = 2 := by rw [execution]; rfl
  rw [finish_ambient_law (policy Claim defaultClaim) 2 (by decide) bob control active remaining
    position, expect_map]
  simp only [Function.comp_def]
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_finite_summary _ _
      (fun result => utility result bob))]
  calc
    _ = expect (policy Claim defaultClaim bob (control.execution.recall bob)
        (control.execution.observe (application Claim) bob)) (fun _ => 1 / 2) := by
      apply expect_congr_on_support
      intro response _
      change expect (runInstructions (policy Claim defaultClaim) (calendar.drop 2)
        (control.execution.respond (application Claim) bob response))
          (fun final => utility (results final.application) bob) = 1 / 2
      rw [execution]
      exact after_prelude_bob_prescribed Claim defaultClaim first response
    _ = _ := expect_constant ..

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
  refine (Context.isLocallyOptimal_iff_of_integrable
    (continuation_integrable assessment site _ _)
      fun _ _ => continuation_integrable assessment site _ _).mpr fun alternative _ => ?_
  rw [prescribed_context_value_finish Claim defaultClaim assessment strategy,
    prescribed_context_baseline Claim defaultClaim assessment strategy]
  have bound : expect (assessment.belief bob site) (fun history =>
      expect ((application Claim).finish (PMF.pure initial) horizon (scheduler Claim)
        (Function.update (policy Claim defaultClaim) bob
          (decodedAlternative Claim bob alternative)) history.1.state)
            (fun state => utility (protocolResults state) bob)) ≤ 1 / 2 := by
      refine expect_le_const _ _ (payoffIntegrable_expect_of_finite_summary _ _ _
        (fun result => utility result bob)) _ fun history _ => ?_
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
  have baseline : expect (assessment.belief bob site) (fun history =>
      expect ((application Claim).finish (PMF.pure initial) horizon (scheduler Claim)
        (policy Claim defaultClaim) history.1.state)
          (fun state => utility (protocolResults state) bob)) = 1 / 2 := by
      calc
        _ = expect (assessment.belief bob site) (fun _ => 1 / 2) := by
          apply expect_congr_on_support
          intro history _
          obtain ⟨control, stateEq, active, _, observed⟩ := information_control Claim bob past view
            ⟨history.1, history.2.trans siteEq⟩
          rcases history with ⟨⟨state, trace⟩, information⟩
          change state = some control at stateEq
          subst state
          apply finish_bob_ambient_prescribed Claim defaultClaim control trace active
          rw [← observed] at ambient
          exact ambient
        _ = _ := expect_constant ..
  exact bound.trans_eq baseline.symm

end Vegas.Examples.SelectiveAssociation.NamedSource
