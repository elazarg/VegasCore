/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceConsistency

/-! # The prescribed guess maximizes the conditional binding reward

Public named evidence determines Alice's bit throughout an information set.
Without such evidence, the common consistent belief has equal successful-bit
masses. Both cases allow arbitrary failed bindings in the information fiber.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Vegas.SourceProgram Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

theorem owns_of_holds (state : State) (fact : NamedFact)
    (valid : state.core.evidenceHolds sourceProgram fact.toSource) :
    state.owns (bindingOwner fact.1) fact := by
  rcases state with ⟨core, visit, clock⟩
  rcases core with config | config | config | config | config | config | config
  all_goals
    change fact.toSource.Holds config.state at valid
    change fact.toSource.Possessed (bindingOwner fact.1)
      (sourceObserve (bindingOwner fact.1) config.state)
    obtain ⟨reference, stored⟩ := valid
    refine ⟨rfl, reference, ?_⟩
    change (if fact.toSource.owner = bindingOwner fact.1 then some (config.state.get reference)
      else none) = some (.success fact.toSource.value)
    simp only [NamedFact.toSource, ↓reduceIte, stored]

theorem publicGuess_certificate {Claim : Type} (view : (application Claim).PlayerView)
    (published : ¬ NoPublicAlice view) :
    ∃ message ∈ view.messages.ledger, (0, publicGuess view) ∈ message.payload.evidence := by
  classical
  let facts := view.messages.ledger.flatMap fun message => message.payload.evidence.toList
  have someFact : ∃ fact ∈ facts, fact.1 = 0 := by
    have existsMessage : ∃ message ∈ view.messages.ledger,
        ∃ fact ∈ message.payload.evidence, fact.1 = 0 := by
      simpa only [NoPublicAlice, not_forall, not_not, exists_prop] using published
    obtain ⟨message, member, fact, certified, named⟩ := existsMessage
    exact ⟨fact, List.mem_flatMap.mpr
      ⟨message, member, Finset.mem_toList.mpr certified⟩, named⟩
  cases found : facts.find? (fun fact => fact.1 = 0) with
  | none =>
      have absent := List.find?_eq_none.mp found
      obtain ⟨fact, member, named⟩ := someFact
      have impossible := absent fact member
      simp only [named, decide_true] at impossible
      exact False.elim (impossible trivial)
  | some fact =>
      have named : fact.1 = 0 := by
        simpa only [decide_eq_true_eq] using (List.find?_eq_some_iff_append.mp found).1
      have member := List.mem_of_find?_eq_some found
      obtain ⟨message, recorded, certified⟩ := List.mem_flatMap.mp member
      have guess : publicGuess view = fact.2 := by
        change ((facts.find? (fun fact => fact.1 = 0)).map Prod.snd).getD false = fact.2
        rw [found]
        rfl
      refine ⟨message, recorded, ?_⟩
      rw [guess, ← named]
      exact Finset.mem_toList.mp certified

theorem publicGuess_known (Claim : Type) [Fintype Claim] (who : Player)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (published : ¬ NoPublicAlice view) :
    (model Claim).Knows who (some (past, view))
      (fun history => hasAliceBit (publicGuess view) history.state) := by
  obtain ⟨message, recorded, certified⟩ := publicGuess_certificate view published
  have observed : (0, publicGuess view) ∈ (packetEvidence Claim).observe view :=
    List.mem_flatMap.mpr ⟨message, List.mem_append_right _ recorded,
      Finset.mem_toList.mpr certified⟩
  have known := observed_fact_known Claim who past view (0, publicGuess view) observed
  rintro ⟨⟨state, trace⟩, compatible⟩
  have valid := known ⟨⟨state, trace⟩, compatible⟩
  have seen := history_observe Claim who ⟨state, trace⟩
  rw [seen] at compatible
  cases state with
  | none => cases compatible
  | some control => exact owns_of_holds control.execution.application _ valid

open Classical in
def bindingReward {Claim : Type} (guess : PublicationResult Bool)
    (state : (application Claim).ProtocolState) : ℝ :=
  match guess with
  | .failure => -4
  | .success bit => if hasAliceBit bit state then 1 else 0

theorem bindingReward_le_one {Claim : Type} (guess : PublicationResult Bool)
    (state : (application Claim).ProtocolState) : bindingReward guess state ≤ 1 := by
  cases guess with
  | failure => norm_num [bindingReward]
  | success bit => simp only [bindingReward]; split <;> norm_num

theorem bindingReward_success_nonneg {Claim : Type} (bit : Bool)
    (state : (application Claim).ProtocolState) : 0 ≤ bindingReward (.success bit) state := by
  simp only [bindingReward]
  split <;> norm_num

theorem expected_bindingReward_success (Claim : Type) [Fintype Claim]
    (assessment : (model Claim).BehavioralAssessment) (who : Player)
    (site : (model Claim).InformationSite who) (bit : Bool) :
    (assessment.belief who site).expect (fun history =>
      bindingReward (.success bit) history.1.state) =
      (assessment.belief who site).probOf {history | hasAliceBit bit history.1.state} := by
  classical
  exact FinDist.expect_indicator_eq_probOf (assessment.belief who site)
    {history | hasAliceBit bit history.1.state}

theorem prescribed_guess_optimal (Claim : Type) [Fintype Claim]
    (assessment : (model Claim).BehavioralAssessment) (fair : FairGuessBeliefs Claim assessment)
    (who : Player) (site : (model Claim).InformationSite who)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (observed : site.1 = some (past, view))
    (decision : (who = carol ∧ view.application.visit = some 1) ∨
      (who = bob ∧ view.application.visit = some 2)) (guess : PublicationResult Bool) :
    (assessment.belief who site).expect (fun history => bindingReward guess history.1.state) ≤
      (assessment.belief who site).expect (fun history =>
        bindingReward (.success (publicGuess view)) history.1.state) := by
  classical
  by_cases hidden : NoPublicAlice view
  · cases guess with
    | failure =>
        rw [show (fun history : (model Claim).InformationHistory who site.1 =>
          bindingReward .failure history.1.state) = (fun _ => -4) from rfl,
          FinDist.expect_const]
        have nonnegative : 0 ≤ (assessment.belief who site).expect (fun history =>
            bindingReward (.success (publicGuess view)) history.1.state) := by
          calc
            0 = (assessment.belief who site).expect (fun _ => 0) :=
              (FinDist.expect_const _ _).symm
            _ ≤ _ := FinDist.expect_mono (fun history _ =>
              bindingReward_success_nonneg (publicGuess view) history.1.state)
        linarith
    | success bit =>
        rw [expected_bindingReward_success, expected_bindingReward_success]
        have equal := fair who site past view observed decision hidden
        cases bit <;> cases publicGuess view <;> exact le_of_eq (by first | rfl | exact equal |
          exact equal.symm)
  · have known := publicGuess_known Claim who past view hidden
    have target : (assessment.belief who site).expect (fun history =>
        bindingReward (.success (publicGuess view)) history.1.state) = 1 := by
      calc
        _ = (assessment.belief who site).expect (fun _ => 1) := by
          apply FinDist.expect_congr
          intro history _
          exact ite_eq_left (known ⟨history.1, history.2.trans observed⟩)
        _ = 1 := FinDist.expect_const _ _
    rw [target]
    exact FinDist.expect_le_of_forall _ _ _
      (fun history _ => bindingReward_le_one guess history.1.state)

theorem prescribed_mixed_guess_optimal (Claim : Type) [Fintype Claim]
    (assessment : (model Claim).BehavioralAssessment) (fair : FairGuessBeliefs Claim assessment)
    (who : Player) (site : (model Claim).InformationSite who)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (observed : site.1 = some (past, view))
    (decision : (who = carol ∧ view.application.visit = some 1) ∨
      (who = bob ∧ view.application.visit = some 2)) (guesses : FinDist (PublicationResult Bool)) :
    (assessment.belief who site).expect (fun history =>
        guesses.expect (fun guess => bindingReward guess history.1.state)) ≤
      (assessment.belief who site).expect (fun history =>
        bindingReward (.success (publicGuess view)) history.1.state) := by
  rw [FinDist.expect_comm]
  exact FinDist.expect_le_of_forall _ _ _ (fun guess _ =>
    prescribed_guess_optimal Claim assessment fair who site past view observed decision guess)

theorem bindingReward_of_alice {Claim : Type} (control : (application Claim).Control)
    (a : PublicationResult Bool) (core : control.execution.application.core = CorePath.alice a)
    (guess : PublicationResult Bool) :
    bindingReward guess (some control) = correctness a guess - openingPenalty guess := by
  cases guess with
  | failure => simp [bindingReward]
  | success bit =>
      have held : hasAliceBit bit (some control) ↔ a = .success bit := by
        change (State.mk control.execution.application.core none 0).owns alice (0, bit) ↔ _
        rw [core, owns_alice]
        simp only [true_and]
      simp only [bindingReward, held]
      cases a <;> simp [correctness]

theorem bindingReward_of_carol {Claim : Type} (control : (application Claim).Control)
    (a c : PublicationResult Bool)
    (core : control.execution.application.core = CorePath.carol a c)
    (guess : PublicationResult Bool) :
    bindingReward guess (some control) = correctness a guess - openingPenalty guess := by
  cases guess with
  | failure => simp [bindingReward]
  | success bit =>
      have held : hasAliceBit bit (some control) ↔ a = .success bit := by
        change (State.mk control.execution.application.core none 0).owns alice (0, bit) ↔ _
        rw [core, owns_carol]
        simp [alice, carol]
      simp only [bindingReward, held]
      cases a <;> simp [correctness]

end VegasTests.SelectiveAssociation.NamedSource
