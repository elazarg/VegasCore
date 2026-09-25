/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.AmbientEnforcement

/-! # Decision information in the ambient-disclosure experiment -/

noncomputable section

namespace GameTheoryExtensionsTests.AmbientEnforcement

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

def aliceSite (bit : Bool) : (model true).InformationSite false :=
  (model true).informationSite false (aliceHistory true bit) false (by exact id) rfl

def bobSilentSite (ambient : Bool) : (model ambient).InformationSite true :=
  (model ambient).informationSite true (bobHistory ambient false false) false
    (by exact id) (by cases ambient <;> rfl)

def bobDisclosedSite (bit : Bool) : (model true).InformationSite true :=
  (model true).informationSite true (bobHistory true bit true) false (by exact id) rfl

theorem history_at_alice (bit : Bool)
    (history : (model true).InformationHistory false (aliceSite bit).1) :
    history.1 = aliceHistory true bit := by
  have observed := history.2
  rw [info_state] at observed
  have known : Classified true history.1 := classified true history.1.trace
  rcases known with same | ⟨other, same⟩ | ⟨other, ask, same⟩ |
    ⟨other, ask, guess, same⟩
  all_goals rw [same] at observed
  all_goals try cases observed
  exact same

theorem history_at_disclosed (bit : Bool)
    (history : (model true).InformationHistory true (bobDisclosedSite bit).1) :
    history.1 = bobHistory true bit true := by
  have observed := history.2
  rw [info_state] at observed
  have known : Classified true history.1 := classified true history.1.trace
  rcases known with same | ⟨other, same⟩ | ⟨other, ask, same⟩ |
    ⟨other, ask, guess, same⟩
  all_goals rw [same] at observed
  all_goals try cases observed
  cases ask
  · cases observed
  · cases observed
    exact same

theorem history_at_silent (ambient : Bool)
    (history : (model ambient).InformationHistory true (bobSilentSite ambient).1) :
    ∃ bit, history.1 = bobHistory ambient bit false := by
  have observed := history.2
  rw [info_state] at observed
  have known : Classified ambient history.1 := classified ambient history.1.trace
  rcases known with same | ⟨bit, same⟩ | ⟨bit, ask, same⟩ |
    ⟨bit, ask, guess, same⟩
  all_goals rw [same] at observed
  all_goals try cases observed
  cases ambient
  · exact ⟨bit, same⟩
  · cases ask
    · exact ⟨bit, same⟩
    · cases observed

instance (bit : Bool) :
    Subsingleton ((model true).InformationHistory false (aliceSite bit).1) :=
  ⟨fun first second => Subtype.ext
    ((history_at_alice bit first).trans (history_at_alice bit second).symm)⟩

instance (bit : Bool) :
    Subsingleton ((model true).InformationHistory true (bobDisclosedSite bit).1) :=
  ⟨fun first second => Subtype.ext
    ((history_at_disclosed bit first).trans (history_at_disclosed bit second).symm)⟩

theorem alice_site_eq (decision : (model true).InformationSite false) :
    ∃ bit, decision = aliceSite bit := by
  obtain ⟨history, _, _, _⟩ := decision.2
  have active := InformationModel.InformationSite.active (model true) decision history
  have known : Classified true history.1 := classified true history.1.trace
  rcases known with same | ⟨bit, same⟩ | ⟨bit, ask, same⟩ | ⟨bit, ask, guess, same⟩
  all_goals rw [same] at active
  all_goals try simp [arena, actor, aliceHistory, bobHistory, guessHistory,
    aliceJoint, bobJoint] at active
  refine ⟨bit, Subtype.ext ?_⟩
  have observed := history.2.symm
  rw [same] at observed
  exact observed

theorem bob_site_cases (ambient : Bool) (decision : (model ambient).InformationSite true) :
    decision = bobSilentSite ambient ∨
      ∃ bit, ambient = true ∧ decision.1 = some (some bit) := by
  obtain ⟨history, _, _, _⟩ := decision.2
  have active := InformationModel.InformationSite.active (model ambient) decision history
  have known : Classified ambient history.1 := classified ambient history.1.trace
  rcases known with same | ⟨bit, same⟩ | ⟨bit, ask, same⟩ | ⟨bit, ask, guess, same⟩
  all_goals rw [same] at active
  all_goals try simp [arena, actor, aliceHistory, bobHistory, guessHistory,
    aliceJoint, bobJoint] at active
  have observed := history.2.symm
  rw [same] at observed
  cases ambient
  · exact Or.inl (Subtype.ext observed)
  · cases ask
    · exact Or.inl (Subtype.ext observed)
    · exact Or.inr ⟨bit, rfl, observed⟩

theorem target_bob_site_eq (decision : (model true).InformationSite true) :
    decision = bobSilentSite true ∨ ∃ bit, decision = bobDisclosedSite bit := by
  rcases bob_site_cases true decision with same | ⟨bit, _, same⟩
  · exact Or.inl same
  · exact Or.inr ⟨bit, Subtype.ext same⟩

theorem source_bob_site_eq (decision : (model false).InformationSite true) :
    decision = bobSilentSite false := by
  rcases bob_site_cases false decision with same | ⟨_, impossible, _⟩
  · exact same
  · cases impossible

theorem source_no_alice_site (decision : (model false).InformationSite false) : False := by
  obtain ⟨history, _, _, _⟩ := decision.2
  have active := InformationModel.InformationSite.active (model false) decision history
  cases state : history.1.state <;> simp_all [arena, actor]

def silentHistory (ambient bit : Bool) :
    (model ambient).InformationHistory true (bobSilentSite ambient).1 :=
  ⟨bobHistory ambient bit false, by cases ambient <;> rfl⟩

theorem silentHistory_injective (ambient : Bool) : Function.Injective (silentHistory ambient) := by
  intro first second same
  have states := congrArg (fun history => history.1.state) same
  change State.bob first _ = State.bob second _ at states
  exact (State.bob.inj states).1

def silentHistories (ambient : Bool) :
    Bool ≃ (model ambient).InformationHistory true (bobSilentSite ambient).1 :=
  Equiv.ofBijective (silentHistory ambient) ⟨silentHistory_injective ambient, fun history => by
    obtain ⟨bit, same⟩ := history_at_silent ambient history
    exact ⟨bit, Subtype.ext same.symm⟩⟩

theorem alice_context (assessment : (model true).BehavioralAssessment) (bit : Bool)
    (utility : State → ℝ) (alternative : (model true).BehavioralPolicy false) :
    (assessment.continuationContext (aliceSite bit) (fun h => utility h.state) 3).value
        alternative =
      ((model true).runSingleMoverBehavioralFrom (single true)
        (Profile.update (sig := (model true).behavioralSignature)
          assessment.strategy false alternative) 3 (aliceHistory true bit)).expect
            (fun h => utility h.state) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    FinDist.eq_pure_of_subsingleton (assessment.belief false (aliceSite bit))
      ⟨aliceHistory true bit, rfl⟩, FinDist.pure_bind,
    ← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom (model true) (single true)]

theorem disclosed_context (assessment : (model true).BehavioralAssessment) (bit : Bool)
    (utility : State → ℝ) (alternative : (model true).BehavioralPolicy true) :
    (assessment.continuationContext (bobDisclosedSite bit) (fun h => utility h.state) 3).value
        alternative =
      ((model true).runSingleMoverBehavioralFrom (single true)
        (Profile.update (sig := (model true).behavioralSignature)
          assessment.strategy true alternative) 3 (bobHistory true bit true)).expect
            (fun h => utility h.state) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    FinDist.eq_pure_of_subsingleton (assessment.belief true (bobDisclosedSite bit))
      ⟨bobHistory true bit true, rfl⟩, FinDist.pure_bind,
    ← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom (model true) (single true)]

theorem value_bob {ambient : Bool} (profile : Profile (model ambient).behavioralSignature)
    (bit disclose : Bool) (utility : State → ℝ) :
    ((model ambient).runSingleMoverBehavioralFrom (single ambient) profile 3
      (bobHistory ambient bit disclose)).expect (fun h => utility h.state) =
        (resultLaw profile bit (ambient && disclose)).expect utility := by
  have mapped := congrArg (fun law => law.expect utility) (run_bob profile bit disclose)
  simpa only [FinDist.expect_map] using mapped

theorem value_alice {ambient : Bool} (profile : Profile (model ambient).behavioralSignature)
    (bit : Bool) (utility : State → ℝ) :
    ((model ambient).runSingleMoverBehavioralFrom (single ambient) profile 3
      (aliceHistory ambient bit)).expect (fun h => utility h.state) =
        (choiceLaw profile false (some (some bit))).expect
          (fun disclose => (resultLaw profile bit (ambient && disclose)).expect utility) := by
  have mapped := congrArg (fun law => law.expect utility) (run_alice profile bit)
  simpa only [FinDist.expect_map, FinDist.expect_bind] using mapped

end GameTheoryExtensionsTests.AmbientEnforcement
