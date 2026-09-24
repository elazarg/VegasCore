/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.SequentialEquilibrium
import GameTheoryExtensionsTests.OffPathDisclosureLaws
import GameTheoryExtensions.Analysis.Protocol.DisclosureObstruction

/-! # Off-path disclosure obstructs utility-independent sequential compilation

The source has a sequential equilibrium for both opposite guessing utilities,
with the same strategy, beliefs and consistency witness. In the disclosed game,
no single strategy admits rational assessments for both utilities, even allowing
different beliefs for each. This is an abstract information-model obstruction;
it does not assert that the native runtime implements this disclosure.
-/

noncomputable section

namespace GameTheoryExtensionsTests.SequentialDisclosure

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol OffPathDisclosure

def bobSite (bit : Bool) : (model true).InformationSite true :=
  (model true).informationSite true (bobHistory bit) false (by exact id) rfl

theorem history_at_bob (bit : Bool)
    (history : (model true).InformationHistory true (bobSite bit).1) :
    history.1 = bobHistory bit := by
  have observed := history.2
  rw [info_state] at observed
  have known : Classified history.1 := classified history.1.trace
  rcases known with same | ⟨other, same⟩ | ⟨other, same⟩ |
    ⟨other, same⟩ | ⟨other, guess, same⟩
  all_goals rw [same] at observed
  all_goals try cases observed
  exact same

instance (bit : Bool) : Subsingleton ((model true).InformationHistory true (bobSite bit).1) :=
  ⟨fun first second => Subtype.ext
    ((history_at_bob bit first).trans (history_at_bob bit second).symm)⟩

theorem antichain : (model true).DecisionInformationAntichain := by
  have length_at_decision (who : Bool) (history : arena.History)
      (active : arena.active history.state who) :
      history.trace.length = if who then 2 else 1 := by
    have known : Classified history := classified history.trace
    rcases known with rfl | ⟨bit, rfl⟩ | ⟨bit, rfl⟩ |
      ⟨bit, rfl⟩ | ⟨bit, guess, rfl⟩
    all_goals cases who
    all_goals simp_all [arena, actor, aliceHistory, bobHistory, stopHistory, guessHistory,
      aliceJoint, bobJoint, History.extend, initHistory, Trace.length]
  intro who site first second joint legal target realized fuel path
  have firstLength := length_at_decision who first.1
    (InformationModel.InformationSite.active _ site first)
  have secondLength := length_at_decision who second.1
    (InformationModel.InformationSite.active _ site second)
  have increases := path.trace_length_le
  change first.1.trace.length + 1 ≤ second.1.trace.length at increases
  omega

theorem continuation_value (assessment : (model true).BehavioralAssessment)
    (bit : Bool) (u : arena.History → ℝ) (alternative : (model true).BehavioralPolicy true) :
    (assessment.continuationContext (bobSite bit) u 3).value alternative =
      ((model true).runSingleMoverBehavioralFrom single
        (Profile.update (sig := (model true).behavioralSignature)
          assessment.strategy true alternative) 3 (bobHistory bit)).expect u := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    FinDist.eq_pure_of_subsingleton (assessment.belief true (bobSite bit))
      ⟨bobHistory bit, rfl⟩, FinDist.pure_bind,
    ← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom (model true) single]

/-- Disclosure leaves a singleton history at Bob's decision, so the actual
continuation has a common binary law and Bob can force either outcome. -/
def disclosedDecision : (model true).BinaryDecision (fun goal who history =>
    payoff goal history who) 3 where
  player := true
  site := bobSite false
  outcome profile := (choiceLaw profile true (some false)).map (fun guess => guess == false)
  policy goal := choose true true (!goal)
  history_value profile goal history := by
    rw [history_at_bob false history,
      ← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom (model true) single]
    unfold payoff
    rw [value_bob profile false (utility goal · true)]
    simp only [resultLaw, FinDist.expect_map, utility, ↓reduceIte]
  force profile goal := by
    cases goal <;> simp [choiceLaw, Profile.update, choose]

theorem rationality_forces_payoff_one (assessment : (model true).BehavioralAssessment)
    (matchBit : Bool)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => payoff matchBit history who) 3) :
    1 ≤ ((model true).runSingleMoverBehavioralFrom single assessment.strategy 3
      (bobHistory false)).expect (payoff matchBit · true) := by
  unfold payoff
  rw [value_bob assessment.strategy false (utility matchBit · true)]
  simpa only [disclosedDecision, resultLaw, FinDist.expect_map, utility, ↓reduceIte] using
    disclosedDecision.rational_value assessment matchBit rational

/-- Beliefs may depend on the utility. Even this freedom cannot rationalize
one target strategy for both opposite utilities. -/
theorem no_common_rational_strategy : ¬ ∃ first second : (model true).BehavioralAssessment,
    first.strategy = second.strategy ∧
      first.IsSequentiallyRationalWithin (fun who history => payoff true history who) 3 ∧
      second.IsSequentiallyRationalWithin (fun who history => payoff false history who) 3 :=
  disclosedDecision.no_common_rational_strategy

/-- A whole-profile translator has more access than a playerwise compiler.
Impossibility already holds for this more permissive class of translators. -/
theorem no_utility_independent_sequential_translation : ¬ ∃ translate :
    Profile (model false).behavioralSignature → Profile (model true).behavioralSignature,
    ∀ matchBit,
      (SequentialBeliefs.assessment SequentialBeliefs.limitProfile).IsSequentialEquilibriumFor
        SequentialBeliefs.antichain (fun who site =>
          (SequentialBeliefs.assessment SequentialBeliefs.limitProfile).continuationContext site
            (fun history => payoff matchBit history who) 3) →
      ∃ target : (model true).BehavioralAssessment,
        target.strategy = translate SequentialBeliefs.limitProfile ∧
          target.IsSequentialEquilibriumFor antichain (fun who site =>
            target.continuationContext site (fun history => payoff matchBit history who) 3) :=
  disclosedDecision.no_utility_independent_sequential_translation
    (SequentialBeliefs.assessment SequentialBeliefs.limitProfile)
    SequentialBeliefs.antichain antichain (fun goal who history => payoff goal history who)
    3 SequentialBeliefs.sequential_equilibrium_guessing

end GameTheoryExtensionsTests.SequentialDisclosure
