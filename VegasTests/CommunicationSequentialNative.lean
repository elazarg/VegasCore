/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationImpossibility
import Interaction.ReactiveFiniteAssessment

/-! # Optimal native responses to authenticated disclosure

One observation-based policy responds to either disclosed bit. At each actual
disclosure information set it realizes the selected guess, throughout the
entire information fiber and against every legal response deviation. For the
matching or mismatching objective it attains the maximum continuation payoff,
independently of beliefs.

The full sequential-equilibrium construction, including information sets
without authenticated disclosure, is in `CommunicationSequentialEquilibrium`.
-/

noncomputable section

namespace VegasTests.CommunicationSequentialNative

open Vegas Vegas.EventGraphRuntime Interaction GameTheory
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open SequentialValidation

/-- A positive authenticated opening determines the bit. The default only
specifies behavior at views outside the two certified information fibers. -/
def disclosedBit (view : nativeApp.PlayerView) : Bool := by
  classical
  exact decide (nativeRuntime.openingObserved nativeLeaks view
    (false, .initial secretInput) ⟨.bool, true⟩)

theorem disclosedBit_actual (bit : Bool) :
    disclosedBit ((nativeBobExecution bit).observe nativeApp true) = bit := by
  classical
  cases bit with
  | true => simp [disclosedBit, native_bob_observed true]
  | false =>
      have absent : ¬ nativeRuntime.openingObserved nativeLeaks
          ((nativeBobExecution false).observe nativeApp true)
          (false, .initial secretInput) ⟨.bool, true⟩ := by
        intro observed
        have stored := native_information_type nativeLeaks nativeMenu 56 nativeScheduler
          true true [] ((nativeBobExecution false).observe nativeApp true) observed
          ⟨nativeBobHistory false, native_bob_info false⟩
        have known := native_bob_type false
          ⟨nativeBobHistory false, rfl⟩
        rw [known] at stored
        cases stored
      simp [disclosedBit, absent]

/-- The translation receives a response function, not a utility or belief. -/
def evidencePolicy (answer : Bool → Bool) : nativeModel.BehavioralPolicy true := fun info =>
  match info with
  | none => FinDist.pure ⟨none, rfl⟩
  | some (past, view) =>
      let guess := answer (disclosedBit view)
      FinDist.pure ⟨some ⟨some (.submit (nativeGuessSubmission guess))⟩,
        ⟨_, native_guess_available guess past view, rfl⟩⟩

theorem evidencePolicy_guess (profile : Profile nativeModel.behavioralSignature)
    (answer : Bool → Bool) (bit : Bool) :
    nativeGuessLaw (Profile.update (sig := nativeModel.behavioralSignature)
      profile true (evidencePolicy answer)) bit = FinDist.pure (answer bit) := by
  simp only [nativeGuessLaw, nativePlayers, ReactiveApplication.ResponseMenu.decodeProfile,
    ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
    Profile.update, Function.update_self, evidencePolicy, disclosedBit_actual,
    FinDist.map_pure, FinDist.pure_bind]
  exact native_tail_guess bit (answer bit)

def winningAnswer (matchBit bit : Bool) : Bool := if matchBit then bit else !bit

theorem evidencePolicy_value (assessment : nativeModel.BehavioralAssessment)
    (matchBit bit : Bool) :
    (assessment.continuationContext (nativeBobSite bit) (nativePayoff matchBit true) 113).value
      (evidencePolicy (winningAnswer matchBit)) = 1 := by
  rw [native_continuation_value, evidencePolicy_guess, FinDist.expect_pure]
  cases matchBit <;> cases bit <;> rfl

/-- The policy is optimal against every legal continuation policy, not just
against the other guess packet. No assumption on off-path beliefs is used. -/
theorem evidencePolicy_optimal (assessment : nativeModel.BehavioralAssessment)
    (matchBit bit : Bool) (alternative : nativeModel.BehavioralPolicy true) :
    (assessment.continuationContext (nativeBobSite bit) (nativePayoff matchBit true) 113).value
      alternative ≤
    (assessment.continuationContext (nativeBobSite bit) (nativePayoff matchBit true) 113).value
      (evidencePolicy (winningAnswer matchBit)) := by
  rw [evidencePolicy_value, native_continuation_value]
  apply FinDist.expect_le_of_forall
  intro guess _
  split <;> norm_num

end VegasTests.CommunicationSequentialNative
