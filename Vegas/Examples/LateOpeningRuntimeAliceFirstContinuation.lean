/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFirstPacket
import Vegas.Examples.LateOpeningRuntimeAliceFinalSupport
import Vegas.Examples.LateOpeningRuntimeAliceQuietPrefix

/-! # The incumbent continuation after first late silence

Silence at Alice's first late callback reaches her actual final empty callback
through arbitrary legal Bob responses. Global sequential rationality already
forces every supported final response to be a genuine opening. Integrating
that actual continuation supplies a lower bound without replacing any future
policy or restricting hidden histories.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceFirstContinuation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeAliceContinuation LateOpeningRuntimeAliceFirstDecision

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (reward forfeit : ℝ) (deposit : Player → ℝ)
  (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
  (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
  (marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
    weight reward forfeit deposit)
  (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
  (rational : assessment.IsSequentiallyRational
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
      (fun actual => PMF.pure actual) deposit history.state who))

include rational positive rewardNonnegative forfeitNonnegative depositNonnegative marginPositive in
/-- The entire incumbent continuation following first-late silence retains
the genuine final-opening payoff lower bound. -/
theorem deferred_payoff_lower (first : DecisionHistory weight nonnegative)
    (bounded : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨22, some alice, first.execution⟩)) :
    -(1 - LateOpeningRuntimeLateAcceptance.inclusionProbability weight) *
        (forfeit + deposit alice) ≤
      expect (LateOpeningRuntimeAliceFirstPacket.responseLaw weight nonnegative first ⟨none⟩
        (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy))
        (aliceUtility reward forfeit deposit) := by
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  let silent := first.execution.respond app alice ⟨none⟩
  have admissible : ∀ who, rawMenu.Admissible initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who (players who) := by
    intro who
    exact rawMenu.admissible_of_covered initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) players
        (fun actor past view response supported => rawMenu.decode_embedPolicy_covered initial
          LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
            actor (assessment.strategy actor) past view response supported) who
  change _ ≤ expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    players (3 + 19) silent) (aliceUtility reward forfeit deposit)
  rw [app.runRounds_add]
  apply expect_bind_ge_constant_on_support
  · exact aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit depositNonnegative _
  · intro middle reached
    have cursor : middle.environmentRecall.length = 7 := by
      have counts := app.runRounds_environmentRecall_length
        (LateOpeningRuntimeService.scheduler weight nonnegative) players 3 silent middle reached
      have start : silent.environmentRecall.length = 4 := by
        rw [app.respond_environmentRecall]
        exact decision_cursor weight nonnegative first
      omega
    have command : LateOpeningRuntimeService.scheduler weight nonnegative middle.environmentRecall
        (middle.observeEnvironment app) = PMF.pure (.activate alice) := by
      change stageChoice weight nonnegative middle.environmentRecall.length _ = _
      rw [cursor]
      rfl
    change _ ≤ expect ((app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players middle).bind (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        players 18)) (aliceUtility reward forfeit deposit)
    unfold ReactiveApplication.round
    rw [command, PMF.pure_bind]
    unfold ReactiveApplication.dispatch ReactiveApplication.resume
    rw [PMF.bind_bind]
    apply expect_bind_ge_constant_on_support
    · exact aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit
        depositNonnegative _
    · intro next activated
      obtain ⟨final, same, _, ⟨finalTrace⟩⟩ :=
        LateOpeningRuntimeAliceQuietPrefix.final_decision_of_silence weight nonnegative first
          bounded players admissible middle next reached activated
      subst next
      exact LateOpeningRuntimeAliceFinalSupport.final_response_value_lower weight nonnegative
        reward forfeit deposit positive rewardNonnegative forfeitNonnegative depositNonnegative
          marginPositive assessment rational final finalTrace

end Vegas.Examples.LateOpeningRuntimeAliceFirstContinuation
