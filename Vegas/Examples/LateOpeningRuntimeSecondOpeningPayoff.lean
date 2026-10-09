/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeFirstSettlementContinuation
import Vegas.Examples.LateOpeningRuntimeEarlyResponseLaw
import Vegas.Examples.LateOpeningRuntimeAliceFinalSupport

/-! # Complete native payoff law after first late silence

An actual rational profile is silent at the early receiver activation and
emits a genuine opening at the sender's empty final activation. Keeping
both original policies and all private aliases, first late silence has
exactly the canonical second-opening payoff distribution.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeSecondOpeningPayoff

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLateAcceptance LateOpeningRuntimeLatePrefixKernel
  LateOpeningRuntimeLateResponseKernel LateOpeningRuntimeSettlementContinuation
  LateOpeningRuntimeFirstRetryComparison

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
theorem final_genuine_payoff_law (bit : Bool) (label : Fin 3) :
    ((finalResponseLaw weight nonnegative bit label ⟨none⟩ ∅
      (players weight nonnegative assessment.strategy)).bind
        (receiverCompletion weight nonnegative
          (players weight nonnegative assessment.strategy))).map
          (fun final => LateOpeningRuntimeNash.payoff reward forfeit
            (fun actual => PMF.pure actual) deposit (app.finished final) alice) =
      (settlementCompletion weight nonnegative (players weight nonnegative assessment.strategy)
        (beforeLottery bit label 1 false)).map (fun final => LateOpeningRuntimeNash.payoff
          reward forfeit (fun actual => PMF.pure actual) deposit (app.finished final) alice) := by
  classical
  unfold finalResponseLaw
  rw [PMF.bind_bind, PMF.map_bind]
  calc
    _ = (finalResponses bit label ⟨none⟩ ∅
        (players weight nonnegative assessment.strategy)).bind fun _ =>
          (settlementCompletion weight nonnegative (players weight nonnegative assessment.strategy)
            (beforeLottery bit label 1 false)).map (fun final =>
              LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
                deposit (app.finished final) alice) := by
      apply bind_congr_on_support
      intro response supported
      have finalState : finalDecision bit label ⟨none⟩ ∅ =
          secondLateDecision bit label 1 false := rfl
      have genuine := LateOpeningRuntimeAliceFinalSupport.decoded_response_genuine weight
        nonnegative reward forfeit deposit positive rewardNonnegative forfeitNonnegative
          depositNonnegative marginPositive assessment rational
            (LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label)
            (LateOpeningRuntimeAliceEmptyWitness.secondLateDecision_trace weight nonnegative
              bit label).some response (by
                change response ∈ (players weight nonnegative assessment.strategy alice
                  ((secondLateDecision bit label 1 false).recall alice)
                  ((secondLateDecision bit label 1 false).observe app alice)).support
                simpa only [finalResponses, finalState] using supported)
      rcases response with ⟨transmission⟩
      cases transmission with
      | none => exact genuine.elim
      | some submission =>
          have law := genuine_final_payoff_law weight nonnegative
            (players weight nonnegative assessment.strategy) bit label submission genuine
              reward forfeit deposit (fun actual => PMF.pure actual) alice
          rw [whole_suffix_law weight nonnegative _ _ (by
            change (finalDecision bit label ⟨none⟩ ∅).environmentRecall.length = 8
            exact final_cursor bit label ⟨none⟩ ∅)] at law
          simpa only [settlementCompletion] using law
    _ = _ := PMF.bind_const _ _

include rational positive rewardNonnegative forfeitNonnegative depositNonnegative marginPositive in
theorem first_silence_payoff_law (collateral : 1 < deposit bob)
    (bit : Bool) (label : Fin 3) :
    (LateOpeningRuntimeAliceFirstPacket.responseLaw weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        ⟨none⟩ (players weight nonnegative assessment.strategy)).map
          (fun final => LateOpeningRuntimeNash.payoff reward forfeit
            (fun actual => PMF.pure actual) deposit (app.finished final) alice) =
      (settlementCompletion weight nonnegative (players weight nonnegative assessment.strategy)
        (beforeLottery bit label 1 false)).map (fun final => LateOpeningRuntimeNash.payoff
          reward forfeit (fun actual => PMF.pure actual) deposit (app.finished final) alice) := by
  have quiet := LateOpeningRuntimeEarlyResponseLaw.sequentially_rational_response_law
    weight nonnegative reward forfeit deposit forfeitNonnegative collateral assessment rational
      bit label 1 false (Or.inr rfl)
  rw [LateOpeningRuntimeFirstSettlementContinuation.response_completion_law,
    silent_first_binding_law]
  unfold ReactiveApplication.invoke
  rw [PMF.bind_map]
  change (((players weight nonnegative assessment.strategy bob
    ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 1 false).recall bob)
    ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 1 false).observe app bob)).bind
      fun response => afterEarly weight nonnegative (players weight nonnegative assessment.strategy)
        ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 1 false).respond app bob
          response)).bind
          (receiverCompletion weight nonnegative
            (players weight nonnegative assessment.strategy))).map _ = _
  rw [quiet, PMF.pure_bind]
  change ((afterEarly weight nonnegative (players weight nonnegative assessment.strategy)
    (earlyQuiet bit label ⟨none⟩ ∅)).bind _).map _ = _
  rw [after_early_quiet_law]
  exact final_genuine_payoff_law weight nonnegative reward forfeit deposit positive
    rewardNonnegative forfeitNonnegative depositNonnegative marginPositive assessment rational
      bit label

end Vegas.Examples.LateOpeningRuntimeSecondOpeningPayoff
