/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit
import Vegas.Examples.LateOpeningRuntimeBobBindingOptimization
import Vegas.Examples.LateOpeningRuntimeBobDirtyOptimization

/-! # Receiver binding rationality under all-or-none traffic audit

The public omission surcharge gives one-sided comparison with full audit at
scaled deposits. Genuine whole-answer continuations attain the scaled bound
on quiet failed-publication and dirty successful-publication information sites.
This yields local rationality with the original assessment and future opponents
on every compatible legal history, without positive-belief restrictions.
-/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeAllOrNoneBinding
open LateOpeningRuntimeAllOrNoneTrafficAudit

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Enforcement GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeUtility

theorem bob_payoff_le_scaled (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (reward forfeit : ℝ) (deposit : Player → ℝ)
    (collateral : 0 ≤ deposit bob) (control : app.Control) :
    LateOpeningRuntimeGame.payoff reward forfeit (sample probability nonnegative bounded)
        deposit (some control) bob ≤
      LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
        (fun owner => probability * deposit owner) (some control) bob := by
  rw [payoff]
  apply sub_le_self
  split
  · exact mul_nonneg (sub_nonneg.mpr bounded) collateral
  · exact le_rfl

theorem bob_state_payoff_le_scaled (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (reward forfeit : ℝ) (deposit : Player → ℝ)
    (collateral : 0 ≤ deposit bob) (state : app.ProtocolState) :
    LateOpeningRuntimeGame.payoff reward forfeit (sample probability nonnegative bounded)
        deposit state bob ≤
      LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
        (fun owner => probability * deposit owner) state bob := by
  cases state with
  | some control =>
      exact bob_payoff_le_scaled probability nonnegative bounded reward forfeit
        deposit collateral control
  | none => simp [LateOpeningRuntimeGame.payoff, TerminalAudit.utility, TerminalAudit.charge,
      EventGraphRuntime.serviceAuditObservation, serviceSourceAudit,
      EventGraphRuntime.serviceAudit, PMF.pure_map]

/-- Every whole-policy value under the actual sampler is bounded by its scaled
full-audit value, with the same continuation runner and assessment. -/
theorem context_value_le_scaled (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ) (collateral : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (run : (LateOpeningRuntimeGame.model weight weightNonnegative).ContinuationRunner)
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite bob)
    (choice : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralPolicy bob) :
    (assessment.continuationContextWith run site
      (fun history => LateOpeningRuntimeGame.payoff reward forfeit
        (sample probability nonnegative bounded) deposit history.state bob)).value choice ≤
      (assessment.continuationContextWith run site
        (fun history => LateOpeningRuntimeGame.payoff reward forfeit
          (fun actual => PMF.pure actual) (fun owner => probability * deposit owner)
            history.state bob)).value choice := by
  apply expect_mono
    (fun history _ => bob_state_payoff_le_scaled probability nonnegative bounded reward forfeit
      deposit collateral history.state)
  · exact payoffIntegrable_of_bounded _ _ fun history =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
        (sample probability nonnegative bounded) deposit history.state
  · exact payoffIntegrable_of_bounded _ _ fun history =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
        (fun actual => PMF.pure actual) (fun owner => probability * deposit owner) history.state

theorem bob_expect_le_scaled (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (reward forfeit : ℝ) (deposit : Player → ℝ)
    (collateral : 0 ≤ deposit bob) (law : PMF app.Execution) :
    expect law (fun final => LateOpeningRuntimeGame.payoff reward forfeit
      (sample probability nonnegative bounded) deposit (app.finished final) bob) ≤
      expect law (fun final => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) (fun owner => probability * deposit owner)
          (app.finished final) bob) := by
  apply expect_mono
    (fun final _ => bob_payoff_le_scaled probability nonnegative bounded reward forfeit
      deposit collateral ⟨0, none, final⟩)
  · exact payoffIntegrable_of_bounded _ _ fun final =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
        (sample probability nonnegative bounded) deposit (app.finished final)
  · exact payoffIntegrable_of_bounded _ _ fun final =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
        (fun actual => PMF.pure actual) (fun owner => probability * deposit owner)
          (app.finished final)

/-- Before binding after Alice's failure, every actual response under every
compatible belief history is bounded by the scaled full-audit best guess.
Future strategies and the assessment's entire information fiber are retained. -/
theorem failed_binding_response_le_bestGuessValue
    (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationHistory
      bob site.1)
    (decision : LateOpeningRuntimeBobBindingInformation.DecisionHistory weight weightNonnegative)
    (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (response : app.Action) :
    expect (assessment.belief bob site) (fun history =>
      expect (app.runRounds (LateOpeningRuntimeService.scheduler weight weightNonnegative)
        (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight weightNonnegative) assessment.strategy) 14
        ((LateOpeningRuntimeBobBindingInformation.decisionOfInformation weight weightNonnegative
          site representative decision current history).execution.respond app bob response))
        (fun final => LateOpeningRuntimeGame.payoff reward forfeit
          (sample probability nonnegative bounded) deposit (app.finished final) bob)) ≤
      LateOpeningRuntimeBobBindingOptimization.bestGuessValue weight weightNonnegative site
        reward forfeit (fun owner => probability * deposit owner) assessment := by
  apply le_trans _ (LateOpeningRuntimeBobBindingOptimization.responseValue_le_bestGuessValue
    weight weightNonnegative site representative decision current reward forfeit
      (fun owner => probability * deposit owner) forfeitNonnegative
      (mul_nonneg nonnegative collateral) assessment response)
  unfold LateOpeningRuntimeBobBindingOptimization.responseValue
  apply expect_mono
    (fun history _ => bob_expect_le_scaled probability nonnegative bounded reward forfeit
      deposit collateral _)
  · exact payoffIntegrable_of_bounded _ _ fun history =>
      expect_abs_le_of_bounded (by positivity) fun final =>
        LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
          (sample probability nonnegative bounded) deposit (app.finished final)
  · exact payoffIntegrable_of_bounded _ _ fun history =>
      expect_abs_le_of_bounded (by positivity) fun final =>
        LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
          (fun actual => PMF.pure actual) (fun owner => probability * deposit owner)
            (app.finished final)

/-- The same actual pre-binding domination covers successful Alice publication
with earlier rejected Bob traffic, preserving all legal compatible histories. -/
theorem dirty_binding_response_le_bestAnswerValue
    (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationHistory
      bob site.1)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight weightNonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (current : representative.1.state = some ⟨14, some bob, execution⟩)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (dirty : ¬ LateOpeningRuntimeBobBindingService.SilentRecall execution) (bit : Bool)
    (published : execution.application.config.store (.inr aliceEvent) =
      some (.success bit : PublicationResult Bool))
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (response : app.Action) :
    expect (assessment.belief bob site) (fun history =>
      expect (app.runRounds (LateOpeningRuntimeService.scheduler weight weightNonnegative)
        (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight weightNonnegative) assessment.strategy) 14
        ((LateOpeningRuntimeBobDirtyContext.executionOfInformation weight weightNonnegative
          site representative execution trace ready current history).respond app bob response))
        (fun final => LateOpeningRuntimeGame.payoff reward forfeit
          (sample probability nonnegative bounded) deposit (app.finished final) bob)) ≤
      LateOpeningRuntimeBobDirtyOptimization.bestAnswerValue weight weightNonnegative site
        reward forfeit (fun owner => probability * deposit owner) assessment := by
  apply le_trans _ (LateOpeningRuntimeBobDirtyOptimization.responseValue_le_bestAnswerValue
    weight weightNonnegative site representative execution trace ready current reward forfeit
      (fun owner => probability * deposit owner) timely dirty bit published forfeitNonnegative
      assessment response)
  unfold LateOpeningRuntimeBobDirtyContext.responseValue
  apply expect_mono
    (fun history _ => bob_expect_le_scaled probability nonnegative bounded reward forfeit
      deposit collateral _)
  · exact payoffIntegrable_of_bounded _ _ fun history =>
      expect_abs_le_of_bounded (by positivity) fun final =>
        LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
          (sample probability nonnegative bounded) deposit (app.finished final)
  · exact payoffIntegrable_of_bounded _ _ fun history =>
      expect_abs_le_of_bounded (by positivity) fun final =>
        LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
          (fun actual => PMF.pure actual) (fun owner => probability * deposit owner)
            (app.finished final)

open LateOpeningRuntimeBobBindingDecision LateOpeningRuntimeBobBindingInformation
  LateOpeningRuntimeBobAnswerPayoff LateOpeningRuntimeEarlyBobSafeMenu in
/-- A genuine whole-answer policy attains its actual bit score under the sampler
on every compatible history, with the original foreign continuation retained. -/
theorem failed_answer_context_value
    (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationHistory
      bob site.1)
    (decision : LateOpeningRuntimeBobBindingInformation.DecisionHistory weight weightNonnegative)
    (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (answer : Answer) :
    (assessment.truncatedContinuationContext site
      (fun history => LateOpeningRuntimeGame.payoff reward forfeit
        (sample probability nonnegative bounded) deposit history.state bob)
      (2 * LateOpeningRuntimeService.horizon + 1)).value
        (answerFinitePolicy weight weightNonnegative answer) =
      expect (assessment.belief bob site) (fun history =>
        if answer.val = (if originalBit (decisionOfInformation weight weightNonnegative site
          representative decision current history).execution then 5 else 4) then 1 else 0) := by
  let auditContext := assessment.truncatedContinuationContext site
    (fun history => LateOpeningRuntimeGame.payoff reward forfeit
      (sample probability nonnegative bounded) deposit history.state bob)
    (2 * LateOpeningRuntimeService.horizon + 1)
  have mapped := expect_map History.state
    ((context weight weightNonnegative site reward forfeit deposit assessment).outcome
      (answerFinitePolicy weight weightNonnegative answer))
    (fun state => LateOpeningRuntimeGame.payoff reward forfeit
      (sample probability nonnegative bounded)
      deposit state bob)
  rw [answer_context_outcome_law weight weightNonnegative site representative decision current,
    expect_map] at mapped
  have nativeValue : auditContext.value
      (answerFinitePolicy weight weightNonnegative answer) =
      expect (answerFinalLaw weight weightNonnegative site representative decision current
        assessment answer) (fun final => LateOpeningRuntimeGame.payoff reward forfeit
          (sample probability nonnegative bounded) deposit (app.finished final) bob) := mapped.symm
  rw [nativeValue]
  unfold answerFinalLaw
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ fun final =>
    LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
      (sample probability nonnegative bounded)
      deposit (app.finished final))]
  apply expect_congr_on_support
  intro history _
  let recovered :=
    decisionOfInformation weight weightNonnegative site representative decision current history
  calc
    _ = expect _ (fun _ => if answer.val =
        (if originalBit recovered.execution then 5 else 4) then (1 : ℝ) else 0) := by
      apply expect_congr_on_support
      intro final reached
      exact failed_answer_continuation_payoff weight weightNonnegative recovered answer
        (answerPlayers weight weightNonnegative assessment answer)
        (by simp only [answerPlayers, Function.update_self]) reward forfeit deposit
        (sample probability nonnegative bounded)
        (sample_authentic probability nonnegative bounded) final reached
    _ = _ := expect_constant _ _

open LateOpeningRuntimeBobBindingDecision LateOpeningRuntimeBobBindingInformation
  LateOpeningRuntimeEarlyBobSafeMenu in
/-- Actual sampled rationality at every failed-publication binding fiber gives
Bob at least one half, without any lower bound on the fiber's belief mass. -/
theorem rational_failed_binding_value_ge_half
    (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationHistory
      bob site.1)
    (decision : LateOpeningRuntimeBobBindingInformation.DecisionHistory weight weightNonnegative)
    (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.truncatedContinuationContext site
        (fun history => LateOpeningRuntimeGame.payoff reward forfeit
          (sample probability nonnegative bounded) deposit history.state bob)
        (2 * LateOpeningRuntimeService.horizon + 1))) :
    (1 / 2 : ℝ) ≤ (assessment.truncatedContinuationContext site
      (fun history => LateOpeningRuntimeGame.payoff reward forfeit
        (sample probability nonnegative bounded) deposit history.state bob)
      (2 * LateOpeningRuntimeService.horizon + 1)).value (assessment.strategy bob) := by
  let auditContext := assessment.truncatedContinuationContext site
    (fun history => LateOpeningRuntimeGame.payoff reward forfeit
      (sample probability nonnegative bounded) deposit history.state bob)
    (2 * LateOpeningRuntimeService.horizon + 1)
  have integrable (choice) : auditContext.IntegrableAt choice :=
    payoffIntegrable_of_bounded _ _ fun history =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
        (sample probability nonnegative bounded) deposit history.state
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (integrable (assessment.strategy bob)) (fun choice _ => integrable choice)).mp rational
  obtain ⟨bit, lower⟩ := exists_bit_guess_value_ge_half weight weightNonnegative site
    representative decision current reward forfeit deposit assessment
  have equal : auditContext.value (answerFinitePolicy weight weightNonnegative (bitGuess bit)) =
      (context weight weightNonnegative site reward forfeit deposit assessment).value
        (answerFinitePolicy weight weightNonnegative (bitGuess bit)) := by
    rw [failed_answer_context_value probability nonnegative bounded weight weightNonnegative
      site representative decision current reward forfeit deposit assessment,
      answer_context_value weight weightNonnegative site representative decision current]
  exact lower.trans (equal ▸ comparison (answerFinitePolicy weight weightNonnegative
    (bitGuess bit)) (Set.mem_univ _))

open LateOpeningRuntimeBobBindingDecision LateOpeningRuntimeBobBindingInformation
  LateOpeningRuntimeBobBindingOptimization in
theorem failed_binding_full_value_le_bestGuessValue
    (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationHistory
      bob site.1)
    (decision : LateOpeningRuntimeBobBindingInformation.DecisionHistory weight weightNonnegative)
    (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (choice : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralPolicy bob) :
    (context weight weightNonnegative site reward forfeit deposit assessment).value choice ≤
      bestGuessValue weight weightNonnegative site reward forfeit deposit assessment := by
  let changedStrategy := Profile.update
    (sig := (LateOpeningRuntimeGame.model weight weightNonnegative).behavioralSignature)
    assessment.strategy bob choice
  let changed : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment :=
    { assessment with strategy := changedStrategy }
  have upper := incumbent_value_le_bestGuessValue weight weightNonnegative site representative
    decision current reward forfeit deposit forfeitNonnegative collateral changed
  have valueEq : (context weight weightNonnegative site reward forfeit deposit changed).value
      (changed.strategy bob) =
      (context weight weightNonnegative site reward forfeit deposit assessment).value choice := by
    simp only [context, changed, changedStrategy,
      InformationModel.BehavioralAssessment.truncatedContinuationContext,
      InformationModel.BehavioralAssessment.continuationContextWith, Context.value,
      GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner,
      Profile.update_same, Profile.update_idem]
  have bestEq : bestGuessValue weight weightNonnegative site reward forfeit deposit changed =
      bestGuessValue weight weightNonnegative site reward forfeit deposit assessment := by
    unfold bestGuessValue
    rw [answer_context_value weight weightNonnegative site representative decision current,
      answer_context_value weight weightNonnegative site representative decision current,
      answer_context_value weight weightNonnegative site representative decision current,
      answer_context_value weight weightNonnegative site representative decision current]
  rwa [valueEq, bestEq] at upper

open LateOpeningRuntimeBobBindingDecision LateOpeningRuntimeBobBindingInformation
  LateOpeningRuntimeBobBindingOptimization LateOpeningRuntimeEarlyBobSafeMenu in
/-- At an actual failed-publication binding fiber, sampled local rationality
implies local rationality for scaled full audit; this is not a global SE transfer. -/
theorem failed_binding_rationality_scaled
    (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationHistory
      bob site.1)
    (decision : LateOpeningRuntimeBobBindingInformation.DecisionHistory weight weightNonnegative)
    (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.truncatedContinuationContext site
        (fun history => LateOpeningRuntimeGame.payoff reward forfeit
          (sample probability nonnegative bounded) deposit history.state bob)
        (2 * LateOpeningRuntimeService.horizon + 1))) :
    assessment.IsSequentiallyRationalAt site
      (context weight weightNonnegative site reward forfeit
        (fun owner => probability * deposit owner) assessment) := by
  let scaled := fun owner => probability * deposit owner
  let auditContext := assessment.truncatedContinuationContext site
    (fun history => LateOpeningRuntimeGame.payoff reward forfeit
      (sample probability nonnegative bounded) deposit history.state bob)
    (2 * LateOpeningRuntimeService.horizon + 1)
  have integrable (choice) : auditContext.IntegrableAt choice :=
    payoffIntegrable_of_bounded _ _ fun history =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
        (sample probability nonnegative bounded) deposit history.state
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (integrable (assessment.strategy bob)) (fun choice _ => integrable choice)).mp rational
  have answerEq (bit : Bool) :
      auditContext.value (answerFinitePolicy weight weightNonnegative (bitGuess bit)) =
      (context weight weightNonnegative site reward forfeit scaled assessment).value
        (answerFinitePolicy weight weightNonnegative (bitGuess bit)) := by
    rw [failed_answer_context_value probability nonnegative bounded weight weightNonnegative
      site representative decision current reward forfeit deposit assessment,
      answer_context_value weight weightNonnegative site representative decision current]
  have lower : bestGuessValue weight weightNonnegative site reward forfeit scaled assessment ≤
      auditContext.value (assessment.strategy bob) := by
    apply max_le
    · rw [← answerEq false]
      exact comparison _ (Set.mem_univ _)
    · rw [← answerEq true]
      exact comparison _ (Set.mem_univ _)
  have dominated := context_value_le_scaled probability nonnegative bounded weight
    weightNonnegative reward forfeit deposit collateral assessment
    ((LateOpeningRuntimeGame.model weight weightNonnegative).truncatedRunner
      (2 * LateOpeningRuntimeService.horizon + 1)) site (assessment.strategy bob)
  apply (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight weightNonnegative site reward forfeit scaled assessment
      (assessment.strategy bob))
    (fun choice _ => context_integrable weight weightNonnegative site reward forfeit scaled
      assessment choice)).mpr
  intro choice _
  exact (failed_binding_full_value_le_bestGuessValue weight weightNonnegative site representative
    decision current reward forfeit scaled forfeitNonnegative (mul_nonneg nonnegative collateral)
      assessment choice).trans (lower.trans dominated)

theorem dirty_fresh_answer_payoff
    (probability : ℝ) (samplingNonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (weight : ℝ) (nonnegative : 0 ≤ weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ) (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (dirty : ¬ LateOpeningRuntimeBobBindingService.SilentRecall execution) (bit : Bool)
    (published : execution.application.config.store (.inr aliceEvent) =
      some (.success bit : PublicationResult Bool))
    (answer : Answer) (serial : Nat)
    (fresh : execution.application.candidates.lookup (bob, .prepared serial) = .fresh)
    (players : Player → app.Policy)
    (bobPolicy : players bob = LateOpeningRuntimeBobSafeContinuation.answerPolicy answer)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob
        (LateOpeningRuntimeBobFreshBinding.response serial answer))).support) :
    LateOpeningRuntimeGame.payoff reward forfeit (sample probability samplingNonnegative bounded)
      deposit (some ⟨0, none, final⟩) bob =
        LateOpeningRuntimeBobSuccessPayoff.answerScore
          (LateOpeningRuntimeBobSuccessPayoff.originalLabel execution) answer -
            probability * deposit bob := by
  have rawTrace := rawMenu.toRawTrace _ _ _ trace
  have answerPublished := LateOpeningRuntimeBobFreshContinuation.answer_fresh_continuation_publishes
    weight nonnegative answer players bobPolicy execution final rawTrace serial fresh ready timely
      reached
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 execution bob _ rawTrace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 14 _ final
      respondedTrace reached
  obtain ⟨bitInitial, labelInitial, finalValid⟩ :=
    LateOpeningRuntimeReadout.history_initial_invariant LateOpeningRuntimeService.runtime leaks
      LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
        ⟨0, none, final⟩ finalTrace
  have finalBound := LateOpeningRuntimeReadout.bob_success_from_binding
    final.application _
    finalValid.reachable answer answerPublished
  have aligned : (app.protocol ((setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph))) LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
          (some ⟨0, none, final⟩) := by
    have same : (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := nativeGraph)) = initial := by
      rw [PMF.map_comp]
      rfl
    rwa [same]
  have associated := LateOpeningRuntimeService.runtime.reactiveBindingInvariant_history leaks
    (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) aligned
  have clear := LateOpeningRuntimeBobAudit.no_binding_omission final.application
    associated answer finalBound
  rw [payoff_of_no_omission probability samplingNonnegative bounded reward forfeit deposit
    ⟨0, none, final⟩ bob clear]
  exact LateOpeningRuntimeBobDirtyPayoff.dirty_fresh_answer_payoff weight nonnegative reward forfeit
    (fun who => probability * deposit who) execution trace ready timely dirty bit published
      answer serial fresh players bobPolicy final reached

open LateOpeningRuntimeBobBindingService LateOpeningRuntimeBobDirtyPrefix
  LateOpeningRuntimeBobFreshBinding LateOpeningRuntimeBobBindingInformation
  LateOpeningRuntimeBobSuccessPayoff in
theorem sampled_dirty_information_answer_attainment
    (probability : ℝ) (samplingNonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (weight : ℝ) (nonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeGame.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
      bob site.1)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (dirty : ¬ SilentRecall execution) (bit : Bool)
    (published : execution.application.config.store (.inr aliceEvent) =
      some (.success bit : PublicationResult Bool))
    (current : representative.1.state = some ⟨14, some bob, execution⟩)
    (history : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory bob site.1)
    (reward forfeit : ℝ) (deposit : Player → ℝ) (answer : Answer) :
    ∃ (other : app.Execution) (serial : Nat),
      history.1.state = some ⟨14, some bob, other⟩ ∧
      LateOpeningRuntimeBobSafeContinuation.answerPolicy answer
        (other.recall bob) (other.observe app bob) = PMF.pure (response serial answer) ∧
      ∀ (players : Player → app.Policy),
        players bob = LateOpeningRuntimeBobSafeContinuation.answerPolicy answer →
        ∀ final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          players 14 (other.respond app bob (response serial answer))).support,
          LateOpeningRuntimeGame.payoff reward forfeit
            (sample probability samplingNonnegative bounded) deposit (some ⟨0, none, final⟩) bob =
              answerScore (originalLabel other) answer - probability * deposit bob := by
  obtain ⟨other, stateEq, sameRecall, sameView⟩ :=
    LateOpeningRuntimeBobBindingFiber.binding_history_same_information weight nonnegative
      site representative execution (rawMenu.toRawTrace _ _ _ trace) ready current history
  have otherTrace := stateEq ▸ history.1.trace
  have otherRawTrace := rawMenu.toRawTrace _ _ _ otherTrace
  have otherReady := ready_same_view _ _ sameView ready
  have otherTimely := timely_same_view _ _ sameView timely
  have otherPublished : other.application.config.store (.inr aliceEvent) =
      some (.success bit : PublicationResult Bool) := by
    rw [← alice_result_same_view _ _ sameView]
    exact published
  have otherDirty : ¬ SilentRecall other := by
    intro quiet
    apply dirty
    unfold SilentRecall at quiet ⊢
    rw [sameRecall]
    exact quiet
  have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) otherRawTrace
  change other.environmentRecall.length + 14 = 26 at counted
  have cursor : other.environmentRecall.length = 12 := by omega
  have clock : other.application.clock = 3 := by
    rw [clock_history weight nonnegative _ otherRawTrace, cursor]
    decide
  obtain ⟨serial, _, fresh, selected⟩ := answerPolicy_fresh_binding weight nonnegative
    ⟨14, some bob, other⟩ otherTrace rfl otherReady clock answer
  refine ⟨other, serial, stateEq, selected, ?_⟩
  intro players bobPolicy final reached
  exact dirty_fresh_answer_payoff probability samplingNonnegative bounded weight nonnegative
    reward forfeit deposit other otherTrace
    otherReady otherTimely otherDirty bit otherPublished answer serial fresh players bobPolicy
      final reached

section
open LateOpeningRuntimeBobDirtyContext LateOpeningRuntimeBobBindingService
  LateOpeningRuntimeBobSuccessPayoff LateOpeningRuntimeBobBindingDecision
  LateOpeningRuntimeEarlyBobSafeMenu
variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeGame.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
    bob site.1)
  (execution : app.Execution)
  (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨14, some bob, execution⟩))
  (ready : execution.application.config.cut.Ready bobBindEvent)
  (current : representative.1.state = some ⟨14, some bob, execution⟩)

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

theorem dirty_answer_context_value
    (probability : ℝ) (samplingNonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (dirty : ¬ SilentRecall execution) (bit : Bool)
    (published : execution.application.config.store (.inr aliceEvent) =
      some (.success bit : PublicationResult Bool))
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) :
    (assessment.truncatedContinuationContext site
      (fun history => LateOpeningRuntimeGame.payoff reward forfeit
        (sample probability samplingNonnegative bounded) deposit history.state bob)
      (2 * LateOpeningRuntimeService.horizon + 1)).value
      (answerFinitePolicy weight nonnegative answer) =
    expect (assessment.belief bob site) fun history =>
      answerScore (originalLabel (executionOfInformation weight nonnegative site representative
        execution trace ready current history)) answer - probability * deposit bob := by
  have mapped := expect_map History.state
    ((LateOpeningRuntimeBobBindingDecision.context weight nonnegative site
      reward forfeit deposit assessment).outcome
      (answerFinitePolicy weight nonnegative answer))
    (fun state => LateOpeningRuntimeGame.payoff reward forfeit
      (sample probability samplingNonnegative bounded)
      deposit state bob)
  rw [answer_context_outcome_law weight nonnegative site representative execution trace ready
    current, expect_map] at mapped
  have nativeValue : (assessment.truncatedContinuationContext site
      (fun history => LateOpeningRuntimeGame.payoff reward forfeit
        (sample probability samplingNonnegative bounded) deposit history.state bob)
      (2 * LateOpeningRuntimeService.horizon + 1)).value
      (answerFinitePolicy weight nonnegative answer) =
      expect (LateOpeningRuntimeBobDirtyContext.answerFinalLaw weight nonnegative site
        representative execution trace ready current
        assessment answer) (fun final => LateOpeningRuntimeGame.payoff reward forfeit
          (sample probability samplingNonnegative bounded) deposit
            (app.finished final) bob) := mapped.symm
  rw [nativeValue]
  unfold LateOpeningRuntimeBobDirtyContext.answerFinalLaw
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ fun final =>
    LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
      (sample probability samplingNonnegative bounded)
      deposit (app.finished final))]
  apply expect_congr_on_support
  intro history _
  obtain ⟨other, serial, stateEq, selected, attained⟩ := sampled_dirty_information_answer_attainment
    probability samplingNonnegative bounded weight nonnegative site representative execution trace
      ready timely dirty bit published current
      history reward forfeit deposit answer
  have valid := executionOfInformation_spec weight nonnegative site representative execution
    trace ready current history
  have otherEq : other = executionOfInformation weight nonnegative site representative execution
      trace ready current history := by
    have equal := Option.some.inj (stateEq.symm.trans valid.1)
    exact congrArg ReactiveApplication.Control.execution equal
  subst other
  dsimp only
  rw [selected, PMF.pure_bind]
  calc
    _ = expect _ (fun _ => answerScore (originalLabel
        (executionOfInformation weight nonnegative site representative execution trace ready
          current history)) answer - probability * deposit bob) := by
      apply expect_congr_on_support
      intro final reached
      exact attained (answerPlayers weight nonnegative assessment answer)
        (by simp only [answerPlayers, Function.update_self]) final reached
    _ = _ := expect_constant _ _

include representative execution trace ready current in
theorem dirty_full_value_le_bestAnswerValue
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (dirty : ¬ SilentRecall execution) (bit : Bool)
    (published : execution.application.config.store (.inr aliceEvent) =
      some (.success bit : PublicationResult Bool))
    (forfeitNonnegative : 0 ≤ forfeit)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (choice : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralPolicy bob) :
    (context weight nonnegative site reward forfeit deposit assessment).value choice ≤
      LateOpeningRuntimeBobDirtyOptimization.bestAnswerValue weight nonnegative site
        reward forfeit deposit assessment := by
  let changedStrategy := Profile.update
    (sig := (LateOpeningRuntimeGame.model weight nonnegative).behavioralSignature)
    assessment.strategy bob choice
  let changed : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment :=
    { assessment with strategy := changedStrategy }
  have upper := LateOpeningRuntimeBobDirtyOptimization.incumbent_value_le_bestAnswerValue
    weight nonnegative site representative execution trace ready current reward forfeit deposit
      timely dirty bit published forfeitNonnegative changed
  have valueEq : (context weight nonnegative site reward forfeit deposit changed).value
      (changed.strategy bob) =
      (context weight nonnegative site reward forfeit deposit assessment).value choice := by
    simp only [context, changed, changedStrategy,
      InformationModel.BehavioralAssessment.truncatedContinuationContext,
      InformationModel.BehavioralAssessment.continuationContextWith, Context.value,
      GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner,
      Profile.update_same, Profile.update_idem]
  have answerEq (answer : Answer) :
      (context weight nonnegative site reward forfeit deposit changed).value
        (answerFinitePolicy weight nonnegative answer) =
      (context weight nonnegative site reward forfeit deposit assessment).value
        (answerFinitePolicy weight nonnegative answer) := by
    rw [LateOpeningRuntimeBobDirtyContext.answer_context_value weight nonnegative site
      representative execution trace ready current reward forfeit deposit timely dirty bit
        published changed,
      LateOpeningRuntimeBobDirtyContext.answer_context_value weight nonnegative site
        representative execution trace ready current reward forfeit deposit timely dirty bit
          published assessment]
  have bestEq : LateOpeningRuntimeBobDirtyOptimization.bestAnswerValue weight nonnegative site
      reward forfeit deposit changed =
      LateOpeningRuntimeBobDirtyOptimization.bestAnswerValue weight nonnegative site
        reward forfeit deposit assessment := by
    unfold LateOpeningRuntimeBobDirtyOptimization.bestAnswerValue
    rw [answerEq, answerEq, answerEq, answerEq]
  rw [valueEq, bestEq] at upper
  exact upper

include representative execution trace ready current in
theorem dirty_binding_rationality_scaled
    (probability : ℝ) (samplingNonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (dirty : ¬ SilentRecall execution) (bit : Bool)
    (published : execution.application.config.store (.inr aliceEvent) =
      some (.success bit : PublicationResult Bool))
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.truncatedContinuationContext site
        (fun history => LateOpeningRuntimeGame.payoff reward forfeit
          (sample probability samplingNonnegative bounded) deposit history.state bob)
        (2 * LateOpeningRuntimeService.horizon + 1))) :
    assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit
        (fun owner => probability * deposit owner) assessment) := by
  let scaled := fun owner => probability * deposit owner
  let auditContext := assessment.truncatedContinuationContext site
    (fun history => LateOpeningRuntimeGame.payoff reward forfeit
      (sample probability samplingNonnegative bounded) deposit history.state bob)
    (2 * LateOpeningRuntimeService.horizon + 1)
  have integrable (choice) : auditContext.IntegrableAt choice :=
    payoffIntegrable_of_bounded _ _ fun history =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
        (sample probability samplingNonnegative bounded) deposit history.state
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (integrable (assessment.strategy bob)) (fun choice _ => integrable choice)).mp rational
  have answerEq (answer : Answer) :
      auditContext.value (answerFinitePolicy weight nonnegative answer) =
      (context weight nonnegative site reward forfeit scaled assessment).value
        (answerFinitePolicy weight nonnegative answer) := by
    rw [dirty_answer_context_value weight nonnegative site representative execution trace ready
      current reward forfeit deposit probability samplingNonnegative bounded timely dirty bit
        published assessment,
      LateOpeningRuntimeBobDirtyContext.answer_context_value weight nonnegative site
        representative execution trace ready current reward forfeit scaled timely dirty bit
          published assessment]
  have lower : LateOpeningRuntimeBobDirtyOptimization.bestAnswerValue weight nonnegative site
      reward forfeit scaled assessment ≤ auditContext.value (assessment.strategy bob) := by
    unfold LateOpeningRuntimeBobDirtyOptimization.bestAnswerValue
    apply max_le
    · rw [← answerEq]
      exact comparison _ (Set.mem_univ _)
    · apply max_le
      · rw [← answerEq]
        exact comparison _ (Set.mem_univ _)
      · apply max_le
        · rw [← answerEq]
          exact comparison _ (Set.mem_univ _)
        · rw [← answerEq]
          exact comparison _ (Set.mem_univ _)
  have dominated := context_value_le_scaled probability samplingNonnegative bounded weight
    nonnegative reward forfeit deposit collateral assessment
    ((LateOpeningRuntimeGame.model weight nonnegative).truncatedRunner
      (2 * LateOpeningRuntimeService.horizon + 1)) site (assessment.strategy bob)
  apply (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight nonnegative site reward forfeit scaled assessment
      (assessment.strategy bob))
    (fun choice _ => context_integrable weight nonnegative site reward forfeit scaled
      assessment choice)).mpr
  intro choice _
  exact (dirty_full_value_le_bestAnswerValue weight nonnegative site representative execution
    trace ready current reward forfeit scaled timely dirty bit published forfeitNonnegative
      assessment choice).trans (lower.trans dominated)

end

end Vegas.Examples.LateOpeningRuntimeAllOrNoneBinding
