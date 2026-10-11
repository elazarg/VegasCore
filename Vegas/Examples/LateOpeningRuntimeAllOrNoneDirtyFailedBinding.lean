/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobDirtyScore
import Vegas.Examples.LateOpeningRuntimeBobDirtyContext
import Vegas.Examples.LateOpeningRuntimeBobRawPayoff
import Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit
import Vegas.Examples.LateOpeningRuntimeAllOrNoneBinding
import Vegas.Examples.LateOpeningRuntimeBobRationality

/-! # Receiver continuation comparisons after failed Alice publication and sunk charge -/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeAllOrNoneDirtyFailedBinding
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Enforcement GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeUtility LateOpeningRuntimeBobBindingService LateOpeningRuntimeBobDirtyPrefix
  LateOpeningRuntimeBobBindingTransport LateOpeningRuntimeBobBindingOmission
  LateOpeningRuntimeBobAnswerPayoff LateOpeningRuntimeBobRawPayoff
variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem failed_continuation_readout
    (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (failed : execution.application.config.store (.inr aliceEvent) =
      some (.failure : PublicationResult Bool))
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob response)).support) :
    ∃ bit label binding publication,
      originalBit execution = bit ∧
      EventGraph.Config.Reachable (graph := nativeGraph)
        (setup.eventInputs (sourceInitial bit label)) final.application.config ∧
      final.application.config.store (.inr bobBindEvent) = some binding ∧
      final.application.config.store (.inr bobRevealEvent) = some publication ∧
      serviceSourceReadout setup .sequential deadline leaks (app.finished final) =
        some (terminalStateOf bit label .failure binding publication) := by
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨14, some bob, execution⟩ trace
  have invariant := LateOpeningRuntimeService.runtime.reactiveStateInvariant leaks
    (setup.eventInputs (sourceInitial bit label))
  have after := (ReactiveApplication.Invariant.policyInvariant app invariant players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (invariant.respond execution bob response valid) reached
  have failedInvariant := LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks
    (.inr aliceEvent) (.failure : PublicationResult Bool)
  have aliceAfter := (ReactiveApplication.Invariant.policyInvariant app failedInvariant
    players).runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (failedInvariant.respond execution bob response failed) reached
  obtain ⟨responded⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 execution bob response
      trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 14 _ final responded reached
  have complete := (contract weight nonnegative).completes ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
  obtain ⟨binding, bound⟩ := Option.isSome_iff_exists.mp
    (final.application.config.store_available_of_terminal complete (.inr bobBindEvent))
  obtain ⟨publication, published⟩ := Option.isSome_iff_exists.mp
    (final.application.config.store_available_of_terminal complete (.inr bobRevealEvent))
  refine ⟨bit, label, binding, publication,
    originalBit_initialized execution bit label valid, after.reachable, bound,
      published, ?_⟩
  change (if final.application.config.cut.Terminal then
    decodeState? (terminalRefs program) final.application.config.store else none) = _
  rw [ite_eq_left complete]
  exact decode_terminalStateOf final.application bit label .failure binding publication
    after.reachable.inputs_eq aliceAfter bound published

theorem dirty_failed_continuation_payoff_le_score (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (dirty : ¬ SilentRecall execution)
    (failed : execution.application.config.store (.inr aliceEvent) =
      some (.failure : PublicationResult Bool))
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob response)).support)
    (reward forfeit : ℝ) (forfeitNonnegative : 0 ≤ forfeit) (deposit : Player → ℝ) :
    LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit (some ⟨0, none, final⟩) bob ≤
        bindingScore (originalBit execution)
          ((servicedBinding execution response).application.config.store (.inr bobBindEvent)) -
            deposit bob := by
  have rawTrace := rawMenu.toRawTrace _ _ _ trace
  obtain ⟨bit, label, binding, publication, bitEq, finalReachable,
    bound, published, readout⟩ := failed_continuation_readout weight nonnegative execution
      rawTrace failed response players final reached
  have splitReach := reached
  change final ∈ ((app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
    (execution.respond app bob response)).bind
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 13)).support
    at splitReach
  rw [servicedBinding_round weight nonnegative execution trace response players,
    PMF.pure_bind] at splitReach
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 execution bob response rawTrace
  obtain ⟨servicedTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 13 _
    (servicedBinding execution response) respondedTrace
    (by rw [servicedBinding_round weight nonnegative execution trace response players]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  change serviceSourceReadout setup .sequential deadline leaks (some ⟨0, none, final⟩) =
    some (terminalStateOf bit label .failure binding publication) at readout
  rw [dirty_binding_payoff_eq_base_sub_deposit weight nonnegative reward forfeit deposit
    execution trace ready dirty response players final reached,
    nativeBaseUtility_of_readout reward forfeit _ _ readout bob]
  apply sub_le_sub_right
  rw [bitEq]
  cases publication with
  | failure =>
      rw [sourceUtility_bob_failure]
      exact (neg_nonpos.mpr forfeitNonnegative).trans (bindingScore_nonnegative bit _)
  | success answer =>
      have finalBinding := bob_success_from_binding final.application _ finalReachable answer
        published
      have selected : (servicedBinding execution response).application.config.store
          (.inr bobBindEvent) = some (.success answer) := by
        cases immediate : (servicedBinding execution response).application.config.store
            (.inr bobBindEvent) with
        | none =>
            have failed := omitted_binding_expires weight nonnegative players _ final
              servicedTrace immediate splitReach
            rw [finalBinding] at failed
            cases failed
        | some result =>
            have retained := (ReactiveApplication.Invariant.policyInvariant app
              (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks
                (.inr bobBindEvent) result) players).runRounds
                  (LateOpeningRuntimeService.scheduler weight nonnegative) 13 _ final immediate
                    splitReach
            exact congrArg some (Option.some.inj (retained.symm.trans finalBinding))
      rw [selected]
      change _ ≤ if answer.val = (if bit then 5 else 4) then 1 else 0
      exact le_of_eq (sourceUtility_bob_after_alice_failure reward forfeit bit label
        binding answer)

theorem dirty_failed_fresh_answer_payoff (weight : ℝ) (nonnegative : 0 ≤ weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ) (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (dirty : ¬ SilentRecall execution)
    (failed : execution.application.config.store (.inr aliceEvent) =
      some (.failure : PublicationResult Bool))
    (answer : Answer) (serial : Nat)
    (fresh : execution.application.candidates.lookup (bob, .prepared serial) = .fresh)
    (players : Player → app.Policy)
    (bobPolicy : players bob = LateOpeningRuntimeBobSafeContinuation.answerPolicy answer)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob
        (LateOpeningRuntimeBobFreshBinding.response serial answer))).support) :
    LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit (some ⟨0, none, final⟩) bob =
        (if answer.val = (if originalBit execution then 5 else 4) then 1 else 0) - deposit bob := by
  have rawTrace := rawMenu.toRawTrace _ _ _ trace
  have answerPublished := LateOpeningRuntimeBobFreshContinuation.answer_fresh_continuation_publishes
    weight nonnegative answer players bobPolicy execution final rawTrace serial fresh ready timely
      reached
  obtain ⟨originalBit, label, valid⟩ :=
    LateOpeningRuntimeReadout.history_initial_invariant LateOpeningRuntimeService.runtime leaks
      LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
        ⟨14, some bob, execution⟩ rawTrace
  have invariant := LateOpeningRuntimeService.runtime.reactiveStateInvariant leaks
    (setup.eventInputs (sourceInitial originalBit label))
  have after := (ReactiveApplication.Invariant.policyInvariant app invariant players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
    (invariant.respond execution bob _ valid) reached
  have publicationInvariant := LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks
    (.inr aliceEvent) (.failure : PublicationResult Bool)
  have aliceAfter := (ReactiveApplication.Invariant.policyInvariant app publicationInvariant
    players).runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (publicationInvariant.respond execution bob _ failed) reached
  have answerBound := LateOpeningRuntimeReadout.bob_success_from_binding final.application _
    after.reachable answer answerPublished
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 execution bob _ rawTrace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 14 _ final
      respondedTrace reached
  have complete := (contract weight nonnegative).completes ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
  have decoded : serviceSourceReadout setup .sequential deadline leaks
      (some ⟨0, none, final⟩) = some (LateOpeningRuntimeReadout.terminalStateOf
        originalBit label .failure (.success answer) (.success answer)) := by
    change (if final.application.config.cut.Terminal then
      decodeState? (terminalRefs program) final.application.config.store else none) = _
    rw [ite_eq_left complete]
    exact LateOpeningRuntimeReadout.decode_terminalStateOf final.application originalBit label
      .failure (.success answer) (.success answer) after.reachable.inputs_eq aliceAfter
        answerBound answerPublished
  rw [dirty_binding_payoff_eq_base_sub_deposit weight nonnegative reward forfeit deposit
    execution trace ready dirty _ players final reached,
    LateOpeningRuntimeUtility.nativeBaseUtility_of_readout reward forfeit _ _ decoded bob,
    LateOpeningRuntimeUtility.sourceUtility_bob_after_alice_failure]
  rw [LateOpeningRuntimeBobAnswerPayoff.originalBit_initialized execution originalBit label
    valid]
theorem dirty_failed_fresh_answer_sampled_payoff
    (probability : ℝ) (probabilityNonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (reward forfeit : ℝ) (deposit : Player → ℝ) (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (dirty : ¬ SilentRecall execution)
    (failed : execution.application.config.store (.inr aliceEvent) =
      some (.failure : PublicationResult Bool))
    (answer : Answer) (serial : Nat)
    (fresh : execution.application.candidates.lookup (bob, .prepared serial) = .fresh)
    (players : Player → app.Policy)
    (bobPolicy : players bob = LateOpeningRuntimeBobSafeContinuation.answerPolicy answer)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob
        (LateOpeningRuntimeBobFreshBinding.response serial answer))).support) :
    LateOpeningRuntimeGame.payoff reward forfeit
        (LateOpeningRuntimeAllOrNoneTrafficAudit.sample probability probabilityNonnegative bounded)
        deposit (some ⟨0, none, final⟩) bob =
      (if answer.val = (if originalBit execution then 5 else 4) then 1 else 0) -
        probability * deposit bob := by
  have rawTrace := rawMenu.toRawTrace _ _ _ trace
  have published := LateOpeningRuntimeBobFreshContinuation.answer_fresh_continuation_publishes
    weight nonnegative answer players bobPolicy execution final rawTrace serial fresh ready timely
      reached
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨14, some bob, execution⟩ rawTrace
  have stateInvariant := LateOpeningRuntimeService.runtime.reactiveStateInvariant leaks
    (setup.eventInputs (sourceInitial bit label))
  have finalValid :=
    (ReactiveApplication.Invariant.policyInvariant app stateInvariant players).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (stateInvariant.respond execution bob _ valid) reached
  have bound := bob_success_from_binding final.application _ finalValid.reachable answer published
  have bindingStart := LateOpeningRuntimeService.runtime.reactiveBindingInvariant_history leaks
    (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (by
      have same : (setup.initialLaw.map setup.eventInputs).map
          (EventGraphRuntime.State.initial (graph := nativeGraph)) = initial := by
        rw [PMF.map_comp]
        rfl
      rw [same]
      exact rawTrace)
  have bindingInvariant := LateOpeningRuntimeService.runtime.reactiveBindingInvariant leaks
  have bindingFinal :=
    (ReactiveApplication.Invariant.policyInvariant app bindingInvariant players).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (bindingInvariant.respond execution bob _ bindingStart) reached
  have clear := LateOpeningRuntimeBobAudit.no_binding_omission final.application bindingFinal
    answer bound
  rw [LateOpeningRuntimeAllOrNoneTrafficAudit.payoff_of_no_omission probability
    probabilityNonnegative bounded reward forfeit deposit ⟨0, none, final⟩ bob clear]
  exact dirty_failed_fresh_answer_payoff weight nonnegative reward forfeit
    (fun owner => probability * deposit owner) execution trace ready timely dirty failed answer
      serial fresh players bobPolicy final reached

section BindingFiber
open LateOpeningRuntimeBobDirtyContext
open LateOpeningRuntimeBobBindingDecision (answerPlayers context)
variable
  (site : (LateOpeningRuntimeGame.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
    bob site.1)
  (execution : app.Execution)
  (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨14, some bob, execution⟩))
  (ready : execution.application.config.cut.Ready bobBindEvent)
  (current : representative.1.state = some ⟨14, some bob, execution⟩)
  (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
  (dirty : ¬ SilentRecall execution)
  (failed : execution.application.config.store (.inr aliceEvent) =
    some (.failure : PublicationResult Bool))
  (reward forfeit : ℝ) (deposit : Player → ℝ)

include representative trace ready current timely dirty failed in
theorem sampled_answer_context_value
    (probability : ℝ) (probabilityNonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) :
    (LateOpeningRuntimeBobRationality.context weight nonnegative site reward forfeit
      (LateOpeningRuntimeAllOrNoneTrafficAudit.sample probability probabilityNonnegative bounded)
      deposit assessment).value
        (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative answer) =
      expect (assessment.belief bob site) (fun history =>
        (if answer.val = (if originalBit (executionOfInformation weight nonnegative site
          representative execution trace ready current history) then 5 else 4) then 1 else 0) -
            probability * deposit bob) := by
  have outcome :
      ((LateOpeningRuntimeBobRationality.context weight nonnegative site reward forfeit
        (LateOpeningRuntimeAllOrNoneTrafficAudit.sample probability probabilityNonnegative bounded)
        deposit assessment).outcome
          (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative answer)).map
            History.state =
      (answerFinalLaw weight nonnegative site representative execution trace ready current
        assessment answer).map app.finished :=
    answer_context_outcome_law weight nonnegative site representative execution trace ready current
      reward forfeit deposit assessment answer
  have mapped := expect_map History.state
    ((LateOpeningRuntimeBobRationality.context weight nonnegative site reward forfeit
      (LateOpeningRuntimeAllOrNoneTrafficAudit.sample probability probabilityNonnegative bounded)
      deposit assessment).outcome
        (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative answer))
    (fun state => LateOpeningRuntimeGame.payoff reward forfeit
      (LateOpeningRuntimeAllOrNoneTrafficAudit.sample probability probabilityNonnegative bounded)
      deposit state bob)
  rw [outcome, expect_map] at mapped
  have nativeValue :
      (LateOpeningRuntimeBobRationality.context weight nonnegative site reward forfeit
        (LateOpeningRuntimeAllOrNoneTrafficAudit.sample probability probabilityNonnegative bounded)
        deposit assessment).value
          (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative answer) =
      expect (answerFinalLaw weight nonnegative site representative execution trace ready current
        assessment answer) (fun final => LateOpeningRuntimeGame.payoff reward forfeit
          (LateOpeningRuntimeAllOrNoneTrafficAudit.sample probability
            probabilityNonnegative bounded)
          deposit (app.finished final) bob) := mapped.symm
  rw [nativeValue]
  unfold answerFinalLaw
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ fun final =>
    LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
      (LateOpeningRuntimeAllOrNoneTrafficAudit.sample probability probabilityNonnegative bounded)
      deposit (app.finished final))]
  apply expect_congr_on_support
  intro history _
  let other := executionOfInformation weight nonnegative site representative execution trace ready
    current history
  have valid := executionOfInformation_spec weight nonnegative site representative execution
    trace ready current history
  have otherTrace := valid.1 ▸ history.1.trace
  have rawTrace := rawMenu.toRawTrace _ _ _ otherTrace
  have otherReady := LateOpeningRuntimeBobBindingInformation.ready_same_view _ _ valid.2.2 ready
  have otherTimely := LateOpeningRuntimeBobBindingInformation.timely_same_view _ _ valid.2.2 timely
  have otherFailed : other.application.config.store (.inr aliceEvent) =
      some (.failure : PublicationResult Bool) := by
    rw [← LateOpeningRuntimeBobBindingInformation.alice_result_same_view _ _ valid.2.2]
    exact failed
  have otherDirty : ¬ SilentRecall other := by
    intro quiet
    apply dirty
    unfold SilentRecall at quiet ⊢
    rw [valid.2.1]
    exact quiet
  have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) rawTrace
  change other.environmentRecall.length + 14 = 26 at accounted
  have clock : other.application.clock = 3 := by
    rw [clock_history weight nonnegative _ rawTrace]
    have cursor : other.environmentRecall.length = 12 := by omega
    rw [cursor]
    decide
  obtain ⟨serial, _, fresh, selected⟩ :=
    LateOpeningRuntimeBobFreshBinding.answerPolicy_fresh_binding weight nonnegative
      ⟨14, some bob, other⟩ otherTrace rfl otherReady clock answer
  dsimp only
  rw [selected, PMF.pure_bind]
  calc
    _ = expect _ (fun _ =>
        (if answer.val = (if originalBit other then 5 else 4) then 1 else 0) -
          probability * deposit bob) := by
      apply expect_congr_on_support
      intro final reached
      exact dirty_failed_fresh_answer_sampled_payoff weight nonnegative probability
        probabilityNonnegative bounded reward forfeit deposit other otherTrace otherReady
        otherTimely otherDirty otherFailed answer serial fresh
        (answerPlayers weight nonnegative assessment answer)
        (by simp only [answerPlayers, Function.update_self]) final reached
    _ = _ := expect_constant _ _

include representative trace ready current timely dirty failed in
theorem full_answer_context_value
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative answer) =
      expect (assessment.belief bob site) (fun history =>
        (if answer.val = (if originalBit (executionOfInformation weight nonnegative site
          representative execution trace ready current history) then 5 else 4) then 1 else 0) -
            deposit bob) := by
  have value := sampled_answer_context_value weight nonnegative site representative execution
    trace ready current timely dirty failed reward forfeit deposit 1 (by norm_num) (by norm_num)
      assessment answer
  have sampler : LateOpeningRuntimeAllOrNoneTrafficAudit.sample 1 (by norm_num) (by norm_num) =
      (fun actual => PMF.pure actual) := by
    funext actual
    exact mix_one _ _
  simpa only [sampler, one_mul, LateOpeningRuntimeBobBindingDecision.context,
    LateOpeningRuntimeBobRationality.context] using value

private theorem failedScore_abs_le_one (bit : Bool)
    (result : Option (PublicationResult Answer)) : |bindingScore bit result| ≤ 1 := by
  cases result with
  | none => simp [bindingScore]
  | some result =>
    cases result with
    | failure => simp [bindingScore]
    | success answer =>
      simp only [bindingScore]
      split_ifs <;> norm_num

include representative trace ready current dirty failed in
theorem responseValue_le_scoreValue
    (forfeitNonnegative : 0 ≤ forfeit)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) :
    responseValue weight nonnegative site representative execution trace ready current reward
      forfeit deposit assessment response ≤
        expect (assessment.belief bob site) (fun history =>
          bindingScore (originalBit (executionOfInformation weight nonnegative site representative
            execution trace ready current history))
              ((servicedBinding execution response).application.config.store (.inr bobBindEvent)) -
                deposit bob) := by
  apply expect_mono _
    (payoffIntegrable_of_bounded _ _ fun history => by
      apply expect_abs_le_of_bounded (show 0 ≤ 1 + |forfeit| + |deposit bob| by positivity)
      intro final
      exact LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final))
    (payoffIntegrable_of_bounded _ _ fun history => by
      have scoreBound := failedScore_abs_le_one (originalBit
        (executionOfInformation weight nonnegative site representative execution trace ready
          current history))
        ((servicedBinding execution response).application.config.store (.inr bobBindEvent))
      have difference := abs_sub (bindingScore (originalBit
        (executionOfInformation weight nonnegative site representative execution trace ready
          current history))
        ((servicedBinding execution response).application.config.store (.inr bobBindEvent)))
        (deposit bob)
      exact difference.trans (add_le_add scoreBound (le_refl |deposit bob|)))
  intro history _
  let recovered := executionOfInformation weight nonnegative site representative execution trace
    ready current history
  have compatible := executionOfInformation_spec weight nonnegative site representative execution
    trace ready current history
  have recoveredTrace := compatible.1 ▸ history.1.trace
  have recoveredReady :=
    LateOpeningRuntimeBobBindingInformation.ready_same_view _ _ compatible.2.2 ready
  have recoveredDirty : ¬ SilentRecall recovered := by
    intro quiet
    apply dirty
    unfold SilentRecall at quiet ⊢
    rw [compatible.2.1]
    exact quiet
  have recoveredFailed : recovered.application.config.store (.inr aliceEvent) =
      some (.failure : PublicationResult Bool) := by
    rw [← LateOpeningRuntimeBobBindingInformation.alice_result_same_view _ _ compatible.2.2]
    exact failed
  apply expect_le_const _ _
    (payoffIntegrable_of_bounded _ _ fun final =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final))
  intro final reached
  have upper := dirty_failed_continuation_payoff_le_score weight
    nonnegative recovered recoveredTrace recoveredReady recoveredDirty recoveredFailed
      response _ final reached reward forfeit forfeitNonnegative deposit
  have same := serviced_binding_same_information weight nonnegative execution recovered
    trace recoveredTrace compatible.2.1 compatible.2.2 response
  rwa [← same] at upper

def bestGuessValue
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment) : ℝ :=
  max ((context weight nonnegative site reward forfeit deposit assessment).value
      (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative
        (LateOpeningRuntimeBobBindingDecision.bitGuess false)))
    ((context weight nonnegative site reward forfeit deposit assessment).value
      (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative
        (LateOpeningRuntimeBobBindingDecision.bitGuess true)))

include representative trace ready current timely dirty failed in
theorem bestGuessValue_ge_sunk
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment) :
    -deposit bob ≤ bestGuessValue weight nonnegative site reward forfeit deposit assessment := by
  unfold bestGuessValue
  apply le_trans _ (le_max_left _ _)
  rw [full_answer_context_value weight nonnegative site representative execution trace ready current
    timely dirty failed reward forfeit deposit assessment]
  rw [← expect_constant (assessment.belief bob site) (-deposit bob)]
  apply expect_mono (fun history _ => by split_ifs <;> linarith)
    (payoffIntegrable_constant _ _)
    (payoffIntegrable_of_bounded _ _ (C := 1 + |deposit bob|) fun history => by
      have bound := abs_sub (1 : ℝ) (deposit bob)
      norm_num only [abs_one] at bound
      split_ifs <;> norm_num only [zero_sub, abs_neg] <;>
        linarith [abs_nonneg (deposit bob)])

include representative trace ready current timely dirty failed in
theorem answer_value_le_bestGuessValue
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative answer) ≤
        bestGuessValue weight nonnegative site reward forfeit deposit assessment := by
  by_cases left : answer.val = 4
  · have same : answer = LateOpeningRuntimeBobBindingDecision.bitGuess false := Subtype.ext left
    rw [same]
    exact le_max_left _ _
  by_cases right : answer.val = 5
  · have same : answer = LateOpeningRuntimeBobBindingDecision.bitGuess true := Subtype.ext right
    rw [same]
    exact le_max_right _ _
  have value : (context weight nonnegative site reward forfeit deposit assessment).value
      (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative answer) =
        -deposit bob := by
    rw [full_answer_context_value weight nonnegative site representative execution trace ready
      current timely dirty failed reward forfeit deposit assessment]
    calc
      _ = expect (assessment.belief bob site) (fun _ => -deposit bob) := by
        apply expect_congr_on_support
        intro history _
        cases originalBit (executionOfInformation weight nonnegative site representative execution
          trace ready current history) <;>
            simp only [Bool.false_eq_true, ↓reduceIte, left, right, zero_sub]
      _ = _ := expect_constant _ _
  rw [value]
  exact bestGuessValue_ge_sunk weight nonnegative site representative execution trace ready current
    timely dirty failed reward forfeit deposit assessment

include representative trace ready current timely dirty failed in
theorem response_score_value_le_bestGuessValue
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) :
    expect (assessment.belief bob site) (fun history =>
      bindingScore (originalBit (executionOfInformation weight nonnegative site representative
        execution trace ready current history))
        ((servicedBinding execution response).application.config.store (.inr bobBindEvent)) -
          deposit bob) ≤
            bestGuessValue weight nonnegative site reward forfeit deposit assessment := by
  cases selected : (servicedBinding execution response).application.config.store
      (.inr bobBindEvent) with
  | none =>
    simp only [bindingScore, expect_constant, zero_sub]
    exact bestGuessValue_ge_sunk weight nonnegative site representative execution trace ready
      current timely dirty failed reward forfeit deposit assessment
  | some result =>
    cases result with
    | failure =>
      simp only [bindingScore, expect_constant, zero_sub]
      exact bestGuessValue_ge_sunk weight nonnegative site representative execution trace ready
        current timely dirty failed reward forfeit deposit assessment
    | success answer =>
      change expect (assessment.belief bob site) (fun history =>
        (if answer.val = (if originalBit (executionOfInformation weight nonnegative site
          representative execution trace ready current history) then 5 else 4) then 1 else 0) -
          deposit bob) ≤ _
      rw [← full_answer_context_value weight nonnegative site representative execution trace ready
        current timely dirty failed reward forfeit deposit assessment answer]
      exact answer_value_le_bestGuessValue weight nonnegative site representative execution trace
        ready current timely dirty failed reward forfeit deposit assessment answer

include representative trace ready current timely dirty failed in
theorem incumbent_value_le_bestGuessValue (forfeitNonnegative : 0 ≤ forfeit)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) ≤
        bestGuessValue weight nonnegative site reward forfeit deposit assessment := by
  rw [incumbent_value_eq_response_average weight nonnegative site representative execution trace
    ready current reward forfeit deposit assessment]
  apply expect_le_const _ _
    (payoffIntegrable_of_bounded _ _ fun response =>
      LateOpeningRuntimeBobDirtyOptimization.responseValue_bounded weight nonnegative site
        representative execution trace ready current reward forfeit deposit assessment response)
  intro response _
  exact (responseValue_le_scoreValue weight nonnegative site representative execution trace ready
    current dirty failed reward forfeit deposit forfeitNonnegative assessment response).trans
    (response_score_value_le_bestGuessValue weight nonnegative site representative execution trace
      ready current timely dirty failed reward forfeit deposit assessment response)

include representative trace ready current timely dirty failed in
theorem full_value_le_bestGuessValue (forfeitNonnegative : 0 ≤ forfeit)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralPolicy bob) :
    (context weight nonnegative site reward forfeit deposit assessment).value alternative ≤
      bestGuessValue weight nonnegative site reward forfeit deposit assessment := by
  let changedStrategy := Profile.update
    (sig := (LateOpeningRuntimeGame.model weight nonnegative).behavioralSignature)
    assessment.strategy bob alternative
  let changed : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment :=
    { assessment with strategy := changedStrategy }
  have upper := incumbent_value_le_bestGuessValue weight nonnegative site representative execution
    trace ready current timely dirty failed reward forfeit deposit forfeitNonnegative changed
  have valueEq : (context weight nonnegative site reward forfeit deposit changed).value
      (changed.strategy bob) =
      (context weight nonnegative site reward forfeit deposit assessment).value alternative := by
    simp only [context, changed, changedStrategy,
      InformationModel.BehavioralAssessment.truncatedContinuationContext,
      InformationModel.BehavioralAssessment.continuationContextWith, Context.value,
      GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner,
      Profile.update_same, Profile.update_idem]
  have bestEq : bestGuessValue weight nonnegative site reward forfeit deposit changed =
      bestGuessValue weight nonnegative site reward forfeit deposit assessment := by
    unfold bestGuessValue
    rw [full_answer_context_value weight nonnegative site representative execution trace ready
      current timely dirty failed reward forfeit deposit changed,
      full_answer_context_value weight nonnegative site representative execution trace ready
        current timely dirty failed reward forfeit deposit changed,
      full_answer_context_value weight nonnegative site representative execution trace ready
        current timely dirty failed reward forfeit deposit assessment,
      full_answer_context_value weight nonnegative site representative execution trace ready
        current timely dirty failed reward forfeit deposit assessment]
  rwa [valueEq, bestEq] at upper

include representative trace ready current timely dirty failed in
/-- Actual dirty failed-publication binding rationality transfers at the same
assessment and whole-policy information fiber. The sunk charge is included in
both genuine comparator values; no quiet-prefix half-value floor is used. -/
theorem dirty_failed_binding_rationality_scaled
    (probability : ℝ) (probabilityNonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (LateOpeningRuntimeBobRationality.context weight nonnegative site reward forfeit
        (LateOpeningRuntimeAllOrNoneTrafficAudit.sample probability probabilityNonnegative bounded)
        deposit assessment)) :
    assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit
        (fun owner => probability * deposit owner) assessment) := by
  let scaled := fun owner => probability * deposit owner
  let auditContext := LateOpeningRuntimeBobRationality.context weight nonnegative site reward
    forfeit (LateOpeningRuntimeAllOrNoneTrafficAudit.sample probability probabilityNonnegative
      bounded) deposit assessment
  have integrable (alternative) : auditContext.IntegrableAt alternative :=
    payoffIntegrable_of_bounded _ _ fun history =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
        (LateOpeningRuntimeAllOrNoneTrafficAudit.sample probability probabilityNonnegative bounded)
        deposit history.state
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (integrable (assessment.strategy bob))
    (fun alternative _ => integrable alternative)).mp rational
  have answerEq (bit : Bool) :
      auditContext.value (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative
        (LateOpeningRuntimeBobBindingDecision.bitGuess bit)) =
      (context weight nonnegative site reward forfeit scaled assessment).value
        (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative
          (LateOpeningRuntimeBobBindingDecision.bitGuess bit)) := by
    rw [sampled_answer_context_value weight nonnegative site representative execution trace ready
      current timely dirty failed reward forfeit deposit probability probabilityNonnegative bounded
      assessment,
      full_answer_context_value weight nonnegative site representative execution trace ready
        current timely dirty failed reward forfeit scaled assessment]
  have lower : bestGuessValue weight nonnegative site reward forfeit scaled assessment ≤
      auditContext.value (assessment.strategy bob) := by
    unfold bestGuessValue
    apply max_le
    · rw [← answerEq false]
      exact comparison _ (Set.mem_univ _)
    · rw [← answerEq true]
      exact comparison _ (Set.mem_univ _)
  have dominated := LateOpeningRuntimeAllOrNoneBinding.context_value_le_scaled probability
    probabilityNonnegative bounded weight nonnegative reward forfeit deposit collateral assessment
    ((LateOpeningRuntimeGame.model weight nonnegative).truncatedRunner
      (2 * LateOpeningRuntimeService.horizon + 1)) site (assessment.strategy bob)
  apply (Context.isLocallyOptimal_iff_of_integrable
    (LateOpeningRuntimeBobBindingDecision.context_integrable weight nonnegative site reward
      forfeit scaled assessment (assessment.strategy bob))
    (fun alternative _ => LateOpeningRuntimeBobBindingDecision.context_integrable weight nonnegative
      site reward forfeit scaled assessment alternative)).mpr
  intro alternative _
  have upper := full_value_le_bestGuessValue weight nonnegative site representative execution trace
    ready current timely dirty failed reward forfeit scaled forfeitNonnegative
    assessment alternative
  exact upper.trans (lower.trans dominated)

end BindingFiber
end Vegas.Examples.LateOpeningRuntimeAllOrNoneDirtyFailedBinding
