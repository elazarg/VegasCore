/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeRecoveryValue
import Vegas.Examples.LateOpeningRuntimeAliceSilentContinuation
import Vegas.Examples.LateOpeningRuntimeBobQuietPrefix

/-! # Silent native continuations at the final proper-opening opportunity -/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeRecoveryDomination

open Interaction GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeAliceContinuation LateOpeningRuntimeAliceEmptyDecision
  LateOpeningRuntimeLateAcceptance

/-- The real silent last callback reaches Bob's ready clock-three opportunity.
The earlier six-round prefix is reconstructed using actual native round laws. -/
theorem silent_binding_opportunity (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (bit : Bool) (label : Fin 3)
    (before observed : app.Execution)
    (reached : before ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 3 ((secondLateDecision bit label 1 false).respond app alice ⟨none⟩)).support)
    (sampled : observed ∈ (before.environmentStep app (.activate bob)).support) :
    Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, observed⟩)) ∧
      LateOpeningRuntimeBobBindingService.SilentRecall observed ∧
      observed.application.config.cut.Ready bobBindEvent ∧
      observed.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent ∧
      observed.application.clock = 3 := by
  let early := LateOpeningRuntimeLateResponseKernel.earlyQuiet bit label ⟨none⟩ ∅
  let start := (secondLateDecision bit label 1 false).respond app alice ⟨none⟩
  have law := app.continuation_policy_independent_of_unactivated
    (LateOpeningRuntimeService.scheduler weight nonnegative) 8 alice
    (LateOpeningRuntimeAliceIncentive.alice_absent weight nonnegative)
    players (quietAgainst players)
    (fun who different => by simp [quietAgainst, different]) 3 start (by
      change 8 ≤ (secondLateDecision bit label 1 false).environmentRecall.length
      rfl)
  change before ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 3 start).support at reached
  rw [law] at reached
  have first : app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (quietAgainst players) 3 early = PMF.pure start := by
    rw [LateOpeningRuntimeLateResponseKernel.final_decision_rounds]
    simp only [ReactiveApplication.invoke, quietAgainst, ↓reduceIte, PMF.pure_map]
    rfl
  have six : before ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (quietAgainst players) 6 early).support := by
    rw [show 6 = 3 + 3 from rfl, app.runRounds_add, first, PMF.pure_bind]
    exact reached
  obtain ⟨earlyRaw⟩ := bobObserved_second_trace weight nonnegative bit label
  have earlyTrace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) earlyRaw
  have quiet : LateOpeningRuntimeBobBindingService.SilentRecall early := by
    intro entry member
    change entry ∈ (bobObserved bit label 1 false).recall bob at member
    rw [bobObserved_second_recall] at member
    cases List.mem_singleton.mp member
    rfl
  obtain ⟨trace, silent, ready, timely, clock, _⟩ :=
    LateOpeningRuntimeBobQuietPrefix.binding_activation weight nonnegative
      (quietAgainst players) early before observed earlyTrace
      (LateOpeningRuntimeLateResponseKernel.early_cursor bit label ⟨none⟩ ∅)
      (by change aliceEvent ∉ (∅ : Finset nativeGraph.EventId); decide) quiet six sampled
  exact ⟨trace, silent, ready, timely, clock⟩

/-- Actual last-turn silence retains no Alice-authored packet throughout the
native continuation, even with arbitrary remaining policies. -/
theorem silent_no_alice_inputs (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (bit : Bool) (label : Fin 3)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 18 ((secondLateDecision bit label 1 false).respond app alice ⟨none⟩)).support) :
    ∀ message ∈ final.network.inputs, message.sender ≠ alice := by
  let predicate := fun execution : app.Execution =>
    ∀ message ∈ execution.network.inputs, message.sender ≠ alice
  have invariant : app.PolicyInvariant (quietAgainst players) predicate := by
    constructor
    · intro execution who action valid supported
      by_cases owner : who = alice
      · subst who
        simp only [quietAgainst, ↓reduceIte, PMF.mem_support_pure_iff] at supported
        subst action
        exact valid
      · rcases action with ⟨transmission⟩
        cases transmission with
        | none => exact valid
        | some material =>
          intro message member authored
          change message ∈ execution.network.inputs ++ [_] at member
          rcases List.mem_append.mp member with old | issued
          · exact valid message old authored
          · cases List.mem_singleton.mp issued
            exact owner authored
    · intro execution next command valid moved message member authored
      rw [app.environmentStep_inputs execution next command moved] at member
      exact valid message member authored
  let decision := LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label
  have initialClean := no_alice_inputs weight nonnegative ⟨18, some alice, decision.execution⟩
    decision.trace decision.quiet
  have law := app.continuation_policy_independent_of_unactivated
    (LateOpeningRuntimeService.scheduler weight nonnegative) 8 alice
    (LateOpeningRuntimeAliceIncentive.alice_absent weight nonnegative)
    players (quietAgainst players)
    (fun who different => by simp [quietAgainst, different]) 18
    (decision.execution.respond app alice ⟨none⟩)
    (by rw [app.respond_environmentRecall, decision_cursor weight nonnegative decision])
  change final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 18 (decision.execution.respond app alice ⟨none⟩)).support at reached
  rw [law] at reached
  exact invariant.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) 18
    (decision.execution.respond app alice ⟨none⟩) final initialClean reached

/-- Silence has zero authentic Alice audit charge, derived from actual traffic
absence rather than from acceptance or a prescribed audit outcome. -/
theorem silent_audit_charge_zero (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (bit : Bool) (label : Fin 3)
    (final : app.Execution)
    (sample : List (Vegas.SettledEvidence setup .sequential) →
      PMF (List (Vegas.SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 18 ((secondLateDecision bit label 1 false).respond app alice ⟨none⟩)).support) :
    GameTheory.Enforcement.TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (Vegas.serviceSourceAudit setup .sequential deadline leaks sample)
        (app.finished final) alice = 0 := by
  let decision := LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label
  obtain ⟨responded⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18 decision.execution alice
    ⟨none⟩ decision.trace
  obtain ⟨trace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 18 _ final
      responded reached
  apply LateOpeningRuntimeUtility.alice_audit_charge_zero sample authentic ⟨0, none, final⟩
  intro traffic member owner
  have inputs := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change (app.executionTraffic final).map ReactiveApplication.TrafficRecord.envelope =
    final.network.inputs at inputs
  have submitted : traffic.envelope ∈ final.network.inputs := by
    rw [← inputs]
    exact List.mem_map.mpr ⟨traffic, member, rfl⟩
  exact False.elim (silent_no_alice_inputs weight nonnegative players bit label final
    reached traffic.envelope submitted owner)

/-- The complete actual silent continuation against Safe publishes Safe and
retains Alice's failed source publication. -/
theorem silent_safe_publication (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy)
    (bobPolicy : players bob = LateOpeningRuntimeBobSafeContinuation.safePolicy)
    (bit : Bool) (label : Fin 3) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 18 ((secondLateDecision bit label 1 false).respond app alice ⟨none⟩)).support) :
    final.application.config.store (.inr aliceEvent) = some (.failure : PublicationResult Bool) ∧
      final.application.config.store (.inr bobRevealEvent) = some (.success safe) := by
  let decision := LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label
  have failed := LateOpeningRuntimeAliceSilentContinuation.silence_terminal_failure
    weight nonnegative decision players final reached
  rw [show 18 = 3 + 15 from rfl, app.runRounds_add] at reached
  obtain ⟨before, first, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have cursor : before.environmentRecall.length = 11 := by
    rw [app.runRounds_environmentRecall_length (LateOpeningRuntimeService.scheduler
      weight nonnegative) players 3 _ before first]
    rfl
  rw [LateOpeningRuntimeSettlementContinuation.receiver_suffix weight nonnegative
    players before cursor] at continued
  obtain ⟨observed, sampled, receiver⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ continued)
  obtain ⟨⟨trace⟩, quiet, ready, timely, clock⟩ := silent_binding_opportunity
    weight nonnegative players bit label before observed first sampled
  exact ⟨failed, LateOpeningRuntimeRecoveryValue.receiverCompletion_safe weight nonnegative
    players bobPolicy observed final trace quiet ready timely clock receiver⟩

/-- Actual silence pays exactly the source forfeit, with no Alice audit loss. -/
theorem silent_safe_payoff (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy)
    (bobPolicy : players bob = LateOpeningRuntimeBobSafeContinuation.safePolicy)
    (bit : Bool) (label : Fin 3) (reward forfeit : ℝ) (deposit : Player → ℝ)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 18 ((secondLateDecision bit label 1 false).respond app alice ⟨none⟩)).support) :
    LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual) deposit
      (app.finished final) alice = -forfeit := by
  obtain ⟨failed, published⟩ := silent_safe_publication weight nonnegative players bobPolicy
    bit label final reached
  have clear := silent_audit_charge_zero weight nonnegative players bit label final
    (fun actual => PMF.pure actual)
    (fun actual observed supported => by
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact List.Subset.refl _) reached
  let decision := LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label
  obtain ⟨responded⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18 decision.execution alice
    ⟨none⟩ decision.trace
  obtain ⟨trace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 18 _ final responded reached
  have completed := LateOpeningRuntimeService.completes weight nonnegative ⟨0, none, final⟩
    trace ⟨rfl, rfl⟩
  obtain ⟨originalBit, originalLabel, valid⟩ := LateOpeningRuntimeReadout.history_initial_invariant
    LateOpeningRuntimeService.runtime leaks LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) ⟨0, none, final⟩ trace
  have bound := LateOpeningRuntimeReadout.bob_success_from_binding final.application _
    valid.reachable safe published
  have decoded := LateOpeningRuntimeReadout.decode_terminalStateOf final.application
    originalBit originalLabel .failure (.success safe) (.success safe)
    valid.reachable.inputs_eq failed bound published
  have readout : Vegas.serviceSourceReadout setup .sequential deadline leaks (app.finished final) =
      some (LateOpeningRuntimeReadout.terminalStateOf originalBit originalLabel .failure
        (.success safe) (.success safe)) := by
    change (if final.application.config.cut.Terminal then
      Vegas.decodeState? (Vegas.terminalRefs program) final.application.config.store else none) = _
    rw [ite_eq_left completed]
    exact decoded
  unfold LateOpeningRuntimeGame.payoff GameTheory.Enforcement.TerminalAudit.utility
  rw [clear, zero_mul, sub_zero,
    LateOpeningRuntimeUtility.nativeBaseUtility_of_readout reward forfeit _ _ readout alice,
    LateOpeningRuntimeUtility.sourceUtility_alice_failure]
  norm_num [safe, answerValue]

/-- Full native payoff law of the actual silent action at the legal late callback. -/
theorem silent_safe_payoff_law (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy)
    (bobPolicy : players bob = LateOpeningRuntimeBobSafeContinuation.safePolicy)
    (bit : Bool) (label : Fin 3) (reward forfeit : ℝ) (deposit : Player → ℝ) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18
      ((secondLateDecision bit label 1 false).respond app alice ⟨none⟩)).map
      (fun final => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final) alice) =
      PMF.pure (-forfeit) := by
  rw [← PMF.map_const (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 18 ((secondLateDecision bit label 1 false).respond app alice ⟨none⟩)) (-forfeit)]
  apply map_congr_on_support
  intro final reached
  exact silent_safe_payoff weight nonnegative players bobPolicy bit label reward forfeit deposit
    final reached

/-- The literal late compiled opening is strictly worse than the actual silent
raw response when the fixed collateral exceeds its late inclusion benefit. -/
theorem late_compiler_action_value_lt_silence (weight : ℝ) (nonnegative : 0 ≤ weight)
    (positive : 0 < weight) (players : Player → app.Policy)
    (bobPolicy : players bob = LateOpeningRuntimeBobSafeContinuation.safePolicy)
    (bit : Bool) (label : Fin 3) (reward forfeit : ℝ) (deposit : Player → ℝ)
    (collateral : weight * (reward / 2 + forfeit) < deposit alice) :
    expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18
      ((secondLateDecision bit label 1 false).respond app alice
        (LateOpeningRuntimeService.runtime.reactiveDecision leaks alice aliceEvent true
          ((secondLateDecision bit label 1 false).observe app alice).application)))
      (fun final => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final) alice) <
      expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18
        ((secondLateDecision bit label 1 false).respond app alice ⟨none⟩))
        (fun final => LateOpeningRuntimeGame.payoff reward forfeit
          (fun actual => PMF.pure actual) deposit (app.finished final) alice) := by
  have silent := congrArg (fun law : PMF ℝ => expect law id)
    (silent_safe_payoff_law weight nonnegative players bobPolicy bit label reward forfeit deposit)
  rw [expect_map, expect_pure] at silent
  simp only [Function.comp_def, id_eq] at silent
  have opening : expect (app.runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) players 18
      ((secondLateDecision bit label 1 false).respond app alice
        (LateOpeningRuntimeService.runtime.reactiveDecision leaks alice aliceEvent true
          ((secondLateDecision bit label 1 false).observe app alice).application)))
      (fun final => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final) alice) =
      inclusionProbability weight * (reward / 2) -
        (1 - inclusionProbability weight) * (forfeit + deposit alice) := by
    rw [LateOpeningRuntimeRecoveryValue.reactiveDecision_late_opening]
    exact LateOpeningRuntimeRecoveryValue.late_callback_safe_value weight nonnegative positive
      players bobPolicy bit label _
      (LateOpeningRuntimeAliceOpeningContinuation.canonical_emits_opening weight nonnegative
        (LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label))
      reward forfeit deposit
  rw [opening, silent]
  have denominator : 0 < 1 + weight := by linarith
  have formula : LateOpeningRuntimeLateAcceptance.inclusionProbability weight =
      weight / (1 + weight) := by
    simp [LateOpeningRuntimeLateAcceptance.inclusionProbability, MessageNetwork.inclusionMass]
  rw [formula]
  have compressed : weight / (1 + weight) * (reward / 2) -
      (1 - weight / (1 + weight)) * (forfeit + deposit alice) =
        (weight * (reward / 2) - forfeit - deposit alice) / (1 + weight) := by
    field_simp [ne_of_gt denominator]
    ring
  rw [compressed]
  apply (div_lt_iff₀ denominator).2
  nlinarith

/-- Under the same fixed source Safe continuation, TRUE strictly beats FALSE
even when late native collateral reverses the two actual response values. -/
theorem source_opening_value_gt_silence (bit : Bool) (label : Fin 3)
    (reward forfeit : ℝ) (benefit : 0 < reward / 2 + forfeit) :
    expect (SourceProgram.run program (constantProfile false safe true) (sourceInitial bit label))
        (fun final => LateOpeningRuntimeUtility.sourceUtility reward forfeit final alice) <
      expect (SourceProgram.run program (constantProfile true safe true) (sourceInitial bit label))
        (fun final => LateOpeningRuntimeUtility.sourceUtility reward forfeit final alice) := by
  rw [run_constant, run_constant, expect_pure, expect_pure,
    (LateOpeningRuntimeUtility.sourceUtility_intended reward forfeit bit label).1]
  have failed : LateOpeningRuntimeUtility.sourceUtility reward forfeit
      (finalState bit label false safe true) alice = -forfeit := by
    change LateOpeningRuntimeUtility.sourceUtility reward forfeit
      (LateOpeningRuntimeReadout.terminalStateOf bit label .failure (.success safe)
        (.success safe)) alice = _
    rw [LateOpeningRuntimeUtility.sourceUtility_alice_failure]
    norm_num [safe, answerValue]
  rw [failed]
  linarith

/-- Every positive collateral fixed before choosing the fallible builder admits
a positive service weight with the opposite native and source action rankings.
The inequalities compare actual local continuations, not equilibria. -/
theorem exists_positive_weight_action_reversal (reward forfeit : ℝ)
    (deposit : Player → ℝ)
    (benefit : 0 < reward / 2 + forfeit) (collateral : 0 < deposit alice) :
    ∃ (weight : ℝ) (nonnegative : 0 ≤ weight), 0 < weight ∧
      ∀ (players : Player → app.Policy),
        players bob = LateOpeningRuntimeBobSafeContinuation.safePolicy →
          ∀ (bit : Bool) (label : Fin 3),
            expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
              players 18 ((secondLateDecision bit label 1 false).respond app alice
                (LateOpeningRuntimeService.runtime.reactiveDecision leaks alice aliceEvent true
                  ((secondLateDecision bit label 1 false).observe app alice).application)))
              (fun final => LateOpeningRuntimeGame.payoff reward forfeit
                (fun actual => PMF.pure actual) deposit (app.finished final) alice) <
            expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
              players 18 ((secondLateDecision bit label 1 false).respond app alice ⟨none⟩))
              (fun final => LateOpeningRuntimeGame.payoff reward forfeit
                (fun actual => PMF.pure actual) deposit (app.finished final) alice) ∧
            expect (SourceProgram.run program (constantProfile false safe true)
              (sourceInitial bit label))
              (fun final => LateOpeningRuntimeUtility.sourceUtility reward forfeit final alice) <
            expect (SourceProgram.run program (constantProfile true safe true)
              (sourceInitial bit label))
              (fun final =>
                LateOpeningRuntimeUtility.sourceUtility reward forfeit final alice) := by
  let weight := deposit alice / (2 * (reward / 2 + forfeit))
  have positive : 0 < weight := div_pos collateral (mul_pos (by norm_num) benefit)
  have mass : weight * (reward / 2 + forfeit) = deposit alice / 2 := by
    dsimp [weight]
    rw [div_mul_eq_mul_div]
    apply (div_eq_div_iff (mul_ne_zero (by norm_num) (ne_of_gt benefit)) (by norm_num)).2
    ring
  refine ⟨weight, positive.le, positive, ?_⟩
  intro players bobPolicy bit label
  constructor
  · apply late_compiler_action_value_lt_silence weight positive.le positive players bobPolicy
      bit label reward forfeit deposit
    rw [mass]
    linarith
  · exact source_opening_value_gt_silence bit label reward forfeit benefit

end Vegas.Examples.LateOpeningRuntimeRecoveryDomination
