/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.PayoffInference
import Vegas.Examples.MonitoredGuessing.Conformance
import Vegas.Examples.MonitoredGuessing.RestrictedExecution
import Interaction.ReactiveNormalHistory

/-! # Fixed comparison charges for the restricted native stack

The declared integer return table determines expected charges before any
strategy is chosen. Bounds include every publication result, including two
failures. Alice's authentic private observation is sampled with probability one half;
Bob's liability audits included packets against the certified opening format.
These quantities support continuation comparisons. Actual report delivery and
escrow collection are separate kernels in `TableSettlement`. Watcher
indifference requires its declared return to be zero.
-/

namespace Vegas.Examples.MonitoredGuessing.Enforcement

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def outcomeValues (table : PayoffTable) (who : Player) : Finset Int :=
  allResults.image (fun result => table result who)

theorem outcomeValues_nonempty (table : PayoffTable) (who : Player) :
    (outcomeValues table who).Nonempty :=
  ⟨_, Finset.mem_image_of_mem _ (mem_allResults ⟨.failure, .failure⟩)⟩

def payoffLower (table : PayoffTable) (who : Player) : Int :=
  (outcomeValues table who).min' (outcomeValues_nonempty table who)

def payoffUpper (table : PayoffTable) (who : Player) : Int :=
  (outcomeValues table who).max' (outcomeValues_nonempty table who)

def payoffRange (table : PayoffTable) (who : Player) : Int :=
  payoffUpper table who - payoffLower table who

theorem payoffLower_le (table : PayoffTable) (who : Player) (result : Results) :
    payoffLower table who ≤ table result who :=
  Finset.min'_le (outcomeValues table who) _
    (Finset.mem_image_of_mem _ (mem_allResults result))

theorem le_payoffUpper (table : PayoffTable) (who : Player) (result : Results) :
    table result who ≤ payoffUpper table who :=
  Finset.le_max' (outcomeValues table who) _
    (Finset.mem_image_of_mem _ (mem_allResults result))

theorem payoffRange_nonnegative (table : PayoffTable) (who : Player) :
    0 ≤ payoffRange table who := by
  exact sub_nonneg.mpr ((payoffLower_le table who ⟨.failure, .failure⟩).trans
    (le_payoffUpper table who ⟨.failure, .failure⟩))

/-- An executable integer charge, uniform over source profiles and continuations. -/
def charge (table : PayoffTable) (who : Player) : Int :=
  if who = alice then 2 * payoffRange table who
  else if who = bob then payoffRange table who else 0

theorem charge_nonnegative (table : PayoffTable) (who : Player) :
    0 ≤ charge table who := by
  unfold charge
  split_ifs
  · exact mul_nonneg (by omega) (payoffRange_nonnegative table who)
  · exact payoffRange_nonnegative table who
  · exact le_rfl

noncomputable section

theorem alice_charge (table : PayoffTable) :
    (charge table alice : ℝ) =
      2 * ((payoffUpper table alice : ℝ) - payoffLower table alice) := by
  simp only [charge, ↓reduceIte, payoffRange, Int.cast_mul, Int.cast_ofNat, Int.cast_sub]

theorem bob_charge (table : PayoffTable) :
    (charge table bob : ℝ) =
      (payoffUpper table bob : ℝ) - payoffLower table bob := by
  simp [charge, bob, alice, payoffRange]

def liability (execution : nativeApp.Execution) (who : Player) : ℝ :=
  if who = alice then if aliceLiability execution then 1 else 0
  else if who = bob then Conformance.bobLedgerLiability execution else 0

def comparisonExecutionUtility (table : PayoffTable) (execution : nativeApp.Execution)
    (who : Player) : ℝ :=
  (table (nativeResults execution.application.config) who : ℝ) -
    (charge table who : ℝ) * liability execution who

/-- The finite summary read by comparison utilities: results, Alice's authentic
evidence mark, and Bob's ledger format violation. -/
private def settlementSummary (execution : nativeApp.Execution) : Results × Bool × Bool :=
  (nativeResults execution.application.config, aliceLiability execution,
    Conformance.bobLedgerViolation execution)

private def summaryUtility (table : PayoffTable) (who : Player)
    (summary : Results × Bool × Bool) : ℝ :=
  (table summary.1 who : ℝ) - (charge table who : ℝ) *
    (if who = alice then (if summary.2.1 then 1 else 0)
      else if who = bob then (if summary.2.2 then 1 else 0) else 0)

theorem comparisonExecutionUtility_integrable (table : PayoffTable) (who : Player)
    (law : PMF nativeApp.Execution) :
    PayoffIntegrable law (fun execution => comparisonExecutionUtility table execution who) :=
  payoffIntegrable_of_finite_summary law settlementSummary (summaryUtility table who)

def comparisonStateUtility (table : PayoffTable) (state : nativeApp.ProtocolState) : Player → ℝ :=
  state.elim (fun _ => 0) (fun control => comparisonExecutionUtility table control.execution)

theorem comparisonStateUtility_integrable (table : PayoffTable) (who : Player)
    (law : PMF nativeApp.ProtocolState) :
    PayoffIntegrable law (fun state => comparisonStateUtility table state who) := by
  have summarized : (fun state : nativeApp.ProtocolState => comparisonStateUtility table state
    who) =
      fun state => ((state.map fun control => settlementSummary control.execution).elim 0
        (summaryUtility table who)) := by
    funext state
    cases state <;> rfl
  rw [summarized]
  exact payoffIntegrable_of_finite_summary law _
    (fun summary : Option (Results × Bool × Bool) => summary.elim 0 (summaryUtility table who))

theorem liability_nonnegative (execution : nativeApp.Execution) (who : Player) :
    0 ≤ liability execution who := by
  simp only [liability, Conformance.bobLedgerLiability]
  split_ifs <;> norm_num

theorem comparisonExecutionUtility_le (table : PayoffTable) (execution : nativeApp.Execution)
    (who : Player) :
    comparisonExecutionUtility table execution who ≤ payoffUpper table who := by
  have charge : (0 : ℝ) ≤ charge table who := by
    exact_mod_cast charge_nonnegative table who
  apply (sub_le_self _ (mul_nonneg charge (liability_nonnegative execution who))).trans
  exact_mod_cast le_payoffUpper table who (nativeResults execution.application.config)

theorem comparisonExecutionUtility_clean (table : PayoffTable) (execution : nativeApp.Execution)
    (aliceClear : aliceLiability execution = false)
    (bobClear : Conformance.bobLedgerViolation execution = false) (who : Player) :
    comparisonExecutionUtility table execution who =
      (table (nativeResults execution.application.config) who : ℝ) := by
  simp only [comparisonExecutionUtility, liability, aliceClear, Conformance.bobLedgerLiability,
    bobClear, Bool.false_eq_true, ↓reduceIte, ite_self, mul_zero, sub_zero]

theorem comparisonExecutionUtility_normalization (table : PayoffTable) (execution :
  nativeApp.Execution) :
    comparisonExecutionUtility table (Restricted.normalization.execution execution) =
      comparisonExecutionUtility table execution := rfl

theorem comparisonStateUtility_normalization (table : PayoffTable) (state :
  nativeApp.ProtocolState) :
    comparisonStateUtility table (Restricted.normalization.state state) =
      comparisonStateUtility table state := by
  cases state <;> rfl

theorem comparisonExecutionUtility_watcher (table : PayoffTable)
    (zero : ∀ result, table result watcher = 0) (execution : nativeApp.Execution) :
    comparisonExecutionUtility table execution watcher = 0 := by
  simp [comparisonExecutionUtility, liability, watcher, alice, bob, zero]

theorem comparisonStateUtility_watcher (table : PayoffTable)
    (zero : ∀ result, table result watcher = 0) (state : nativeApp.ProtocolState) :
    comparisonStateUtility table state watcher = 0 := by
  cases state with
  | none => rfl
  | some control => exact comparisonExecutionUtility_watcher table zero control.execution

theorem alice_utility (table : PayoffTable) (execution : nativeApp.Execution) :
    comparisonExecutionUtility table execution alice =
      comparisonSettlement (fun result => table result alice) (charge table alice) execution := by
  simp only [comparisonExecutionUtility, liability, ↓reduceIte, comparisonSettlement]
  cases aliceLiability execution <;> simp

theorem bob_utility (table : PayoffTable) (execution : nativeApp.Execution) :
    comparisonExecutionUtility table execution bob =
      (table (nativeResults execution.application.config) bob : ℝ) -
        (charge table bob : ℝ) * Conformance.bobLedgerLiability execution := by
  simp [comparisonExecutionUtility, liability, alice, bob]

theorem detected_bob_utility_le (table : PayoffTable) (execution : nativeApp.Execution)
    (detected : Conformance.bobLedgerViolation execution = true) :
    comparisonExecutionUtility table execution bob ≤ payoffLower table bob := by
  simp only [bob_utility, Conformance.bobLedgerLiability, detected, ↓reduceIte, mul_one]
  rw [bob_charge]
  have upper : (table (nativeResults execution.application.config) bob : ℝ) ≤
      payoffUpper table bob := by
    exact_mod_cast le_payoffUpper table bob _
  linarith

theorem lower_le_expect (table : PayoffTable) (who : Player) (outcomes : PMF Results) :
    (payoffLower table who : ℝ) ≤ expect outcomes (fun result => (table result who : ℝ)) := by
  rw [← expect_constant outcomes (payoffLower table who : ℝ)]
  refine expect_mono (fun result _ => ?_) (payoffIntegrable_constant _ _)
    (payoffIntegrable_of_finite _ _)
  exact_mod_cast payoffLower_le table who result

/-- The actual passive-monitor kernel bounds every initial raw submission,
even when later players use arbitrary policies. Its prescribed reporting is
part of `monitoredPrefixLaw`, not a claim about arbitrary watcher policies. -/
theorem initial_submission_le_lower (table : PayoffTable)
    (bit : Bool) (submission : WitnessedSubmission nativeGraph)
    (players : Player → nativeApp.Policy) (plan : List (ServiceInstruction nativeGraph)) :
    expect ((monitoredPrefixLaw bit (submissionAction submission)).bind
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan))
        (fun execution => comparisonExecutionUtility table execution alice) ≤ payoffLower table
          alice := by
  simp only [alice_utility]
  apply submission_deterred_by_range (fun result => table result alice)
    (payoffLower table alice) (payoffUpper table alice) (charge table alice)
  · intro result
    exact_mod_cast le_payoffUpper table alice result
  · exact_mod_cast charge_nonnegative table alice
  · exact le_of_eq (alice_charge table).symm

theorem initial_submission_le_clean_outcomes (table : PayoffTable) (outcomes : PMF Results)
    (bit : Bool) (submission : WitnessedSubmission nativeGraph)
    (players : Player → nativeApp.Policy) (plan : List (ServiceInstruction nativeGraph)) :
    expect ((monitoredPrefixLaw bit (submissionAction submission)).bind
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan))
        (fun execution => comparisonExecutionUtility table execution alice) ≤
      expect outcomes (fun result => (table result alice : ℝ)) :=
  (initial_submission_le_lower table bit submission players plan).trans
    (lower_le_expect table alice outcomes)

theorem before_alice_bob_clear (bit guess : Bool) :
    Conformance.bobLedgerViolation (Restricted.beforeAlice bit guess) = false := by
  cases guess with
  | false =>
      change ledgerViolation bob Conformance.bobPacketPermitted
        (quietBob bit).network.ledger = false
      rw [quiet_bob_network]
      rfl
  | true => exact Conformance.canonical_opening_clear bit

theorem before_alice_utility (table : PayoffTable) (bit guess : Bool) (who : Player) :
    comparisonExecutionUtility table (Restricted.beforeAlice bit guess) who =
      (table (nativeResults (Restricted.beforeAlice bit guess).application.config) who : ℝ) :=
  comparisonExecutionUtility_clean table _ (Restricted.before_alice_no_charge bit guess)
    (before_alice_bob_clear bit guess) who

private theorem maintenance_bob_audit (players : Player → nativeApp.Policy)
    (command : EnvironmentCommand nativeGraph) (before after : nativeApp.Execution)
    (supported : after ∈ (nativeApp.dispatch players (.application command) before).support) :
    Conformance.bobLedgerViolation after = Conformance.bobLedgerViolation before := by
  change after ∈ ((before.environmentStep nativeApp (.application command)).bind
    PMF.pure).support at supported
  rw [PMF.bind_pure] at supported
  exact nativeApp.ledgerViolation_application bob Conformance.bobPacketPermitted
    before after command supported

theorem clock_tail_bob_audit (players : Player → nativeApp.Policy)
    (before after : nativeApp.Execution)
    (supported : after ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      [.tick, .tick, .expire alicePublication] before).support) :
    Conformance.bobLedgerViolation after = Conformance.bobLedgerViolation before := by
  obtain ⟨first, firstMem, restMem⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨second, secondMem, lastMem⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ restMem)
  simp only [runInteractionPlan, PMF.bind_pure] at lastMem
  have firstEq := maintenance_bob_audit players .advanceClock before first
    (by simpa only [interactionStep, interactionInstruction, PMF.pure_bind] using firstMem)
  have secondEq := maintenance_bob_audit players .advanceClock first second
    (by simpa only [interactionStep, interactionInstruction, PMF.pure_bind] using secondMem)
  have finalEq := maintenance_bob_audit players (.expire alicePublication) second after
    (by simpa only [interactionStep, interactionInstruction, PMF.pure_bind] using lastMem)
  exact finalEq.trans (secondEq.trans firstEq)

private theorem alice_opening_bob_audit (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (bit : Bool) (serials : execution.network.SerialsBeforeNext)
    (next : nativeApp.Execution)
    (supported : next ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest alicePublication alice)
      (execution.respond nativeApp alice
        (nativeOpeningAction alicePublication aliceHandle bit))).support) :
    Conformance.bobLedgerViolation next = Conformance.bobLedgerViolation execution := by
  have selected := nativeRuntime.reactiveLatest_after_submit nativeLeaks alice alicePublication
    execution serials
    (⟨⟨.opening alicePublication aliceHandle ⟨.bool, bit⟩, none⟩,
      .owned ⟨aliceHandle, ⟨.bool, bit⟩⟩⟩ : WitnessedSubmission nativeGraph) rfl
  change nativeRuntime.reactiveLatest nativeLeaks alicePublication alice
    ((execution.respond nativeApp alice
      (nativeOpeningAction alicePublication aliceHandle bit)).observeEnvironment nativeApp) =
        .include (alice, execution.network.nextSerial alice) at selected
  rw [nativeRuntime.interaction_includeLatest_environment, selected] at supported
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at supported
  cases (PMF.mem_support_pure_iff _ _).mp supported
  change ledgerViolation bob Conformance.bobPacketPermitted
    (ReactiveApplication.Execution.includePending nativeApp
      (execution.respond nativeApp alice (nativeOpeningAction alicePublication aliceHandle bit))
      (alice, execution.network.nextSerial alice)).network.ledger = _
  rw [nativeApp.includePending_network]
  have lookup : (execution.respond nativeApp alice
      (nativeOpeningAction alicePublication aliceHandle bit)).network.lookup
        (alice, execution.network.nextSerial alice) = some
          ⟨(alice, execution.network.nextSerial alice), _⟩ := serials.lookup_submit alice _
  simp only [MessageNetwork.includePending, lookup]
  change ledgerViolation bob Conformance.bobPacketPermitted
    (execution.network.ledger ++ [⟨(alice, execution.network.nextSerial alice), _⟩]) = _
  let material : nativeApp.Submission :=
    ⟨⟨.opening alicePublication aliceHandle ⟨.bool, bit⟩, none⟩,
      .owned ⟨aliceHandle, ⟨.bool, bit⟩⟩⟩
  let emitted : Message Player nativeApp.Payload :=
    ⟨(alice, execution.network.nextSerial alice),
      nativeApp.packet (nativeApp.submit execution.application alice material) alice
        (execution.network.known alice) material⟩
  change (execution.network.ledger ++ [emitted]).any
    (fun message : Message Player nativeApp.Payload =>
      decide (message.sender = bob) && !Conformance.bobPacketPermitted message.payload) =
    execution.network.ledger.any (fun message : Message Player nativeApp.Payload =>
      decide (message.sender = bob) && !Conformance.bobPacketPermitted message.payload)
  have authored : emitted.sender ≠ bob := by change (0 : Fin 3) ≠ 1; decide
  rw [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  simp only [decide_eq_false authored, Bool.false_and, Bool.or_false]

theorem alice_service_bob_clear (players : Player → nativeApp.Policy)
    (bit guess disclose : Bool) (final : nativeApp.Execution)
    (supported : final ∈
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
        ((Restricted.beforeAlice bit guess).respond nativeApp alice
          (Restricted.choiceAction alicePublication aliceHandle bit disclose))).support) :
    Conformance.bobLedgerViolation final = false := by
  cases disclose with
  | false =>
      simp only [Restricted.choiceAction, Bool.false_eq_true, ↓reduceIte,
        Restricted.silent_alice_service] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact before_alice_bob_clear bit guess
  | true =>
      obtain ⟨middle, middleMem, tailMem⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      exact (clock_tail_bob_audit players middle final tailMem).trans
        ((alice_opening_bob_audit players (Restricted.beforeAlice bit guess) bit
          (Restricted.before_alice_serials bit guess) middle middleMem).trans
            (before_alice_bob_clear bit guess))

/-- Every source choice retains its results and its entire declared payoff
vector after the actual final native service, with no charge deductions. -/
theorem alice_service_payoff_law (table : PayoffTable) (players : Player → nativeApp.Policy)
    (bit guess disclose : Bool) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
      ((Restricted.beforeAlice bit guess).respond nativeApp alice
        (Restricted.choiceAction alicePublication aliceHandle bit disclose))).map
          (fun final => (nativeResults final.application.config, comparisonExecutionUtility
            table final)) =
      PMF.pure (sourceResults (finalConfig bit guess disclose).state,
        fun who => (table (sourceResults (finalConfig bit guess disclose).state) who : ℝ)) := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨final, reached, rfl⟩ := PMF.support_map .. ▸ supported
  have summary : (nativeResults final.application.config, aliceLiability final) =
      (sourceResults (finalConfig bit guess disclose).state, false) := by
    apply (PMF.mem_support_pure_iff _ _).mp
    rw [Restricted.source_results, ← Restricted.alice_service_summary players bit guess disclose,
      PMF.support_map]
    exact ⟨final, reached, rfl⟩
  change (nativeResults final.application.config, comparisonExecutionUtility table final) = _
  apply Prod.ext
  · exact congrArg (fun pair : Results × Bool => pair.1) summary
  funext who
  change comparisonExecutionUtility table final who = _
  rw [comparisonExecutionUtility_clean table final (congrArg Prod.snd summary)
    (alice_service_bob_clear players bit guess disclose final reached)]
  exact congrArg (fun pair : Results × Bool => (table pair.1 who : ℝ)) summary

theorem alice_service_value (table : PayoffTable) (players : Player → nativeApp.Policy)
    (bit guess disclose : Bool) (who : Player) :
    expect (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
      ((Restricted.beforeAlice bit guess).respond nativeApp alice
        (Restricted.choiceAction alicePublication aliceHandle bit disclose)))
          (fun final => comparisonExecutionUtility table final who) =
      (table (sourceResults (finalConfig bit guess disclose).state) who : ℝ) := by
  have law := congrArg (fun law : PMF (Results × (Player → ℝ)) =>
    expect law (fun outcome => outcome.2 who)) (alice_service_payoff_law table players bit guess
      disclose)
  simpa only [expect_map, expect_pure, Function.comp_def] using law

end

end Vegas.Examples.MonitoredGuessing.Enforcement
