/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobAudit
import Vegas.Examples.LateOpeningRuntimeNash
import GameTheoryExtensions.Math.Probability.Regret

/-! # Final native publication incentives after a clean accepted binding

At the actual last Bob callback, a ready and timely successfully bound answer
has a clean canonical opening continuation. Every raw response either publishes
that same immutable answer or incurs a publication forfeit. Authentic audit
deductions are nonnegative. The comparison uses the initialized native readout
and complete remaining physical continuation; it does not assert a sequential
equilibrium or an incentive result at earlier callbacks.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobIncentive

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeBobService LateOpeningRuntimeBobAudit LateOpeningRuntimeUtility

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- Legal initialized final Bob histories whose accepted answer can still be
opened, with earlier Bob traffic consisting of accepted canonical bindings. -/
structure DecisionHistory where
  execution : app.Execution
  trace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨6, some bob, execution⟩)
  answer : Answer
  bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer)
  ready : execution.application.config.cut.Ready bobRevealEvent
  timely : execution.application.WithinDeadline
    LateOpeningRuntimeService.runtime bobRevealEvent
  clean : CleanBindings execution

def continuation (history : DecisionHistory weight nonnegative) (response : app.Action)
    (players : Player → app.Policy) : PMF app.Execution :=
  app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 6
    (history.execution.respond app bob response)

def canonical (history : DecisionHistory weight nonnegative) : app.Action :=
  LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
    (history.execution.recall bob) (history.execution.observe app bob) bobRevealEvent true

/-- The comparator uses only Bob's own recall and current observation. It is
one available response across all hidden histories at the same information. -/
theorem canonical_same_information (first second : DecisionHistory weight nonnegative)
    (sameRecall : first.execution.recall bob = second.execution.recall bob)
    (sameView : first.execution.observe app bob = second.execution.observe app bob) :
    canonical weight nonnegative first = canonical weight nonnegative second := by
  unfold canonical
  rw [sameRecall, sameView]

theorem continuation_trace (history : DecisionHistory weight nonnegative)
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (continuation weight nonnegative history response players).support) :
    Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨0, none, final⟩)) := by
  obtain ⟨responded⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 6 history.execution bob response
      history.trace
  exact app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 6 _ final responded reached

theorem continuation_readout (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨6, some bob, execution⟩))
    (answer : Answer)
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (bit : Bool) (label : Fin 3)
    (valid : EventGraphRuntime.State.Invariant (graph := nativeGraph)
      (setup.eventInputs (sourceInitial bit label)) execution.application)
    (aliceResult : PublicationResult Bool)
    (aliceStored : execution.application.config.store (.inr aliceEvent) = some aliceResult)
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 6
      (execution.respond app bob response)).support) :
    ∃ result,
      final.application.config.store (.inr bobRevealEvent) = some result ∧
      serviceSourceReadout setup .sequential deadline leaks (app.finished final) =
        some (terminalStateOf bit label aliceResult (.success answer) result) := by
  obtain ⟨responded⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
    6 execution bob response trace
  obtain ⟨terminalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 0 6 _ final responded reached
  have complete := (contract weight nonnegative).completes ⟨0, none, final⟩ terminalTrace
    ⟨rfl, rfl⟩
  have invariant := LateOpeningRuntimeService.runtime.reactiveStateInvariant leaks
    (setup.eventInputs (sourceInitial bit label))
  have after := (ReactiveApplication.Invariant.policyInvariant app invariant players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 6 _ final
      (invariant.respond execution bob response valid) reached
  have inherited := bob_continuation_other_fields LateOpeningRuntimeService.runtime leaks players
    (LateOpeningRuntimeService.scheduler weight nonnegative) 6 execution final ready response
      reached
  have aliceAfter : final.application.config.store (.inr aliceEvent) = some aliceResult :=
    (inherited _ (by decide)).trans aliceStored
  have boundAfter : final.application.config.store (.inr bobBindEvent) = some (.success answer) :=
    (inherited _ (by decide)).trans bound
  obtain ⟨result, stored⟩ := Option.isSome_iff_exists.mp
    (final.application.config.store_available_of_terminal complete (.inr bobRevealEvent))
  refine ⟨result, stored, ?_⟩
  have decoded := decode_terminalStateOf final.application bit label aliceResult
    (.success answer) result after.reachable.inputs_eq aliceAfter boundAfter stored
  change (if final.application.config.cut.Terminal then
    decodeState? (terminalRefs program) final.application.config.store else none) = _
  rw [ite_eq_left complete]
  exact decoded

/-- Canonical opening succeeds and incurs zero actual terminal audit charge,
under arbitrary future raw policies and authentic evidence sampling. -/
theorem canonical_clean (history : DecisionHistory weight nonnegative)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈
      (continuation weight nonnegative history
        (canonical weight nonnegative history) players).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success history.answer) ∧
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks sample)
          (app.finished final) bob = 0 := by
  obtain ⟨candidate, material, decision, terminal⟩ := canonical_terminal weight nonnegative
    history.execution history.trace history.answer history.bound history.ready history.timely
  have selected : canonical weight nonnegative history = ⟨some material⟩ := decision
  rw [selected] at reached
  obtain ⟨published, accepted, inputs⟩ := terminal players final reached
  obtain ⟨trace⟩ := continuation_trace weight nonnegative history
    ⟨some material⟩ players final reached
  have inherited := bob_continuation_other_fields LateOpeningRuntimeService.runtime leaks players
    (LateOpeningRuntimeService.scheduler weight nonnegative) 6 history.execution final
      history.ready ⟨some material⟩ reached
  have boundAfter : final.application.config.store (.inr bobBindEvent) =
      some (.success history.answer) := (inherited _ (by decide)).trans history.bound
  refine ⟨published, charge_zero weight nonnegative ⟨0, none, final⟩ trace history.answer
    boundAfter history.execution candidate accepted ?_ sample authentic⟩
  intro message member owner
  rw [inputs] at member
  rcases List.mem_append.mp member with past | fresh
  · obtain ⟨token, content, receipt⟩ := history.clean message past owner
    refine Or.inl ⟨token, content, ?_⟩
    apply (app.receipt_policyInvariant players (message.id, true)).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 6 _ final _ reached
    rw [app.respond_receipts]
    exact receipt
  · exact Or.inr (List.mem_singleton.mp fresh)

/-- The actual terminal utility has a uniform bound, suitable for arbitrary
beliefs over final native decision histories. -/
theorem payoff_bounded (reward forfeit : ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ)
    (state : app.ProtocolState) :
    |LateOpeningRuntimeNash.payoff reward forfeit sample deposit state bob| ≤
      1 + |forfeit| + |deposit bob| := by
  have base : |nativeBaseUtility reward forfeit state bob| ≤ 1 + |forfeit| := by
    change |(serviceSourceReadout setup .sequential deadline leaks state).elim 0
      (fun terminal => sourceUtility reward forfeit terminal bob)| ≤ _
    cases read : serviceSourceReadout setup .sequential deadline leaks state with
    | none => simp only [Option.elim_none, abs_zero]; positivity
    | some terminal =>
        change State simpleExpr program.terminalCtx at terminal
        simp only [Option.elim_some]
        rw [sourceUtility_bob]
        have gross := bob_gross_bounds reward (setup.parameterOutcome parameter terminal)
        calc
          _ ≤ |grossUtility reward (setup.parameterOutcome parameter terminal) bob| +
              |if (terminal.get bobPublication).isSuccess then 0 else forfeit| := abs_sub _ _
          _ ≤ 1 + |forfeit| := by
            rw [abs_of_nonneg gross.1]
            split
            · rw [abs_zero]
              linarith [abs_nonneg forfeit]
            · linarith
  have charged := TerminalAudit.charge_mem_Icc
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks sample) state bob
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
  calc
    _ ≤ |nativeBaseUtility reward forfeit state bob| +
        |TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
          (serviceSourceAudit setup .sequential deadline leaks sample) state bob * deposit bob| :=
      abs_sub _ _
    _ ≤ 1 + |forfeit| + |deposit bob| := by
      rw [abs_mul, abs_of_nonneg charged.1]
      nlinarith [charged.2, abs_nonneg (deposit bob)]

/-- Canonical final opening weakly dominates every raw response. A failed
publication loses at least the entire forfeit, since its gross payoff is zero
and a successful immutable answer has nonnegative gross payoff. -/
theorem canonical_dominates (history : DecisionHistory weight nonnegative)
    (reward forfeit : ℝ) (forfeitNonnegative : 0 ≤ forfeit)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit bob)
    (response : app.Action) (players future : Player → app.Policy)
    (final canonicalFinal : app.Execution)
    (reached : final ∈ (continuation weight nonnegative history response players).support)
    (canonicalReached : canonicalFinal ∈
      (continuation weight nonnegative history
        (canonical weight nonnegative history) future).support) :
    LateOpeningRuntimeNash.payoff reward forfeit sample deposit (app.finished final) bob ≤
      LateOpeningRuntimeNash.payoff reward forfeit sample deposit
        (app.finished canonicalFinal) bob ∧
    (final.application.config.store (.inr bobRevealEvent) = some .failure →
      LateOpeningRuntimeNash.payoff reward forfeit sample deposit
        (app.finished final) bob + forfeit ≤
        LateOpeningRuntimeNash.payoff reward forfeit sample deposit
          (app.finished canonicalFinal) bob) := by
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
    ⟨6, some bob, history.execution⟩ history.trace
  obtain ⟨aliceResult, aliceStored⟩ := Option.isSome_iff_exists.mp
    (bob_prefix_other_field_available history.execution.application history.ready
      (.inr aliceEvent) (by decide))
  obtain ⟨rawResult, rawStored, rawRead⟩ := continuation_readout weight nonnegative
    history.execution history.trace history.answer history.bound history.ready bit label valid
    aliceResult aliceStored response players final reached
  obtain ⟨canonicalResult, canonicalStored, canonicalRead⟩ := continuation_readout
    weight nonnegative history.execution history.trace history.answer history.bound history.ready
    bit label valid aliceResult aliceStored
    (canonical weight nonnegative history)
      future canonicalFinal canonicalReached
  obtain ⟨published, clear⟩ := canonical_clean weight nonnegative history sample authentic
    future canonicalFinal canonicalReached
  have canonicalEqual : canonicalResult = .success history.answer :=
    Option.some.inj (canonicalStored.symm.trans published)
  subst canonicalResult
  have charged := TerminalAudit.charge_mem_Icc
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks sample) (app.finished final) bob
  have deduction := mul_nonneg charged.1 depositNonnegative
  have canonicalValue : LateOpeningRuntimeNash.payoff reward forfeit sample deposit
      (app.finished canonicalFinal) bob =
      grossUtility reward (setup.parameterOutcome parameter
        (terminalStateOf bit label aliceResult (.success history.answer)
          (.success history.answer))) bob := by
    unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
    rw [nativeBaseUtility_of_readout reward forfeit _ _ canonicalRead bob, clear, zero_mul,
      sub_zero, sourceUtility_bob]
    change _ - 0 = _
    exact sub_zero _
  have canonicalNonnegative : 0 ≤ LateOpeningRuntimeNash.payoff reward forfeit sample deposit
      (app.finished canonicalFinal) bob := by
    rw [canonicalValue]
    exact (bob_gross_bounds _ _).1
  have failedBound (failed : final.application.config.store (.inr bobRevealEvent) = some .failure) :
      LateOpeningRuntimeNash.payoff reward forfeit sample deposit (app.finished final) bob ≤
        -forfeit := by
    have equal : rawResult = .failure := Option.some.inj (rawStored.symm.trans failed)
    subst rawResult
    unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
    rw [nativeBaseUtility_of_readout reward forfeit _ _ rawRead bob, sourceUtility_bob_failure]
    exact sub_le_self _ deduction
  refine ⟨?_, fun failed => by linarith [failedBound failed]⟩
  cases rawResult with
  | failure => linarith [failedBound rawStored]
  | success opened =>
      have immutable := bob_continuation_success_immutable LateOpeningRuntimeService.runtime
        leaks players (LateOpeningRuntimeService.scheduler weight nonnegative) 6
        history.execution final _ valid history.answer history.bound response reached
          opened rawStored
      subst opened
      unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
      rw [nativeBaseUtility_of_readout reward forfeit _ _ rawRead bob,
        nativeBaseUtility_of_readout reward forfeit _ _ canonicalRead bob,
        clear, zero_mul, sub_zero]
      exact sub_le_self _ deduction

/-- Under any belief over the specified actual final histories, the gain
from canonical opening is at least the forfeit times the raw continuation's
failure probability. Response lotteries may even depend on the hidden history;
an information-feasible response is a special case. -/
theorem canonical_regret (reward forfeit : ℝ) (forfeitNonnegative : 0 ≤ forfeit)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit bob)
    (belief : PMF (DecisionHistory weight nonnegative))
    (responses : DecisionHistory weight nonnegative → PMF app.Action)
    (players future : DecisionHistory weight nonnegative → Player → app.Policy) :
    forfeit * ((belief.bind fun history => (responses history).bind fun response =>
      continuation weight nonnegative history response (players history)).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal ≤
    expect (belief.bind fun history => continuation weight nonnegative history
      (canonical weight nonnegative history) (future history))
      (fun final => LateOpeningRuntimeNash.payoff reward forfeit sample deposit
        (app.finished final) bob) -
    expect (belief.bind fun history => (responses history).bind fun response =>
      continuation weight nonnegative history response (players history))
      (fun final => LateOpeningRuntimeNash.payoff reward forfeit sample deposit
        (app.finished final) bob) := by
  classical
  let payoff : app.Execution → ℝ := fun final =>
    LateOpeningRuntimeNash.payoff reward forfeit sample deposit (app.finished final) bob
  let failure : Set app.Execution :=
    {final | final.application.config.store (.inr bobRevealEvent) = some .failure}
  let raw := fun history => (responses history).bind fun response =>
    continuation weight nonnegative history response (players history)
  let comparator := fun history => continuation weight nonnegative history
    (canonical weight nonnegative history) (future history)
  have integrable (law : PMF app.Execution) : PayoffIntegrable law payoff :=
    payoffIntegrable_of_bounded _ _ fun final =>
      payoff_bounded reward forfeit sample deposit (app.finished final)
  apply expect_failure_regret belief raw comparator payoff payoff failure forfeit
    (integrable _) (integrable _) (fun history _ => integrable (raw history))
    (fun history _ => integrable (comparator history))
  intro history _ final reached canonicalFinal canonicalReached
  obtain ⟨response, _, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have comparison := canonical_dominates weight nonnegative history reward forfeit
    forfeitNonnegative sample authentic deposit depositNonnegative response
    (players history) (future history) final canonicalFinal continued canonicalReached
  by_cases failed : final ∈ failure
  · simpa only [failed, ite_true, mul_one, payoff] using comparison.2 failed
  · simpa only [failed, ite_false, mul_zero, add_zero, payoff] using comparison.1

end Vegas.Examples.LateOpeningRuntimeBobIncentive
