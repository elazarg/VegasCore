/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeOptionalOpening

/-! # Complete optional-publication payoff and audit comparison

Immediate canonical disclosure followed by the existing quiet answer policy
attains the immutable answer's entire gross score at each hidden history.
Every raw current response and arbitrary future raw policy is below that
score by its actual audit deduction and, on publication failure, its forfeit.
The comparison retains initialized private inputs and the full native suffix.
It does not assume rationality, a posterior, or a restricted response menu.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeOptionalIncentive

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeBobService LateOpeningRuntimeBobAudit LateOpeningRuntimeUtility
  LateOpeningRuntimeBobSafeContinuation LateOpeningRuntimeOptionalOpening

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def continuation (history : DecisionHistory weight nonnegative) (response : app.Action)
    (players : Player → app.Policy) : PMF app.Execution :=
  app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 12
    (history.execution.respond app bob response)

def canonical (history : DecisionHistory weight nonnegative) : app.Action :=
  LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
    (history.execution.recall bob) (history.execution.observe app bob) bobRevealEvent true

theorem canonical_clean (history : DecisionHistory weight nonnegative)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (players : Player → app.Policy) (bobPolicy : players bob = answerPolicy history.answer)
    (final : app.Execution)
    (reached : final ∈ (continuation weight nonnegative history
      (canonical weight nonnegative history) players).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success history.answer) ∧
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks sample)
          (app.finished final) bob = 0 := by
  obtain ⟨candidate, material, selected, settled⟩ := canonical_continuation_clean weight nonnegative
    history players bobPolicy sample authentic
  change final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 12 (history.execution.respond app bob
      (LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
        (history.execution.recall bob) (history.execution.observe app bob)
          bobRevealEvent true))).support at reached
  rw [selected] at reached
  obtain ⟨published, _accepted, clear⟩ := settled final reached
  exact ⟨published, clear⟩

/-- The attainable gross ceiling is the same at every physical branch from
this hidden history. Arbitrary foreign traffic does not affect the comparator. -/
theorem canonical_payoff_eq_gross (history : DecisionHistory weight nonnegative)
    (bit : Bool) (label : Fin 3)
    (valid : EventGraphRuntime.State.Invariant (graph := nativeGraph)
      (setup.eventInputs (sourceInitial bit label)) history.execution.application)
    (aliceResult : PublicationResult Bool)
    (aliceStored : history.execution.application.config.store (.inr aliceEvent) = some aliceResult)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (players : Player → app.Policy) (bobPolicy : players bob = answerPolicy history.answer)
    (final : app.Execution)
    (reached : final ∈ (continuation weight nonnegative history
      (canonical weight nonnegative history) players).support) :
    LateOpeningRuntimeNash.payoff reward forfeit sample deposit (app.finished final) bob =
      grossUtility reward (setup.parameterOutcome parameter
        (terminalStateOf bit label aliceResult (.success history.answer)
          (.success history.answer))) bob := by
  obtain ⟨result, stored, readout⟩ :=
    LateOpeningRuntimeBobIncentive.continuation_readout weight nonnegative 12
    history.execution history.trace history.answer history.bound history.ready bit label
    valid aliceResult aliceStored (canonical weight nonnegative history) players final reached
  obtain ⟨published, clear⟩ := canonical_clean weight nonnegative history sample authentic players
    bobPolicy final reached
  have equal : result = .success history.answer := Option.some.inj (stored.symm.trans published)
  subst result
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
  rw [nativeBaseUtility_of_readout reward forfeit _ _ readout bob, clear, zero_mul,
    sub_zero, sourceUtility_bob]
  change _ - 0 = _
  exact sub_zero _

open Classical in
/-- The actual audit deduction is included in the pointwise regret bound.
No sign restriction on reward, forfeit or collateral is needed for this bound. -/
theorem canonical_audit_regret (history : DecisionHistory weight nonnegative)
    (reward forfeit : ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (response : app.Action) (players future : Player → app.Policy)
    (bobPolicy : future bob = answerPolicy history.answer)
    (final canonicalFinal : app.Execution)
    (reached : final ∈ (continuation weight nonnegative history response players).support)
    (canonicalReached : canonicalFinal ∈ (continuation weight nonnegative history
      (canonical weight nonnegative history) future).support) :
    LateOpeningRuntimeNash.payoff reward forfeit sample deposit (app.finished final) bob +
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks sample) (app.finished final) bob *
          deposit bob +
      (if final.application.config.store (.inr bobRevealEvent) = some .failure
        then forfeit else 0) ≤
      LateOpeningRuntimeNash.payoff reward forfeit sample deposit
        (app.finished canonicalFinal) bob := by
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨12, some bob, history.execution⟩ history.trace
  obtain ⟨aliceResult, aliceStored⟩ := Option.isSome_iff_exists.mp
    (bob_prefix_other_field_available history.execution.application history.ready
      (.inr aliceEvent) (by decide))
  obtain ⟨result, stored, readout⟩ :=
    LateOpeningRuntimeBobIncentive.continuation_readout weight nonnegative 12
    history.execution history.trace history.answer history.bound history.ready bit label
    valid aliceResult aliceStored response players final reached
  have comparator := canonical_payoff_eq_gross weight nonnegative history bit label valid
    aliceResult aliceStored reward forfeit deposit sample authentic future bobPolicy
      canonicalFinal canonicalReached
  rw [comparator]
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
  rw [nativeBaseUtility_of_readout reward forfeit _ _ readout bob]
  cases result with
  | failure =>
      rw [stored, ite_eq_left rfl, sourceUtility_bob_failure]
      have gross := (bob_gross_bounds reward (setup.parameterOutcome parameter
        (terminalStateOf bit label aliceResult (.success history.answer)
          (.success history.answer)))).1
      linarith
  | success answer =>
      have immutable := bob_continuation_success_immutable LateOpeningRuntimeService.runtime
        leaks players (LateOpeningRuntimeService.scheduler weight nonnegative) 12
        history.execution final _ valid history.answer history.bound response reached answer stored
      subst answer
      rw [stored, ite_eq_right (by intro wrong; cases wrong), sourceUtility_bob]
      change _ - 0 - _ + _ + 0 ≤ _
      linarith

end Vegas.Examples.LateOpeningRuntimeOptionalIncentive
