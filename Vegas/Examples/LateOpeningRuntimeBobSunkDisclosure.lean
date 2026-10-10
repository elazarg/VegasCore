/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobIncentive
import Vegas.Examples.LateOpeningRuntimeBobSunkAudit

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeBobSunkDisclosure
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeBobService LateOpeningRuntimeBobAudit LateOpeningRuntimeUtility
open LateOpeningRuntimeBobIncentive (continuation_readout)
variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- Canonical opening succeeds while retaining the same sunk terminal audit charge,
under arbitrary future raw policies and full evidence. -/
theorem canonical_dominates (remaining : Nat) (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨(remaining + 1), some bob, execution⟩))
    (answer : Answer)
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobRevealEvent)
    (serial : Nat) (rejected : ((bob, serial), false) ∈ execution.receipts)
    (reward forfeit : ℝ) (forfeitNonnegative : 0 ≤ forfeit) (deposit : Player → ℝ)
    (response : app.Action) (players future : Player → app.Policy)
    (final canonicalFinal : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players (remaining + 1)
      (execution.respond app bob response)).support)
    (canonicalReached : canonicalFinal ∈ (app.runRounds (LateOpeningRuntimeService.scheduler
      weight nonnegative) future (remaining + 1)
      (execution.respond app bob
        (LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob (execution.recall bob)
          (execution.observe app bob) bobRevealEvent true))).support) :
    LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual) deposit
        (app.finished final) bob ≤
      LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual) deposit
        (app.finished canonicalFinal) bob ∧
    (final.application.config.store (.inr bobRevealEvent) = some .failure →
      LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual) deposit
          (app.finished final) bob + forfeit ≤
        LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual) deposit
          (app.finished canonicalFinal) bob) := by
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) ⟨(remaining + 1), some bob,
      execution⟩ trace
  obtain ⟨aliceResult, aliceStored⟩ := Option.isSome_iff_exists.mp
    (bob_prefix_other_field_available execution.application ready (.inr aliceEvent) (by decide))
  change PublicationResult Bool at aliceResult
  obtain ⟨rawResult, rawStored, rawRead⟩ := continuation_readout weight nonnegative
    (remaining + 1) execution trace
    answer bound ready bit label valid aliceResult aliceStored response players final reached
  change PublicationResult Answer at rawResult
  let canonical := LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
    (execution.recall bob)
    (execution.observe app bob) bobRevealEvent true
  obtain ⟨canonicalResult, canonicalStored, canonicalRead⟩ :=
    continuation_readout weight nonnegative (remaining + 1)
    execution trace answer bound ready bit label valid aliceResult aliceStored canonical future
      canonicalFinal canonicalReached
  obtain ⟨candidate, material, first, decision, _emitted, moved, published, _accepted⟩ :=
    canonical_round weight nonnegative future (remaining + 1) execution trace answer
      bound ready timely
  have canonicalResponse : canonical = ⟨some material⟩ := decision
  have canonicalReached' : canonicalFinal ∈
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) future (remaining + 1)
        (execution.respond app bob canonical)).support := canonicalReached
  rw [canonicalResponse, ReactiveApplication.runRounds] at canonicalReached'
  obtain ⟨next, firstReached, suffix⟩ := Set.mem_iUnion₂.mp
    (PMF.support_bind .. ▸ canonicalReached')
  rw [moved, PMF.mem_support_pure_iff] at firstReached
  subst next
  have published := (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr bobRevealEvent)
      (.success answer)) future).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) remaining first canonicalFinal
    published suffix
  have canonicalEqual : canonicalResult = .success answer :=
    Option.some.inj (canonicalStored.symm.trans published)
  subst canonicalResult
  have rawCharge := LateOpeningRuntimeBobSunkAudit.rejected_identifier_continuation_full_charge
    weight nonnegative (remaining + 1) execution trace serial rejected response players
      final reached
  have canonicalCharge :=
    LateOpeningRuntimeBobSunkAudit.rejected_identifier_continuation_full_charge weight nonnegative
      (remaining + 1) execution trace serial rejected canonical future canonicalFinal
        canonicalReached
  change TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
      (app.finished final) bob = 1 at rawCharge
  change TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
      (app.finished canonicalFinal) bob = 1 at canonicalCharge
  have canonicalValue : LateOpeningRuntimeNash.payoff reward forfeit
      (fun actual => PMF.pure actual) deposit (app.finished canonicalFinal) bob =
      grossUtility reward (setup.parameterOutcome parameter
        (terminalStateOf bit label aliceResult (.success answer) (.success answer))) bob -
        deposit bob := by
    unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
    rw [nativeBaseUtility_of_readout reward forfeit _ _ canonicalRead bob, canonicalCharge,
      one_mul, sourceUtility_bob]
    change _ - 0 - _ = _
    rw [sub_zero]
  have grossNonnegative := (bob_gross_bounds reward (setup.parameterOutcome parameter
    (terminalStateOf bit label aliceResult (.success answer) (.success answer)))).1
  have failedValue (failed : final.application.config.store (.inr bobRevealEvent) = some .failure) :
      LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual) deposit
        (app.finished final) bob = -forfeit - deposit bob := by
    have equal : rawResult = .failure := Option.some.inj (rawStored.symm.trans failed)
    subst rawResult
    unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
    rw [nativeBaseUtility_of_readout reward forfeit _ _ rawRead bob, sourceUtility_bob_failure,
      rawCharge, one_mul]
  refine ⟨?_, fun failed => by rw [failedValue failed, canonicalValue]; linarith⟩
  cases rawResult with
  | failure => rw [failedValue rawStored, canonicalValue]; linarith
  | success opened =>
      have immutable := bob_continuation_success_immutable LateOpeningRuntimeService.runtime leaks
        players
        (LateOpeningRuntimeService.scheduler weight nonnegative) (remaining + 1)
          execution final _ valid answer
          bound response reached
          opened rawStored
      subst opened
      unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
      rw [nativeBaseUtility_of_readout reward forfeit _ _ rawRead bob,
        nativeBaseUtility_of_readout reward forfeit _ _ canonicalRead bob,
        rawCharge, canonicalCharge]
end Vegas.Examples.LateOpeningRuntimeBobSunkDisclosure
