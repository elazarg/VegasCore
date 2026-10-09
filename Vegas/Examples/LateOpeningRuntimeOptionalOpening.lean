/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobSafeContinuation
import Vegas.Examples.LateOpeningRuntimeBobIncentive
import Vegas.Examples.LateOpeningRuntimeBobInformation

/-! # Clean complete publication from the optional receiver callback

An actual ready timely optional callback can publish the immutable selected
answer immediately, then stay silent. This complete native continuation has
zero receiver audit charge on every physical branch. The initial binding's
private representation is unrestricted; its existing clean public traffic is
the relevant premise. This supplies an attainable deviation, not an equilibrium
normalization or a new service interface.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeOptionalOpening

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeBobService LateOpeningRuntimeBobAudit LateOpeningRuntimeBobSafeContinuation
  LateOpeningRuntimeUtility

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

structure DecisionHistory where
  execution : app.Execution
  trace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨12, some bob, execution⟩)
  answer : Answer
  bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer)
  ready : execution.application.config.cut.Ready bobRevealEvent
  timely : execution.application.WithinDeadline
    LateOpeningRuntimeService.runtime bobRevealEvent
  clean : CleanBindings execution

/-- The immediate opening belongs to the unchanged bounded native menu. -/
theorem canonical_available
    (history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History)
    (decision : DecisionHistory weight nonnegative)
    (current : history.state = some ⟨12, some bob, decision.execution⟩) :
    LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
      (decision.execution.recall bob) (decision.execution.observe app bob) bobRevealEvent true ∈
        rawMenu.actions bob (decision.execution.recall bob) (decision.execution.observe app bob) :=
  LateOpeningRuntimeBobResponseMenu.opening_available weight nonnegative
    LateOpeningRuntimeBobInformation.output_values_covered ⟨12, some bob, decision.execution⟩
      (current ▸ history.trace) rfl

/-- The comparator is the real canonical current response followed by the
existing whole answer policy, which stays silent at the later callback. -/
theorem canonical_continuation_clean (decision : DecisionHistory weight nonnegative)
    (players : Player → app.Policy) (bobPolicy : players bob = answerPolicy decision.answer)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    ∃ candidate material,
      LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
        (decision.execution.recall bob) (decision.execution.observe app bob) bobRevealEvent true =
          ⟨some material⟩ ∧
      ∀ final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        players 12 (decision.execution.respond app bob ⟨some material⟩)).support,
        final.application.config.store (.inr bobRevealEvent) = some (.success decision.answer) ∧
        ((openingMessage decision.execution candidate decision.answer).id, true) ∈ final.receipts ∧
        TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
          (serviceSourceAudit setup .sequential deadline leaks sample) (app.finished final) bob =
            0 := by
  obtain ⟨candidate, material, opened, canonical, emitted, law, published, accepted⟩ :=
    canonical_round weight nonnegative players 12 decision.execution decision.trace
      decision.answer decision.bound decision.ready decision.timely
  refine ⟨candidate, material, canonical, ?_⟩
  intro final reached
  have whole := reached
  obtain ⟨first, firstReached, suffix⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  rw [law, PMF.mem_support_pure_iff] at firstReached
  subst first
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 12 decision.execution bob
      ⟨some material⟩ decision.trace
  obtain ⟨openedTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 11 _ opened respondedTrace
      (by rw [law]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have late : 15 ≤ opened.environmentRecall.length := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) openedTrace
    change opened.environmentRecall.length + 11 = 26 at counted
    omega
  have inputs := after_opening_inputs weight nonnegative decision.answer players bobPolicy
    11 0 opened final openedTrace late suffix
  have openingInputs : opened.network.inputs = decision.execution.network.inputs ++
      [(show Message Player app.Payload from
        openingMessage decision.execution candidate decision.answer)] := by
    have firstSupported : opened ∈ (app.round
        (LateOpeningRuntimeService.scheduler weight nonnegative) players
        (decision.execution.respond app bob ⟨some material⟩)).support := by
      rw [law]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
    have preserved : opened.network.inputs =
        (decision.execution.respond app bob ⟨some material⟩).network.inputs := by
      obtain ⟨command, selected, dispatched⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ firstSupported)
      have serviceChoice := protected_response_scheduler weight nonnegative
        ⟨12, some bob, decision.execution⟩ decision.trace bob rfl ⟨some material⟩ (Or.inl rfl)
      rw [serviceChoice, PMF.mem_support_pure_iff] at selected
      subst command
      obtain ⟨middle, supported, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      have passive := (latestAuthor_passive bob
        ((decision.execution.respond app bob ⟨some material⟩).observeEnvironment app)).1
      rw [passive] at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      exact app.environmentStep_inputs _ _ _ supported
    rw [preserved]
    change (decision.execution.network.submit bob
      (app.packet (app.submit decision.execution.application bob material) bob
        (decision.execution.network.known bob) material)).2.inputs = _
    rw [emitted]
    rfl
  have finalPublished := (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr bobRevealEvent)
      (.success decision.answer)) players).runRounds
        (LateOpeningRuntimeService.scheduler weight nonnegative) 11 opened final published suffix
  have finalAccepted := (app.receipt_policyInvariant players
    ((openingMessage decision.execution candidate decision.answer).id, true)).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 11 opened final accepted suffix
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 12 _ final
      respondedTrace whole
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨0, none, final⟩ finalTrace
  have finalBound := bob_success_from_binding final.application _ valid.reachable decision.answer
    finalPublished
  refine ⟨finalPublished, finalAccepted, charge_zero weight nonnegative ⟨0, none, final⟩
    finalTrace decision.answer finalBound decision.execution candidate finalAccepted ?_
      sample authentic⟩
  intro message member owner
  rw [inputs, openingInputs, List.mem_append, List.mem_singleton] at member
  rcases member with old | same
  · obtain ⟨token, content, receipt⟩ := decision.clean message old owner
    exact Or.inl ⟨token, content, (app.receipt_policyInvariant players (message.id, true)).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 12
      (decision.execution.respond app bob ⟨some material⟩) final receipt whole⟩
  · exact Or.inr same

/-- Successful complete disclosure has nonnegative gross value and no
deduction, for any reward, forfeit or deposit signs. -/
theorem canonical_payoff_nonnegative (decision : DecisionHistory weight nonnegative)
    (players : Player → app.Policy) (bobPolicy : players bob = answerPolicy decision.answer)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 12 (decision.execution.respond app bob
        (LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
          (decision.execution.recall bob) (decision.execution.observe app bob)
            bobRevealEvent true))).support) :
    0 ≤ LateOpeningRuntimeNash.payoff reward forfeit sample deposit (app.finished final) bob := by
  obtain ⟨candidate, material, canonical, clean⟩ := canonical_continuation_clean weight nonnegative
    decision players bobPolicy sample authentic
  rw [canonical] at reached
  obtain ⟨published, _accepted, clear⟩ := clean final reached
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 12 decision.execution bob
      ⟨some material⟩ decision.trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 12 _ final respondedTrace
      reached
  have completed := (contract weight nonnegative).completes ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨0, none, final⟩ finalTrace
  have bound := bob_success_from_binding final.application _ valid.reachable decision.answer
    published
  obtain ⟨aliceResult, aliceStored⟩ := Option.isSome_iff_exists.mp
    (final.application.config.store_available_of_terminal completed (.inr aliceEvent))
  have decoded := decode_terminalStateOf final.application bit label aliceResult
    (.success decision.answer) (.success decision.answer) valid.reachable.inputs_eq
      aliceStored bound published
  have readout : serviceSourceReadout setup .sequential deadline leaks (app.finished final) =
      some (terminalStateOf bit label aliceResult (.success decision.answer)
        (.success decision.answer)) := by
    unfold serviceSourceReadout
    change (if final.application.config.cut.Terminal then
      decodeState? (terminalRefs program) final.application.config.store else none) = _
    rw [ite_eq_left completed]
    exact decoded
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
  rw [clear, zero_mul, sub_zero, nativeBaseUtility_of_readout reward forfeit _ _ readout bob,
    sourceUtility_bob]
  have success : ((terminalStateOf bit label aliceResult (.success decision.answer)
      (.success decision.answer)).get bobPublication).isSuccess = true := rfl
  rw [ite_eq_left success, sub_zero]
  exact (bob_gross_bounds reward _).1

end Vegas.Examples.LateOpeningRuntimeOptionalOpening
