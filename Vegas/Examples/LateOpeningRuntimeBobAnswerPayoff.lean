/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingInformation
import Vegas.Examples.LateOpeningRuntimeBobSafeContinuation

/-! # Exact clean answer payoffs after Alice's failed publication

The selected commitment and its complete opening policy retain the actual
immutable source inputs. Successful settlement removes Bob's source forfeit,
and accepted canonical traffic has zero audit charge. After Alice's failure,
the resulting native payoff is exactly the indicator of a correct bit guess.
The bit read below is used to describe hidden-history payoffs, never to choose
the runtime policy's action.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobAnswerPayoff

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeUtility LateOpeningRuntimeBobBindingInformation
  LateOpeningRuntimeBobSafeContinuation

/-- The immutable initialized bit of a hidden physical history. -/
def originalBit (execution : app.Execution) : Bool :=
  match aliceBinding.get? execution.application.config.store with
  | some (.success bit) => bit
  | _ => false

theorem originalBit_initialized (execution : app.Execution) (bit : Bool) (label : Fin 3)
    (valid : EventGraphRuntime.State.Invariant (graph := nativeGraph)
      (setup.eventInputs (sourceInitial bit label)) execution.application) :
    originalBit execution = bit := by
  unfold originalBit
  change (match some (execution.application.config.inputs aliceInput) with
    | some (.success stored) => stored
    | _ => false) = bit
  rw [valid.reachable.inputs_eq]
  rfl

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- The complete selected-answer continuation has its actual success payoff,
without a posterior premise or a restriction on Alice's future responses. -/
theorem failed_answer_continuation_payoff
    (decision : DecisionHistory weight nonnegative) (answer : Answer)
    (players : Player → app.Policy) (bobPolicy : players bob = answerPolicy answer)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14
        (decision.execution.respond app bob
          (LateOpeningRuntimeBobSuffix.binding answer))).support) :
    LateOpeningRuntimeNash.payoff reward forfeit sample deposit (app.finished final) bob =
      if answer.val = (if originalBit decision.execution then 5 else 4) then 1 else 0 := by
  obtain ⟨published, clear⟩ := answer_continuation_clean weight nonnegative answer players
    bobPolicy decision.execution final decision.trace decision.quiet decision.ready decision.timely
      sample authentic reached
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨14, some bob, decision.execution⟩ decision.trace
  have bitEq := originalBit_initialized decision.execution bit label valid
  have invariant := LateOpeningRuntimeService.runtime.reactiveStateInvariant leaks
    (setup.eventInputs (sourceInitial bit label))
  have finalValid := (ReactiveApplication.Invariant.policyInvariant app invariant players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (invariant.respond decision.execution bob (LateOpeningRuntimeBobSuffix.binding answer) valid)
        reached
  have failedInvariant := LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks
    (.inr aliceEvent) (.failure : PublicationResult Bool)
  have finalFailed := (ReactiveApplication.Invariant.policyInvariant app failedInvariant
    players).runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (failedInvariant.respond decision.execution bob (LateOpeningRuntimeBobSuffix.binding answer)
        decision.failed) reached
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 decision.execution bob
      (LateOpeningRuntimeBobSuffix.binding answer) decision.trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 14 _ final respondedTrace
      reached
  have completed := (contract weight nonnegative).completes ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
  have bound := bob_success_from_binding final.application _ finalValid.reachable answer published
  have decoded := decode_terminalStateOf final.application bit label .failure (.success answer)
    (.success answer) finalValid.reachable.inputs_eq finalFailed bound published
  have readout : serviceSourceReadout setup .sequential deadline leaks (app.finished final) =
      some (terminalStateOf bit label .failure (.success answer) (.success answer)) := by
    unfold serviceSourceReadout
    change (if final.application.config.cut.Terminal then
      decodeState? (terminalRefs program) final.application.config.store else none) = _
    rw [ite_eq_left completed]
    exact decoded
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
  rw [clear, zero_mul, sub_zero, nativeBaseUtility_of_readout reward forfeit _ _ readout bob,
    sourceUtility_bob_after_alice_failure, bitEq]

end Vegas.Examples.LateOpeningRuntimeBobAnswerPayoff
