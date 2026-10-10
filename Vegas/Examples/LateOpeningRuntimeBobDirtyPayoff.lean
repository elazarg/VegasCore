/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobDirtyPrefix
import Vegas.Examples.LateOpeningRuntimeBobSuccessPayoff
import Vegas.Examples.LateOpeningRuntimeBobFreshContinuation

/-! # Attained answer scores after a sunk native receiver charge

Fresh native bindings and subsequent openings attain the selected answer's
logical score, less the prior full receiver audit deduction. Earlier sender
publication and subsequent sender behavior are unrestricted beyond the stated
successful-publication hypothesis.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobDirtyPayoff

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobBindingService
  LateOpeningRuntimeBobDirtyPrefix

/-- A genuine fresh-answer continuation attains its logical score after the
fixed sunk charge, with arbitrary further sender behavior. -/
theorem dirty_fresh_answer_payoff (weight : ℝ) (nonnegative : 0 ≤ weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ) (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (dirty : ¬ SilentRecall execution) (bit : Bool)
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
    LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit (some ⟨0, none, final⟩) bob =
        LateOpeningRuntimeBobSuccessPayoff.answerScore
          (LateOpeningRuntimeBobSuccessPayoff.originalLabel execution) answer - deposit bob := by
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
    (.inr aliceEvent) (.success bit : PublicationResult Bool)
  have aliceAfter := (ReactiveApplication.Invariant.policyInvariant app publicationInvariant
    players).runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (publicationInvariant.respond execution bob _ published) reached
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
        originalBit label (.success bit) (.success answer) (.success answer)) := by
    change (if final.application.config.cut.Terminal then
      decodeState? (terminalRefs program) final.application.config.store else none) = _
    rw [ite_eq_left complete]
    exact LateOpeningRuntimeReadout.decode_terminalStateOf final.application originalBit label
      (.success bit) (.success answer) (.success answer) after.reachable.inputs_eq aliceAfter
        answerBound answerPublished
  rw [dirty_binding_payoff_eq_base_sub_deposit weight nonnegative reward forfeit deposit
    execution trace ready dirty _ players final reached,
    LateOpeningRuntimeUtility.nativeBaseUtility_of_readout reward forfeit _ _ decoded bob,
    LateOpeningRuntimeBobSuccessPayoff.sourceUtility_bob_after_alice_success]
  rw [LateOpeningRuntimeBobSuccessPayoff.originalLabel_initialized execution originalBit label
    valid]
end Vegas.Examples.LateOpeningRuntimeBobDirtyPayoff
