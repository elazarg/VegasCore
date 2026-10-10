/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobDirtyPayoff
import Vegas.Examples.LateOpeningRuntimeBobBindingFiber

/-! # Attained receiver answer scores on full native information fibers

Every compatible legal history admits the actual whole answer policy's fresh
binding and disclosure. The score formula includes the receiver's prior sunk
audit deduction and does not restrict histories to positive posterior belief.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobDirtyAttainment

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobBindingService
  LateOpeningRuntimeBobDirtyPrefix LateOpeningRuntimeBobDirtyPayoff
  LateOpeningRuntimeBobFreshBinding
  LateOpeningRuntimeBobBindingInformation LateOpeningRuntimeBobSuccessPayoff

/-- The actual whole answer policy attains the same sunk-charge score formula
throughout the complete legal information fiber, without a belief-support guard. -/
theorem dirty_information_answer_attainment (weight : ℝ) (nonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
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
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (reward forfeit : ℝ) (deposit : Player → ℝ) (answer : Answer) :
    ∃ (other : app.Execution) (serial : Nat),
      history.1.state = some ⟨14, some bob, other⟩ ∧
      LateOpeningRuntimeBobSafeContinuation.answerPolicy answer
        (other.recall bob) (other.observe app bob) = PMF.pure (response serial answer) ∧
      ∀ (players : Player → app.Policy),
        players bob = LateOpeningRuntimeBobSafeContinuation.answerPolicy answer →
        ∀ final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          players 14 (other.respond app bob (response serial answer))).support,
          LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
            deposit (some ⟨0, none, final⟩) bob =
              answerScore (originalLabel other) answer - deposit bob := by
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
  exact dirty_fresh_answer_payoff weight nonnegative reward forfeit deposit other otherTrace
    otherReady otherTimely otherDirty bit otherPublished answer serial fresh players bobPolicy
      final reached

end Vegas.Examples.LateOpeningRuntimeBobDirtyAttainment
