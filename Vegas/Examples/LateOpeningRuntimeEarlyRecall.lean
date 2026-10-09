/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBindingFactors

/-! # Irreversible early receiver recall before the binding callback

The remaining lottery, clock, expiry and activation preserve the receiver's
exact remembered early response. Arbitrary final sender packets can change
current traffic and public settlement, but cannot manufacture an earlier
receiver observation of an opening.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeEarlyRecall

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLatePrefixKernel LateOpeningRuntimeLateResponseKernel
  LateOpeningRuntimeBindingObservation LateOpeningRuntimeBobBindingService

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private theorem lottery_recall (execution : app.Execution)
    (selected : Option (MessageId Player)) :
    (lotteryOutcome execution selected).recall bob = execution.recall bob := by
  cases selected with
  | none => rfl
  | some identifier =>
      simp only [lotteryOutcome, ReactiveApplication.Execution.includePending,
        MessageNetwork.includePending]
      cases execution.network.lookup identifier <;> rfl

theorem settlement_recall (execution final : app.Execution)
    (reached : final ∈ (settlementKernel weight nonnegative execution).support) :
    final.recall bob = execution.recall bob := by
  obtain ⟨selected, _, continued⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  obtain ⟨before, expired, activated⟩ := (PMF.mem_support_bind_iff _ _ _).mp continued
  have last := congrFun (app.environmentStep_recall before final (.activate bob) activated) bob
  have middle := congrFun (app.environmentStep_recall
    (clocked (lotteryOutcome execution selected)) before
      (.application (.expire aliceEvent)) expired) bob
  exact last.trans (middle.trans (lottery_recall execution selected))

theorem final_response_recall (bit : Bool) (label : Fin 3) (response : app.Action)
    (selected : Finset (MessageId Player)) (players : Player → app.Policy)
    (final : app.Execution)
    (reached : final ∈
      (finalResponseLaw weight nonnegative bit label response selected players).support) :
    final.recall bob = (earlyQuiet bit label response selected).recall bob := by
  obtain ⟨lastResponse, _, settled⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  have preserved := settlement_recall weight nonnegative _ final settled
  rw [app.respond_recall_other _ alice bob (by decide)] at preserved
  exact preserved

def EarlyObservedOpening (bit : Bool) (execution : app.Execution) : Prop :=
  ∃ entry ∈ execution.recall bob, openingMessage bit ∈ entry.beforeView.messages.leaked

private theorem empty_early_not_observed (bit : Bool) (label : Fin 3)
    (response : app.Action) (otherBit : Bool) :
    ¬ EarlyObservedOpening otherBit (earlyQuiet bit label response ∅) := by
  rintro ⟨entry, member, observed⟩
  change entry ∈ [_] at member
  cases List.mem_singleton.mp member
  rcases response with ⟨transmission⟩
  cases transmission <;> change openingMessage otherBit ∈ [] at observed <;> cases observed

theorem empty_early_observed_event_zero (bit : Bool) (label : Fin 3) (response : app.Action)
    (otherBit : Bool) (players : Player → app.Policy) (event : Set app.Execution)
    (observed : ∀ final ∈ event, EarlyObservedOpening otherBit final) :
    (finalResponseLaw weight nonnegative bit label response ∅ players).toOuterMeasure event =
      0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro final reached member
  have preserved := final_response_recall weight nonnegative bit label response ∅
    players final reached
  have retained := observed final member
  change ∃ entry ∈ final.recall bob, openingMessage otherBit ∈ entry.beforeView.messages.leaked
    at retained
  rw [preserved] at retained
  exact empty_early_not_observed bit label response otherBit retained

theorem first_silent_observed_event_zero (bit : Bool) (label : Fin 3)
    (otherBit : Bool) (players : Player → app.Policy) (event : Set app.Execution)
    (quiet : ∀ final ∈ event, SilentRecall final)
    (observed : ∀ final ∈ event, EarlyObservedOpening otherBit final) :
    ((firstBindingLaw weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        ⟨none⟩ players).toOuterMeasure event).toReal = 0 := by
  rw [silent_first_silent_event_probability weight nonnegative bit label players _ quiet]
  rw [empty_early_observed_event_zero weight nonnegative bit label ⟨none⟩
    otherBit players event observed, ENNReal.toReal_zero, mul_zero]

end Vegas.Examples.LateOpeningRuntimeEarlyRecall
