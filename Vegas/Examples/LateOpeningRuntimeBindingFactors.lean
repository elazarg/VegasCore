/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBindingObservation

/-! # Exact native receiver branch probabilities

The original all-identifier lottery and the fair pending sample give these
laws of Bob's complete current observation and remembered early response.
An opening already learned at the earlier callback is retained without an
additional disclosure factor. Private sender submission aliases remain in
the physical executions and disappear only under the actual Bob projection.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBindingFactors

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLateAcceptance LateOpeningRuntimeLatePrefixKernel
  LateOpeningRuntimeLateResponseKernel LateOpeningRuntimeBindingObservation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- Erasing Alice's private recall preserves the full original lottery and
the actual receiver observation kernel, including every pending identifier. -/
theorem settlement_information_eq (first second : app.Execution)
    (same : first.eraseRecall app alice = second.eraseRecall app alice) :
    (settlementKernel weight nonnegative first).map bobInformation =
      (settlementKernel weight nonnegative second).map bobInformation := by
  have pending := congrArg (fun execution : app.Execution => execution.network.pending) same
  change first.network.pending = second.network.pending at pending
  unfold settlementKernel
  rw [PMF.map_bind, PMF.map_bind, pending]
  apply bind_congr_on_support
  intro selected _
  exact branch_information_eq first second same selected

theorem canonical_information_law (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (settlementKernel weight nonnegative (beforeLottery bit label slot seen)).map bobInformation =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure (bobInformation (answerDecision bit label slot seen)))
        (mix (1 / 2) (by norm_num) (by norm_num)
          (PMF.pure (bobInformation (failedAnswerDecision bit label slot seen true)))
          (PMF.pure (bobInformation (failedAnswerDecision bit label slot seen false)))) := by
  unfold settlementKernel
  rw [beforeLottery_pending]
  change ((MessageNetwork.chooseWithOutside weight nonnegative {(alice, 0)}).bind
    (branchLaw (beforeLottery bit label slot seen))).map bobInformation = _
  rw [MessageNetwork.chooseWithOutside]
  simp only [Finset.card_singleton]
  rw [MessageNetwork.chooseUniform_singleton, mix_bind, PMF.pure_bind, PMF.pure_bind,
    mix_map, included_information_law, omitted_information_law]

/-- When the first sample already disclosed the opening, the omitted branch
is one actual information record, regardless of the later fair sample. -/
theorem canonical_seen_information_law (bit : Bool) (label : Fin 3) :
    (settlementKernel weight nonnegative (beforeLottery bit label 0 true)).map bobInformation =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure (bobInformation (answerDecision bit label 0 true)))
        (PMF.pure (bobInformation (failedAnswerDecision bit label 0 true false))) := by
  unfold settlementKernel
  rw [beforeLottery_pending]
  change ((MessageNetwork.chooseWithOutside weight nonnegative {(alice, 0)}).bind
    (branchLaw (beforeLottery bit label 0 true))).map bobInformation = _
  rw [MessageNetwork.chooseWithOutside]
  simp only [Finset.card_singleton]
  rw [MessageNetwork.chooseUniform_singleton, mix_bind, PMF.pure_bind, PMF.pure_bind,
    mix_map, included_information_law, omitted_seen_information_law]

theorem genuine_first_information_law (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) (seen : Bool) :
    (settlementKernel weight nonnegative
      ((finalDecision bit label ⟨some submission⟩
        (if seen then {(alice, 0)} else ∅)).respond app alice ⟨none⟩)).map bobInformation =
      (settlementKernel weight nonnegative (beforeLottery bit label 0 seen)).map
        bobInformation :=
  settlement_information_eq weight nonnegative _ _
    (genuine_retry_erased weight nonnegative bit label submission genuine seen)

theorem genuine_final_information_law (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceOpeningContinuation.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label)
        submission) :
    (settlementKernel weight nonnegative
      ((finalDecision bit label ⟨none⟩ ∅).respond app alice ⟨some submission⟩)).map bobInformation =
      (settlementKernel weight nonnegative (beforeLottery bit label 1 false)).map
        bobInformation :=
  settlement_information_eq weight nonnegative _ _
    (genuine_final_erased weight nonnegative bit label submission genuine)

private theorem success_ne_failure (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool) :
    bobInformation (answerDecision bit label slot earlySeen) ≠
      bobInformation (failedAnswerDecision bit label slot earlySeen finalSeen) := by
  intro same
  have receipts := congrArg (fun information : BobInformation => information.2.receipts) same
  change (acceptedLottery bit label slot earlySeen).receipts =
    (failedAnswerDecision bit label slot earlySeen finalSeen).receipts at receipts
  rw [acceptedLottery_receipts_eq, failedAnswerDecision_receipts] at receipts
  contradiction

private theorem unseen_disclosure_ne_empty (bit : Bool) (label : Fin 3) (slot : Fin 2) :
    bobInformation (failedAnswerDecision bit label slot false true) ≠
      bobInformation (failedAnswerDecision bit label slot false false) := by
  intro same
  have leaked := congrArg (fun information : BobInformation =>
    information.2.messages.leaked) same
  change ((failedAnswerDecision bit label slot false true).network.observe bob).leaked =
    ((failedAnswerDecision bit label slot false false).network.observe bob).leaked at leaked
  rw [failedAnswerDecision_network, failedAnswerDecision_network] at leaked
  simp at leaked

/-- The retained-seen failure atom has probability exactly one minus inclusion;
there is no second factor of one half. -/
theorem seen_failure_probability (bit : Bool) (label : Fin 3) :
    (((settlementKernel weight nonnegative (beforeLottery bit label 0 true)).map
      bobInformation) (bobInformation (failedAnswerDecision bit label 0 true false))).toReal =
        1 - inclusionProbability weight := by
  rw [canonical_seen_information_law, mix_apply_toReal]
  simp [PMF.pure_apply, (success_ne_failure bit label 0 true false).symm]

theorem unseen_disclosure_failure_probability (bit : Bool) (label : Fin 3) (slot : Fin 2) :
    (((settlementKernel weight nonnegative (beforeLottery bit label slot false)).map
      bobInformation) (bobInformation (failedAnswerDecision bit label slot false true))).toReal =
        (1 - inclusionProbability weight) / 2 := by
  rw [canonical_information_law, mix_apply_toReal, mix_apply_toReal]
  simp [PMF.pure_apply, (success_ne_failure bit label slot false true).symm,
    unseen_disclosure_ne_empty]
  ring

theorem unseen_empty_failure_probability (bit : Bool) (label : Fin 3) (slot : Fin 2) :
    (((settlementKernel weight nonnegative (beforeLottery bit label slot false)).map
      bobInformation) (bobInformation (failedAnswerDecision bit label slot false false))).toReal =
        (1 - inclusionProbability weight) / 2 := by
  rw [canonical_information_law, mix_apply_toReal, mix_apply_toReal]
  simp [PMF.pure_apply, (success_ne_failure bit label slot false false).symm,
    (unseen_disclosure_ne_empty bit label slot).symm]
  ring

theorem unseen_success_probability (bit : Bool) (label : Fin 3) (slot : Fin 2) :
    (((settlementKernel weight nonnegative (beforeLottery bit label slot false)).map
      bobInformation) (bobInformation (answerDecision bit label slot false))).toReal =
        inclusionProbability weight := by
  rw [canonical_information_law, mix_apply_toReal, mix_apply_toReal]
  simp [PMF.pure_apply, success_ne_failure]

end Vegas.Examples.LateOpeningRuntimeBindingFactors
