/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.LogicalCommitment
import GameTheoryExtensions.Math.Probability.DecisionObservation

/-! # Information erasure at one logical settlement decision

These finite decision experiments use the logical binding's opened/quit result.
They do not instantiate the pending-message runtime. The positive example has
an outcome kernel independent of erased metadata, even though the policy may
depend on that metadata. The negative example keeps one fixed settlement rule
but erases an observation relevant to its result. It separates attainable
utilities, not merely the representation of an operational transition.
-/

noncomputable section

namespace InteractionTests.LogicalCommitmentInformation

open Interaction GameTheory.Math.Probability

private def metadata : FinDist (Fin 2) := FinDist.uniformFin 2

private def forget (_ : Fin 2) : Unit := ()

private def binding : LogicalCommitment Unit Unit := ⟨(), id⟩

private def fixedBinding : LogicalCommitment.State Unit Unit Unit :=
  (LogicalCommitment.State.empty.prepare binding () () ()).recordInclusion
    binding (.select () ())

private def voluntarySettlement (publish : Bool) :
    FinDist (LogicalCommitment.Result Unit) :=
  FinDist.pure
    ((if publish then fixedBinding.recordInclusion binding (.open () () ())
      else fixedBinding.settleQuit binding ()).result)

private theorem voluntarySettlement_eq (publish : Bool) :
    voluntarySettlement publish = FinDist.pure (if publish then .opened () else .quit) := by
  cases publish <;> rfl

/-- Arbitrary responses to erased metadata can be randomized at the logical
view when the fixed continuation depends only on the retained view and action.
The same settlement rule is used for every native and logical policy. -/
theorem erased_metadata_policy_law (nativePolicy : Fin 2 → FinDist Bool) :
    ∃ logicalPolicy : Unit → FinDist Bool,
      metadata.bind (fun native => (nativePolicy native).bind voluntarySettlement) =
        (metadata.map forget).bind
          (fun observed => (logicalPolicy observed).bind voluntarySettlement) := by
  exact ⟨metadata.conditionedPolicy forget nativePolicy,
    metadata.bind_policy_logicalKernel_eq_bind_conditionedPolicy forget nativePolicy
      (fun _ => voluntarySettlement)⟩

private def metadataResponse (native : Fin 2) : FinDist Bool :=
  FinDist.pure (native == 0)

/-- The positive example genuinely permits different native commands on one
logical information fiber; pointwise policy constancy is unnecessary. -/
theorem metadata_response_distinguishes_erased_inputs :
    forget 0 = forget 1 ∧ metadataResponse 0 ≠ metadataResponse 1 := by
  refine ⟨rfl, ?_⟩
  intro heq
  change FinDist.pure true = FinDist.pure false at heq
  have hprob := congrArg (fun law : FinDist Bool => law.prob true) heq
  norm_num [FinDist.prob_pure_eq_ite] at hprob

private def phaseSettlement (phase action : Fin 2) :
    FinDist (LogicalCommitment.Result Unit) :=
  voluntarySettlement (decide (action = phase))

private def settlementUtility : LogicalCommitment.Result Unit → ℝ
  | .opened _ => 1
  | .pending | .quit => 0

private def informedResult : FinDist (LogicalCommitment.Result Unit) :=
  metadata.bind (fun phase => (FinDist.pure phase).bind (phaseSettlement phase))

private def blindResult (policy : Unit → FinDist (Fin 2)) :
    FinDist (LogicalCommitment.Result Unit) :=
  metadata.bind (fun phase => (policy (forget phase)).bind (phaseSettlement phase))

/-- Observing the phase permits an action whose settlement opens with certainty. -/
theorem informed_settlement_value : informedResult.expect settlementUtility = 1 := by
  simp [informedResult, phaseSettlement, voluntarySettlement_eq, settlementUtility]

/-- Every randomized policy on the erased observation succeeds with probability
one half. The policy cannot correlate its private draw with the hidden phase. -/
theorem blind_settlement_value (policy : Unit → FinDist (Fin 2)) :
    (blindResult policy).expect settlementUtility = 1 / 2 := by
  unfold blindResult forget
  rw [FinDist.bind_comm, FinDist.expect_bind]
  calc
    _ = (policy ()).expect (fun _ => (1 / 2 : ℝ)) := by
      apply FinDist.expect_congr
      intro action _
      rw [FinDist.expect_bind]
      simp only [phaseSettlement, voluntarySettlement_eq, FinDist.expect_pure]
      unfold metadata
      rw [FinDist.expect_uniformFin]
      fin_cases action <;> norm_num [Fin.sum_univ_succ, settlementUtility]
    _ = 1 / 2 := FinDist.expect_const _ _

/-- Erasing a settlement-relevant observation can strictly reduce attainable
utility under the very same fixed environment rule. This is a counterexample
to unrestricted information erasure, not to the candidate-runtime compiler. -/
theorem erased_phase_strict_value_gap (policy : Unit → FinDist (Fin 2)) :
    (blindResult policy).expect settlementUtility <
      informedResult.expect settlementUtility := by
  rw [blind_settlement_value, informed_settlement_value]
  norm_num

/-- No randomized policy on the erased view reproduces this informed result law. -/
theorem no_blind_settlement_law :
    ¬ ∃ policy : Unit → FinDist (Fin 2), blindResult policy = informedResult := by
  rintro ⟨policy, heq⟩
  have hgap := erased_phase_strict_value_gap policy
  rw [heq] at hgap
  exact (lt_irrefl _) hgap

end InteractionTests.LogicalCommitmentInformation

/-- info: 'InteractionTests.LogicalCommitmentInformation.erased_metadata_policy_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractionTests.LogicalCommitmentInformation.erased_metadata_policy_law

/-- info: 'InteractionTests.LogicalCommitmentInformation.no_blind_settlement_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractionTests.LogicalCommitmentInformation.no_blind_settlement_law
