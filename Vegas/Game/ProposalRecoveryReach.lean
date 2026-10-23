/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryHybridInformation
import GameTheoryExtensions.Analysis.Protocol.SingleMoverReach

/-! # Original chance factors and full enriched counterfactual reach -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Cross multiplication compares policies on the SAME actual source path.
It does not identify their action laws or divide by an own-play probability. -/
theorem proposalRecovery_counterfactual_cross_factor [Fintype Player]
    (strategy : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (reference : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (focal : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    setup.proposalRecoveryModel.counterfactualReachProbability strategy focal trace *
        (∏ who ∈ Finset.univ.erase focal,
          setup.commitRecoveryModel.playerReachProbability reference who
            (setup.proposalRecoveryEraseTrace trace)) =
      setup.commitRecoveryModel.counterfactualReachProbability reference focal
          (setup.proposalRecoveryEraseTrace trace) *
        (∏ who ∈ Finset.univ.erase focal,
          setup.proposalRecoveryModel.playerReachProbability strategy who trace) := by
  classical
  induction trace with
  | start => simp only [proposalRecoveryEraseTrace,
      InformationModel.counterfactualReachProbability_start,
      InformationModel.playerReachProbability_start, Finset.prod_const_one, mul_one]
  | @extend source target prior joint legal supported ih =>
      let oldJoint : {chosen // setup.commitRecoveryProtocol.Legal source chosen} :=
        ⟨proposalRecoveryJoint joint,
        setup.proposalRecovery_erase_legal joint legal⟩
      have oldProduct :
          (∏ who ∈ Finset.univ.erase focal,
            setup.commitRecoveryModel.playerReachProbability reference who
              (setup.proposalRecoveryEraseTrace (prior.extend joint legal supported))) =
          (∏ who ∈ Finset.univ.erase focal,
            setup.commitRecoveryModel.playerReachProbability reference who
              (setup.proposalRecoveryEraseTrace prior)) *
            setup.commitRecoveryModel.opponentsStepProb reference focal
              (setup.proposalRecoveryEraseTrace prior) oldJoint := by
        simp only [proposalRecoveryEraseTrace, InformationModel.playerReachProbability,
          Finset.prod_mul_distrib, InformationModel.opponentsStepProb,
          InformationModel.playerStepProb, oldJoint]
      have newProduct :
          (∏ who ∈ Finset.univ.erase focal,
            setup.proposalRecoveryModel.playerReachProbability strategy who
              (prior.extend joint legal supported)) =
          (∏ who ∈ Finset.univ.erase focal,
            setup.proposalRecoveryModel.playerReachProbability strategy who prior) *
            setup.proposalRecoveryModel.opponentsStepProb strategy focal prior ⟨joint, legal⟩ := by
        simp only [InformationModel.playerReachProbability, Finset.prod_mul_distrib,
          InformationModel.opponentsStepProb, InformationModel.playerStepProb]
      rw [oldProduct, newProduct, InformationModel.counterfactualReachProbability]
      change _ = (setup.commitRecoveryModel.counterfactualReachProbability reference focal
        (setup.proposalRecoveryEraseTrace prior) *
        setup.commitRecoveryModel.counterfactualStepProb reference focal
          (setup.proposalRecoveryEraseTrace prior) oldJoint target) * _
      let newReach := setup.proposalRecoveryModel.counterfactualReachProbability
        strategy focal prior
      let oldReach := setup.commitRecoveryModel.counterfactualReachProbability
        reference focal (setup.proposalRecoveryEraseTrace prior)
      let newOwn := ∏ who ∈ Finset.univ.erase focal,
        setup.proposalRecoveryModel.playerReachProbability strategy who prior
      let oldOwn := ∏ who ∈ Finset.univ.erase focal,
        setup.commitRecoveryModel.playerReachProbability reference who
          (setup.proposalRecoveryEraseTrace prior)
      let newStep := setup.proposalRecoveryModel.opponentsStepProb strategy focal prior
        ⟨joint, legal⟩
      let oldStep := setup.commitRecoveryModel.opponentsStepProb reference focal
        (setup.proposalRecoveryEraseTrace prior) oldJoint
      let chance := ((setup.commitRecoveryProtocol.step source oldJoint) target).toReal
      change newReach * oldOwn = oldReach * newOwn at ih
      change (newReach * (newStep * chance)) * (oldOwn * oldStep) =
        (oldReach * (oldStep * chance)) * (newOwn * newStep)
      calc
        _ = (newReach * oldOwn) * (newStep * oldStep * chance) := by ring
        _ = (oldReach * newOwn) * (newStep * oldStep * chance) :=
          congrArg (fun coefficient => coefficient * (newStep * oldStep * chance)) ih
        _ = _ := by ring


/-- Full enriched opponent information supplies every opponent response
factor; the old fully mixed reference cancels only a strictly positive product. -/
theorem proposalRecovery_counterfactual_reach_eq_of_reference [Fintype Player]
    (strategy : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (reference : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (mixed : ∀ who (site : setup.commitRecoveryModel.InformationSite who) choice,
      choice ∈ (reference who site.1).support) (focal : Player)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (information : ∀ who, who ≠ focal →
      setup.proposalRecoveryModel.infoOf who left = setup.proposalRecoveryModel.infoOf who right)
    (chance : setup.commitRecoveryModel.counterfactualReachProbability reference focal
        (setup.proposalRecoveryEraseTrace left) =
      setup.commitRecoveryModel.counterfactualReachProbability reference focal
        (setup.proposalRecoveryEraseTrace right)) :
    setup.proposalRecoveryModel.counterfactualReachProbability strategy focal left =
      setup.proposalRecoveryModel.counterfactualReachProbability strategy focal right := by
  classical
  have newOwn who (foreign : who ≠ focal) :
      setup.proposalRecoveryModel.playerReachProbability strategy who left =
        setup.proposalRecoveryModel.playerReachProbability strategy who right := by
    rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability,
      InformationModel.playerReachProbability_eq_ownPlayReachProbability]
    exact congrArg _ (setup.proposalRecoveryModel_perfectRecall who _ _
      (information who foreign))
  have oldOwn who (foreign : who ≠ focal) :
      setup.commitRecoveryModel.playerReachProbability reference who
          (setup.proposalRecoveryEraseTrace left) =
        setup.commitRecoveryModel.playerReachProbability reference who
          (setup.proposalRecoveryEraseTrace right) := by
    have erased := congrArg (setup.proposalRecoveryEraseInfo who) (information who foreign)
    rw [setup.proposalRecoveryEraseInfo_observed,
      setup.proposalRecoveryEraseInfo_observed] at erased
    rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability,
      InformationModel.playerReachProbability_eq_ownPlayReachProbability]
    exact congrArg _ (setup.commitRecoveryModel_perfectRecall who _ _ erased)
  have newProduct :
      (∏ who ∈ Finset.univ.erase focal,
        setup.proposalRecoveryModel.playerReachProbability strategy who left) =
        ∏ who ∈ Finset.univ.erase focal,
          setup.proposalRecoveryModel.playerReachProbability strategy who right := by
    exact Finset.prod_congr rfl fun who member => newOwn who (Finset.ne_of_mem_erase member)
  have oldProduct :
      (∏ who ∈ Finset.univ.erase focal,
        setup.commitRecoveryModel.playerReachProbability reference who
          (setup.proposalRecoveryEraseTrace left)) =
        ∏ who ∈ Finset.univ.erase focal,
          setup.commitRecoveryModel.playerReachProbability reference who
            (setup.proposalRecoveryEraseTrace right) := by
    exact Finset.prod_congr rfl fun who member => oldOwn who (Finset.ne_of_mem_erase member)
  have positive : 0 < ∏ who ∈ Finset.univ.erase focal,
      setup.commitRecoveryModel.playerReachProbability reference who
        (setup.proposalRecoveryEraseTrace right) := by
    exact Finset.prod_pos fun who _ => setup.commitRecoveryModel.playerReachProbability_pos
      reference mixed who (setup.proposalRecoveryEraseTrace right)
  have leftFactor := setup.proposalRecovery_counterfactual_cross_factor
    strategy reference focal left
  have rightFactor := setup.proposalRecovery_counterfactual_cross_factor
    strategy reference focal right
  rw [oldProduct, chance, newProduct] at leftFactor
  exact mul_right_cancel₀ (ne_of_gt positive) (leftFactor.trans rightFactor.symm)

end Vegas.SourceProgram.Setup
