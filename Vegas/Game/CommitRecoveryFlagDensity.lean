/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryFlagWordSwap

/-! # Original source counterfactual likelihood under private-word substitution

The untouched setup/chance prefix is literal. Every later transition inside
the original commitment window has mass one, including the final real close.
The opponent's full original records determine all remaining reach factors.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem commit_step_mass_one (current : CommitRecoveryState setup.program)
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal (some current) joint)
    (target : setup.commitRecoveryProtocol.State)
    (supported : target ∈ (setup.commitRecoveryProtocol.step (some current)
      ⟨joint, legal⟩).support) :
    (setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩) target = 1 := by
  change target ∈ ((current.step joint).map some).support at supported
  obtain ⟨next, nextSupport, rfl⟩ :=
    (PMF.mem_support_map_iff some (current.step joint) _).mp supported
  apply (PMF.apply_eq_one_iff _ _).mpr
  ext result
  constructor
  · intro member
    change result ∈ ((current.step joint).map some).support at member
    obtain ⟨other, otherSupport, rfl⟩ :=
      (PMF.mem_support_map_iff some (current.step joint) _).mp member
    exact Set.mem_singleton_iff.mpr (congrArg some
      (current.step_unique_of_commit committing joint other next otherSupport nextSupport))
  · intro equal
    rw [Set.mem_singleton_iff] at equal
    subst result
    exact (PMF.mem_support_map_iff some (current.step joint) _).mpr ⟨next, nextSupport, rfl⟩

variable [Fintype Player]

/-- Exact counterfactual source likelihood is invariant under replacing a
focal commitment word, including its accepted-failure bits, at the SAME
original entry and omission tables. No chance factor or opponent old word
is dropped or restarted. -/
theorem commitRecoveryNormalizedFlagPolicy_counterfactual_reach_eq
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (strategy : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (firstMemory secondMemory : (who : Player) →
      setup.CommitRecoveryFlagDraw finite who × setup.CommitRecoveryDomainDraw finite who)
    (flags : ∀ who, (fun clock => ((firstMemory who).1 clock).1) =
      (fun clock => ((secondMemory who).1 clock).1))
    (otherMemory : ∀ who, who ≠ focal → firstMemory who = secondMemory who)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix prior leftTrace) (rightRetained : TracePrefix prior rightTrace)
    (leftConsistent : ∀ who,
      setup.commitRecoveryNormalizedFlagPolicy finite who (firstMemory who) ∈
        setup.commitRecoveryModel.Consistent who (setup.commitRecoveryModel.ownPlay who leftTrace))
    (rightConsistent : ∀ who,
      setup.commitRecoveryNormalizedFlagPolicy finite who (secondMemory who) ∈
        setup.commitRecoveryModel.Consistent who (setup.commitRecoveryModel.ownPlay who rightTrace))
    (clock : leftTrace.length = rightTrace.length)
    (within : leftTrace.length + ProtocolState.commitEnd setup.program first.point ≤
      prior.length + ProtocolState.remaining setup.program first.point) :
    setup.commitRecoveryModel.counterfactualReachProbability strategy focal leftTrace =
      setup.commitRecoveryModel.counterfactualReachProbability strategy focal rightTrace := by
  classical
  induction leftRetained generalizing rightState with
  | refl =>
      have equal := rightRetained.eq_of_length clock
      cases equal
      rfl
  | @extend source target earlier kept joint legal reached ih =>
      cases rightRetained with
      | refl =>
          have lower := kept.length_le
          simp only [Trace.length] at clock
          omega
      | @extend rightSource rightTarget rightEarlier rightKept rightJoint rightLegal rightReached =>
          have previousClock : earlier.length = rightEarlier.length := by
            simpa only [Trace.length, Nat.add_left_inj] using clock
          have previousInside : earlier.length +
              ProtocolState.commitEnd setup.program first.point <
              prior.length + ProtocolState.remaining setup.program first.point := by
            simp only [Trace.length] at within
            omega
          have leftBefore who := setup.commitRecoveryModel.consistent_subset_of_isSuffix
            (setup.commitRecoveryModel.ownPlay_isSuffix_of_reachesWithin who
              (TracePrefix.extend .refl joint legal reached).reachesWithin) (leftConsistent who)
          have rightBefore who := setup.commitRecoveryModel.consistent_subset_of_isSuffix
            (setup.commitRecoveryModel.ownPlay_isSuffix_of_reachesWithin who
              (TracePrefix.extend .refl rightJoint rightLegal rightReached).reachesWithin)
            (rightConsistent who)
          have previous := ih rightEarlier rightKept leftBefore rightBefore previousClock
            previousInside.le
          have before := setup.commitRecoveryNormalizedFlagPolicy_nonfocal_info_eq finite focal
            first prior committing firstMemory secondMemory flags otherMemory earlier rightEarlier
            kept rightKept leftBefore rightBefore previousClock previousInside.le
          obtain ⟨left, rfl, leftCommit, _leftEnd, _leftRank⟩ :=
            setup.commitRecovery_prefix_inside_commit first prior committing earlier kept
              previousInside
          obtain ⟨right, rfl, rightCommit, _rightEnd, _rightRank⟩ :=
            setup.commitRecovery_prefix_inside_commit first prior committing rightEarlier rightKept
              (by omega)
          have leftJoint := setup.recorded_joint
            (fun who => setup.commitRecoveryNormalizedFlagPolicy finite who (firstMemory who))
            earlier joint legal reached leftConsistent
          have rightJointEq := setup.recorded_joint
            (fun who => setup.commitRecoveryNormalizedFlagPolicy finite who (secondMemory who))
            rightEarlier rightJoint rightLegal rightReached rightConsistent
          have leftMass := setup.commit_step_mass_one left leftCommit joint legal _ reached
          have rightMass := setup.commit_step_mass_one right rightCommit rightJoint rightLegal _
            rightReached
          have stepEqual : setup.commitRecoveryModel.counterfactualStepProb strategy focal earlier
                ⟨joint, legal⟩ target =
              setup.commitRecoveryModel.counterfactualStepProb strategy focal rightEarlier
                ⟨rightJoint, rightLegal⟩ rightState := by
            unfold InformationModel.counterfactualStepProb
            rw [leftMass, rightMass]
            simp only [ENNReal.toReal_one, mul_one]
            unfold InformationModel.opponentsStepProb
            apply Finset.prod_congr rfl
            intro who member
            have nonfocal := (Finset.mem_erase.mp member).1
            have sameInfo := before who nonfocal
            have ownChoice : joint who = rightJoint who := by
              calc
                joint who = (setup.commitRecoveryNormalizedFlagPolicy finite who
                    (firstMemory who) (setup.commitRecoveryModel.infoOf who earlier)).val :=
                  congrFun leftJoint who
                _ = (setup.commitRecoveryNormalizedFlagPolicy finite who
                    (secondMemory who) (setup.commitRecoveryModel.infoOf who earlier)).val :=
                  congrArg (fun memory => (setup.commitRecoveryNormalizedFlagPolicy finite who
                    memory (setup.commitRecoveryModel.infoOf who earlier)).val)
                      (otherMemory who nonfocal)
                _ = (setup.commitRecoveryNormalizedFlagPolicy finite who
                    (secondMemory who) (setup.commitRecoveryModel.infoOf who rightEarlier)).val :=
                  congrArg (fun info => (setup.commitRecoveryNormalizedFlagPolicy finite who
                    (secondMemory who) info).val) sameInfo
                _ = rightJoint who := (congrFun rightJointEq who).symm
            have leftRaw := pmf_map_apply_of_injective
              (f := fun choice : setup.commitRecoveryModel.Choice who
                (setup.commitRecoveryModel.infoOf who earlier) => choice.val)
              (strategy who (setup.commitRecoveryModel.infoOf who earlier)) Subtype.val_injective
              (setup.commitRecoveryModel.choicesOfLegal earlier ⟨joint, legal⟩ who)
            have rightRaw := pmf_map_apply_of_injective
              (f := fun choice : setup.commitRecoveryModel.Choice who
                (setup.commitRecoveryModel.infoOf who rightEarlier) => choice.val)
              (strategy who (setup.commitRecoveryModel.infoOf who rightEarlier))
              Subtype.val_injective
              (setup.commitRecoveryModel.choicesOfLegal rightEarlier ⟨rightJoint, rightLegal⟩ who)
            have rawLaw := congrArg (fun info => (strategy who info).map Subtype.val) sameInfo
            apply congrArg ENNReal.toReal
            rw [← leftRaw, ← rightRaw]
            change ((strategy who (setup.commitRecoveryModel.infoOf who earlier)).map Subtype.val)
                (joint who) =
              ((strategy who (setup.commitRecoveryModel.infoOf who rightEarlier)).map Subtype.val)
                (rightJoint who)
            rw [rawLaw, ownChoice]
          change setup.commitRecoveryModel.counterfactualReachProbability strategy focal earlier *
              setup.commitRecoveryModel.counterfactualStepProb strategy focal earlier
                ⟨joint, legal⟩ target =
            setup.commitRecoveryModel.counterfactualReachProbability strategy focal rightEarlier *
              setup.commitRecoveryModel.counterfactualStepProb strategy focal rightEarlier
                ⟨rightJoint, rightLegal⟩ rightState
          rw [previous, stepEqual]

/-- The two actual full-history densities differ only by their original
focal own-record likelihoods, with no positivity or supplied density factor.
This is the division-free identity needed before Bayes normalization. -/
theorem commitRecoveryNormalizedFlagPolicy_reach_cross_mul_eq
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (strategy : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (firstMemory secondMemory : (who : Player) →
      setup.CommitRecoveryFlagDraw finite who × setup.CommitRecoveryDomainDraw finite who)
    (flags : ∀ who, (fun clock => ((firstMemory who).1 clock).1) =
      (fun clock => ((secondMemory who).1 clock).1))
    (otherMemory : ∀ who, who ≠ focal → firstMemory who = secondMemory who)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix prior leftTrace) (rightRetained : TracePrefix prior rightTrace)
    (leftConsistent : ∀ who,
      setup.commitRecoveryNormalizedFlagPolicy finite who (firstMemory who) ∈
        setup.commitRecoveryModel.Consistent who (setup.commitRecoveryModel.ownPlay who leftTrace))
    (rightConsistent : ∀ who,
      setup.commitRecoveryNormalizedFlagPolicy finite who (secondMemory who) ∈
        setup.commitRecoveryModel.Consistent who (setup.commitRecoveryModel.ownPlay who rightTrace))
    (clock : leftTrace.length = rightTrace.length)
    (within : leftTrace.length + ProtocolState.commitEnd setup.program first.point ≤
      prior.length + ProtocolState.remaining setup.program first.point) :
    (setup.commitRecoveryModel.historyReachWeight strategy ⟨leftState, leftTrace⟩).toReal *
        setup.commitRecoveryModel.playerReachProbability strategy focal rightTrace =
      (setup.commitRecoveryModel.historyReachWeight strategy ⟨rightState, rightTrace⟩).toReal *
        setup.commitRecoveryModel.playerReachProbability strategy focal leftTrace := by
  have counterfactual := setup.commitRecoveryNormalizedFlagPolicy_counterfactual_reach_eq finite
    strategy focal first prior committing firstMemory secondMemory flags otherMemory leftTrace
    rightTrace leftRetained rightRetained leftConsistent rightConsistent clock within
  rw [setup.commitRecoveryModel.historyReachProbability_eq_player_mul_counterfactual,
    setup.commitRecoveryModel.historyReachProbability_eq_player_mul_counterfactual,
    counterfactual]
  ring

end Vegas.SourceProgram.Setup
