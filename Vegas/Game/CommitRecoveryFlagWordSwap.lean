/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryFlagCoupling
import Vegas.Source.CommitRecoveryPrivateWordSwap
import GameTheory.Analysis.Protocol.CounterfactualReach

/-! # Original opponent trajectories during private source-word substitution

Both histories retain the SAME original entry history, original opponent
tables and occurrence flags. Changing the focal domain table preserves every
other owner's FULL source information through the actual commitment close.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem current_signal (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.commitRecoveryModel.infoOf who trace).1.1 =
      (setup.commitRecoveryPrivate who state, setup.commitRecoveryPublic state) := by
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who trace).1.1 = _
  rw [InfoSignals.withOwnPlayRecall_infoOf]
  exact setup.commitRecoverySignals_current who trace

private theorem information_extend_congr (who : Player)
    {leftSource leftTarget rightSource rightTarget : setup.commitRecoveryProtocol.State}
    (left : setup.commitRecoveryProtocol.Trace leftSource)
    (right : setup.commitRecoveryProtocol.Trace rightSource)
    (leftJoint rightJoint : Player → Option (CommitRecoveryMove Player L))
    (leftLegal : setup.commitRecoveryProtocol.Legal leftSource leftJoint)
    (rightLegal : setup.commitRecoveryProtocol.Legal rightSource rightJoint)
    (leftSupport : leftTarget ∈
      (setup.commitRecoveryProtocol.step leftSource ⟨leftJoint, leftLegal⟩).support)
    (rightSupport : rightTarget ∈
      (setup.commitRecoveryProtocol.step rightSource ⟨rightJoint, rightLegal⟩).support)
    (before : setup.commitRecoveryModel.infoOf who left =
      setup.commitRecoveryModel.infoOf who right)
    (ownChoice : leftJoint who = rightJoint who)
    (signal : (setup.commitRecoveryPrivate who leftTarget,
        setup.commitRecoveryPublic leftTarget) =
      (setup.commitRecoveryPrivate who rightTarget, setup.commitRecoveryPublic rightTarget)) :
    setup.commitRecoveryModel.infoOf who (left.extend leftJoint leftLegal leftSupport) =
      setup.commitRecoveryModel.infoOf who (right.extend rightJoint rightLegal rightSupport) := by
  change setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _ =
    setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _
  change setup.commitRecoverySignals.withOwnPlayRecall.infoOf who left =
    setup.commitRecoverySignals.withOwnPlayRecall.infoOf who right at before
  rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf] at before ⊢
  have base := congrArg Prod.fst before
  have record := congrArg Prod.snd before
  dsimp only at base record
  apply Prod.ext
  · rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend]
    change ((setup.commitRecoveryPrivate who leftTarget,
      setup.commitRecoveryPublic leftTarget), _) =
      ((setup.commitRecoveryPrivate who rightTarget, setup.commitRecoveryPublic rightTarget), _)
    rw [signal, base]
  · rw [InfoSignals.ownPlay_extend, InfoSignals.ownPlay_extend, ownChoice]
    cases rightJoint who with
    | none => exact record
    | some action => exact congrArg₂ List.cons (congrArg (fun info => (info, action)) base) record

variable [Fintype Player]

/-- Changing one owner's original domain table within an actual commitment
window preserves every OTHER owner's entire original source information.
All private inputs and chance outcomes are those of the literal SAME prior;
there is no replacement entry distribution or supplied observation equality. -/
theorem commitRecoveryNormalizedFlagPolicy_nonfocal_info_eq
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
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
    ∀ who, who ≠ focal → setup.commitRecoveryModel.infoOf who leftTrace =
      setup.commitRecoveryModel.infoOf who rightTrace := by
  induction leftRetained generalizing rightState with
  | refl =>
      have equal := rightRetained.eq_of_length clock
      cases equal
      exact fun _ _ => rfl
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
          have before := ih rightEarlier rightKept leftBefore rightBefore previousClock
            previousInside.le
          have previous := setup.commitRecoveryNormalizedFlagPolicy_omissionRecall_eq finite focal
            first prior committing firstMemory secondMemory flags earlier rightEarlier kept
            rightKept leftBefore rightBefore previousClock previousInside.le
          obtain ⟨left, right, rfl, rfl, leftSaved, rightSaved, leftEntry, rightEntry,
            leftGeneration, rightGeneration, excluded, observed, _publicPast⟩ :=
              setup.inside_attempt_public_eq focal first prior committing earlier rightEarlier
                kept rightKept previous previousInside
          obtain ⟨middle, middleState, middleCommit, _middleEnd, _middleRank⟩ :=
            setup.commitRecovery_prefix_inside_commit first prior committing earlier kept
              previousInside
          have middleEq := Option.some.inj middleState
          subst middle
          obtain ⟨other, otherState, otherCommit, _otherEnd, _otherRank⟩ :=
            setup.commitRecovery_prefix_inside_commit first prior committing rightEarlier rightKept
              (by omega)
          have otherEq := Option.some.inj otherState
          subst other
          have leftJoint := setup.recorded_joint
            (fun who => setup.commitRecoveryNormalizedFlagPolicy finite who (firstMemory who))
            earlier joint legal reached leftConsistent
          have rightJointEq := setup.recorded_joint
            (fun who => setup.commitRecoveryNormalizedFlagPolicy finite who (secondMemory who))
            rightEarlier rightJoint rightLegal rightReached rightConsistent
          have omissions := setup.commitRecoveryNormalizedFlagPolicy_joint_missed_eq finite
            left right earlier rightEarlier firstMemory secondMemory flags previousClock excluded
            observed middleCommit otherCommit
          have omissions : (fun who => CommitRecoveryMove.missed (joint who)) =
              (fun who => CommitRecoveryMove.missed (rightJoint who)) := by
            simpa only [leftJoint, rightJointEq] using omissions
          change _ ∈ ((left.step joint).map some).support at reached
          change _ ∈ ((right.step rightJoint).map some).support at rightReached
          obtain ⟨leftNext, leftSupport, rfl⟩ :=
            (PMF.mem_support_map_iff some (left.step joint) _).mp reached
          obtain ⟨rightNext, rightSupport, rfl⟩ :=
            (PMF.mem_support_map_iff some (right.step rightJoint) _).mp rightReached
          obtain ⟨l, lm, lnext⟩ := left.step_raw_result joint leftNext leftSupport
          obtain ⟨r, rm, rnext⟩ := right.step_raw_result rightJoint rightNext rightSupport
          have rightRaw : r.1 ∈
              (ProtocolState.recoveryStep setup.program right.point left.excluded
                rightJoint).support := excluded.symm ▸ rm
          have rawExcluded := (ProtocolState.recoveryStep_commit_public_congr focal setup.program
            left.point right.point (observed focal) middleCommit left.excluded joint rightJoint
            l.1 lm r.1 rightRaw).2 (congrFun omissions)
          intro who nonfocal
          have oldInfo := before who nonfocal
          have oldSignal := congrArg (fun info => info.1.1) oldInfo
          rw [setup.current_signal who earlier, setup.current_signal who rightEarlier] at oldSignal
          have oldView := Option.some.inj (congrArg Prod.fst oldSignal)
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
                  (secondMemory who) info).val) oldInfo
              _ = rightJoint who := (congrFun rightJointEq who).symm
          have rawView := ProtocolState.recoveryStep_commit_observe_congr who setup.program
            left.point right.point oldView middleCommit left.excluded joint rightJoint ownChoice
            l.1 lm r.1 rightRaw
          have savedPair : left.saved = right.saved := leftSaved.trans rightSaved.symm
          have closed := CommitRecoveryState.close_observed_congr who
            (left.install l.1 l.2) (right.install r.1 r.2) rawView
            (congrArg (ProtocolState.observe who setup.program) savedPair) rawExcluded
            (leftEntry.trans rightEntry.symm) (leftGeneration.trans rightGeneration.symm)
          have point : ProtocolState.observe who setup.program leftNext.point =
              ProtocolState.observe who setup.program rightNext.point := by
            rw [lnext, rnext]
            exact congrArg Prod.fst closed
          have saved : ProtocolState.observe who setup.program leftNext.saved =
              ProtocolState.observe who setup.program rightNext.saved := by
            rw [lnext, rnext]
            exact congrArg (fun data => data.2.1) closed
          have finalExcluded : leftNext.excluded = rightNext.excluded := by
            rw [lnext, rnext]
            exact congrArg (fun data => data.2.2.1) closed
          have generation : leftNext.generation = rightNext.generation := by
            rw [lnext, rnext]
            exact congrArg (fun data => data.2.2.2.2) closed
          have savedRank : ProtocolState.remaining setup.program leftNext.saved =
              ProtocolState.remaining setup.program rightNext.saved := by
            have lower := ProtocolView.position_add_remaining who setup.program leftNext.saved
            have upper := ProtocolView.position_add_remaining who setup.program rightNext.saved
            rw [saved] at lower
            omega
          have signal : (setup.commitRecoveryPrivate who (some leftNext),
                setup.commitRecoveryPublic (some leftNext)) =
              (setup.commitRecoveryPrivate who (some rightNext),
                setup.commitRecoveryPublic (some rightNext)) := by
            simp only [commitRecoveryPrivate, commitRecoveryPublic, Option.map_some]
            rw [point, finalExcluded, generation, savedRank]
          exact setup.information_extend_congr who earlier rightEarlier joint rightJoint legal
            rightLegal reached rightReached oldInfo ownChoice signal

/-- Every nonfocal original behavioral action-likelihood factor is unchanged
by the actual source-word substitution. In particular this retains each
opponent's complete retired word rather than a refreshed entry prior. -/
theorem commitRecoveryNormalizedFlagPolicy_nonfocal_reach_eq
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
    ∀ who, who ≠ focal →
      setup.commitRecoveryModel.playerReachProbability strategy who leftTrace =
        setup.commitRecoveryModel.playerReachProbability strategy who rightTrace := by
  have same := setup.commitRecoveryNormalizedFlagPolicy_nonfocal_info_eq finite focal first
    prior committing firstMemory secondMemory flags otherMemory leftTrace rightTrace leftRetained
    rightRetained leftConsistent rightConsistent clock within
  intro who nonfocal
  rw [setup.commitRecoveryModel.playerReachProbability_eq_ownPlayReachProbability,
    setup.commitRecoveryModel.playerReachProbability_eq_ownPlayReachProbability,
    setup.commitRecoveryModel_perfectRecall who leftTrace rightTrace (same who nonfocal)]

end Vegas.SourceProgram.Setup
