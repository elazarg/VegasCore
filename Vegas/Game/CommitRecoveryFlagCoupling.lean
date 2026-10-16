/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryFlagDecoding

/-! # Failed source attempts driven by the same initialized flags

Actual complete member records determine the original source instructions.
The initialized occurrence flags then determine the entire omission word,
including the final instruction which invokes the real close dispatcher.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem recorded_joint
    (policies : ∀ who, setup.commitRecoveryModel.Policy who)
    {source target : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace source)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal source joint)
    (realized : target ∈ (setup.commitRecoveryProtocol.step source ⟨joint, legal⟩).support)
    (consistent : ∀ who, policies who ∈ setup.commitRecoveryModel.Consistent who
      (setup.commitRecoveryModel.ownPlay who (prior.extend joint legal realized))) :
    joint = fun who => (policies who (setup.commitRecoveryModel.infoOf who prior)).val := by
  funext who
  cases chosen : joint who with
  | some action =>
      have member : (setup.commitRecoveryModel.infoOf who prior, action) ∈
          setup.commitRecoveryModel.ownPlay who (prior.extend joint legal realized) := by
        change _ ∈ setup.commitRecoveryModel.toInfoSignals.ownPlay who _
        rw [InfoSignals.ownPlay_extend, chosen]
        exact List.mem_cons_self
      exact ((consistent who) _ member).symm
  | none =>
      have inactive : ¬ setup.commitRecoveryActive who
          (setup.commitRecoveryModel.infoOf who prior).1.1 :=
        (setup.commitRecoveryModel.menu_adequate who prior none).mpr
          (by simpa only [chosen] using
            setup.commitRecoveryProtocol.legalOption_of_legal legal who)
      cases selected : (policies who (setup.commitRecoveryModel.infoOf who prior)).val with
      | none => rfl
      | some move =>
          have offered := (policies who (setup.commitRecoveryModel.infoOf who prior)).property
          change setup.commitRecoveryMenu who _ _ at offered
          rw [selected] at offered
          exact (inactive offered.1).elim

private theorem consistent_prefix
    (policies : ∀ who, setup.commitRecoveryModel.Policy who)
    {source target : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace source)
    (later : setup.commitRecoveryProtocol.Trace target)
    (retained : TracePrefix prior later)
    (consistent : ∀ who, policies who ∈ setup.commitRecoveryModel.Consistent who
      (setup.commitRecoveryModel.ownPlay who later)) :
    ∀ who, policies who ∈ setup.commitRecoveryModel.Consistent who
      (setup.commitRecoveryModel.ownPlay who prior) := by
  intro who
  exact setup.commitRecoveryModel.consistent_subset_of_isSuffix
    (setup.commitRecoveryModel.ownPlay_isSuffix_of_reachesWithin who retained.reachesWithin)
    (consistent who)

variable [Fintype Player]

/-- The SAME initialized occurrence flags determine every original omission
in two actual member-consistent commitment windows. Neither the domain tables
nor the complete remembered typed words need agree. -/
theorem commitRecoveryNormalizedFlagPolicy_omissionRecall_eq
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (observer : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (firstMemory secondMemory : (who : Player) →
      setup.CommitRecoveryFlagDraw finite who × setup.CommitRecoveryDomainDraw finite who)
    (flags : ∀ who, (firstMemory who).1 = (secondMemory who).1)
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
    setup.omissionRecall leftTrace = setup.omissionRecall rightTrace := by
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
          have leftBefore := setup.consistent_prefix
            (fun who => setup.commitRecoveryNormalizedFlagPolicy finite who (firstMemory who))
            earlier _ (.extend .refl joint legal reached) leftConsistent
          have rightBefore := setup.consistent_prefix
            (fun who => setup.commitRecoveryNormalizedFlagPolicy finite who (secondMemory who))
            rightEarlier _ (.extend .refl rightJoint rightLegal rightReached) rightConsistent
          have previous := ih rightEarlier rightKept leftBefore rightBefore previousClock
            previousInside.le
          obtain ⟨left, right, rfl, rfl, _leftSaved, _rightSaved, _leftEntry, _rightEntry,
            _leftGeneration, _rightGeneration, excluded, observed, _publicPast⟩ :=
              setup.inside_attempt_public_eq observer first prior committing earlier rightEarlier
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
          change (fun who => CommitRecoveryMove.missed (joint who)) ::
              setup.omissionRecall earlier =
            (fun who => CommitRecoveryMove.missed (rightJoint who)) ::
              setup.omissionRecall rightEarlier
          rw [previous]
          congr 1
          rw [leftJoint, rightJointEq]
          exact omissions

/-- Actual failed windows generated by the same initialized flag tables have
identical erased reset histories. The omission word is derived from the full
member records rather than supplied as a coupling hypothesis. -/
theorem commitRecoveryNormalizedFlagPolicy_failed_attempt_erased_eq
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (observer : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (firstMemory secondMemory : (who : Player) →
      setup.CommitRecoveryFlagDraw finite who × setup.CommitRecoveryDomainDraw finite who)
    (flags : ∀ who, (firstMemory who).1 = (secondMemory who).1)
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
    (boundary : leftTrace.length + ProtocolState.commitEnd setup.program first.point =
      prior.length + ProtocolState.remaining setup.program first.point)
    (failed : leftState.elim False
      (fun left => (left.excluded \ first.entryExcluded).Nonempty)) :
    setup.commitRecoveryErasedHistory ⟨leftState, leftTrace⟩ =
      setup.commitRecoveryErasedHistory ⟨rightState, rightTrace⟩ := by
  have omissions := setup.commitRecoveryNormalizedFlagPolicy_omissionRecall_eq finite observer
    first prior committing firstMemory secondMemory flags leftTrace rightTrace leftRetained
    rightRetained leftConsistent rightConsistent clock boundary.le
  exact setup.commitRecovery_failed_attempt_erased_eq observer first prior committing leftTrace
    rightTrace leftRetained rightRetained omissions boundary failed

/-- The selected erased/no-new-miss source continuation has the same ORIGINAL
terminal readout and every player's payoff after actual failed attempts driven
by the same initialized flags. Future accepted failure and rescue remain in
this terminal law. -/
theorem commitRecoveryNormalizedFlagPolicy_failed_attempt_terminal_joint_eq
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (observer : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (firstMemory secondMemory : (who : Player) →
      setup.CommitRecoveryFlagDraw finite who × setup.CommitRecoveryDomainDraw finite who)
    (flags : ∀ who, (firstMemory who).1 = (secondMemory who).1)
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
    (boundary : leftTrace.length + ProtocolState.commitEnd setup.program first.point =
      prior.length + ProtocolState.remaining setup.program first.point)
    (failed : leftState.elim False
      (fun left => (left.excluded \ first.entryExcluded).Nonempty)) :
    (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.commitRecoveryNoMissErasedProfile profile) ⟨leftState, leftTrace⟩).map
        (fun history =>
          (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) =
      (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.commitRecoveryNoMissErasedProfile profile) ⟨rightState, rightTrace⟩).map
        (fun history =>
          (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) := by
  have omissions := setup.commitRecoveryNormalizedFlagPolicy_omissionRecall_eq finite observer
    first prior committing firstMemory secondMemory flags leftTrace rightTrace leftRetained
    rightRetained leftConsistent rightConsistent clock boundary.le
  exact setup.commitRecoveryNoMissErasedProfile_failed_attempt_terminal_joint_eq profile utility
    excludedPayoff certificate observer first prior committing leftTrace rightTrace leftRetained
    rightRetained omissions boundary failed

end Vegas.SourceProgram.Setup
