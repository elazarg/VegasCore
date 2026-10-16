/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryNonCommitObservation
import Vegas.Source.CommitRecoveryPredecessor
import Vegas.Source.CommitRecoveryOwnHistory
import Vegas.Source.CommitRecoveryControl
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Actual surviving observations before noncommitment recovery steps -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Setup

/-- Genuine noncommitment steps preserve enough observed information to
recover the previous private signal, with arbitrary permanent exclusions. -/
theorem commitRecovery_noncommit_predecessor_private
    (setup : Setup (Player := Player) (L := L)) (who : Player)
    (first second : CommitRecoveryState setup.program)
    (firstTrace : setup.commitRecoveryProtocol.Trace (some first))
    (secondTrace : setup.commitRecoveryProtocol.Trace (some second))
    (firstJoint secondJoint : Player → Option (CommitRecoveryMove Player L))
    (firstLegal : setup.commitRecoveryProtocol.Legal (some first) firstJoint)
    (secondLegal : setup.commitRecoveryProtocol.Legal (some second) secondJoint)
    (firstAfter secondAfter : setup.commitRecoveryProtocol.State)
    (firstReached : firstAfter ∈
      (setup.commitRecoveryProtocol.step (some first) ⟨firstJoint, firstLegal⟩).support)
    (secondReached : secondAfter ∈
      (setup.commitRecoveryProtocol.step (some second) ⟨secondJoint, secondLegal⟩).support)
    (firstNotCommit : ProtocolState.atCommit setup.program first.point = false)
    (secondNotCommit : ProtocolState.atCommit setup.program second.point = false)
    (firstSurvives : who ∉ first.excluded) (secondSurvives : who ∉ second.excluded)
    (after : setup.commitRecoveryPrivate who firstAfter =
      setup.commitRecoveryPrivate who secondAfter) :
    setup.commitRecoveryPrivate who (some first) =
      setup.commitRecoveryPrivate who (some second) := by
  obtain ⟨left, leftReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp firstReached
  obtain ⟨right, rightReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp secondReached
  obtain ⟨leftRaw, leftRawReached, rfl⟩ := first.step_noncommit_atPoint
    (setup.commitRecovery_blockFrontier firstTrace) firstNotCommit firstJoint left leftReached
  obtain ⟨rightRaw, rightRawReached, rfl⟩ := second.step_noncommit_atPoint
    (setup.commitRecovery_blockFrontier secondTrace) secondNotCommit secondJoint right rightReached
  change some (ProtocolState.observe who setup.program leftRaw.1) =
    some (ProtocolState.observe who setup.program rightRaw.1) at after
  exact congrArg some (ProtocolView.recoveryStep_predecessor_eq who setup.program first.point
    second.point first.excluded second.excluded firstJoint secondJoint leftRaw rightRaw
    firstLegal.1 secondLegal.1 leftRawReached rightRawReached firstSurvives secondSurvives
    (Option.some.inj after))

/-- Two genuine noncommitment intervals retain the same complete signal recall
when their prior recalls and final private observations agree. -/
theorem commitRecovery_noncommit_signals_eq_of_prefixes
    (setup : Setup (Player := Player) (L := L)) (who : Player)
    {firstStart secondStart firstEnd secondEnd : setup.commitRecoveryProtocol.State}
    (firstPrior : setup.commitRecoveryProtocol.Trace firstStart)
    (secondPrior : setup.commitRecoveryProtocol.Trace secondStart)
    (firstTrace : setup.commitRecoveryProtocol.Trace firstEnd)
    (secondTrace : setup.commitRecoveryProtocol.Trace secondEnd)
    (firstPrefix : TracePrefix firstPrior firstTrace)
    (secondPrefix : TracePrefix secondPrior secondTrace)
    (prior : setup.commitRecoverySignals.infoOf who firstPrior =
      setup.commitRecoverySignals.infoOf who secondPrior)
    (lengths : firstTrace.length - firstPrior.length =
      secondTrace.length - secondPrior.length)
    (firstNonCommit : ∀ {middle} (trace : setup.commitRecoveryProtocol.Trace middle),
      TracePrefix firstPrior trace → TracePrefix trace firstTrace →
      trace.length < firstTrace.length →
      ∃ current, middle = some current ∧
        ProtocolState.atCommit setup.program current.point = false)
    (secondNonCommit : ∀ {middle} (trace : setup.commitRecoveryProtocol.Trace middle),
      TracePrefix secondPrior trace → TracePrefix trace secondTrace →
      trace.length < secondTrace.length →
      ∃ current, middle = some current ∧
        ProtocolState.atCommit setup.program current.point = false)
    (firstSurvives : who ∉ (setup.commitRecoveryPublic firstEnd).1)
    (secondSurvives : who ∉ (setup.commitRecoveryPublic secondEnd).1)
    (after : setup.commitRecoveryPrivate who firstEnd =
      setup.commitRecoveryPrivate who secondEnd) :
    setup.commitRecoverySignals.infoOf who firstTrace =
      setup.commitRecoverySignals.infoOf who secondTrace := by
  induction firstPrefix generalizing secondEnd with
  | refl =>
      have bounded := secondPrefix.length_le
      have sameLength : secondPrior.length = secondTrace.length := by
        simp only [Nat.sub_self] at lengths
        omega
      have sameHistory := secondPrefix.eq_of_length sameLength
      cases sameHistory
      exact prior
  | @extend firstBefore firstAfter firstBeforeTrace firstEarlier firstJoint firstLegal
      firstReached ih =>
      cases secondPrefix with
      | refl =>
          have bounded := firstEarlier.length_le
          simp only [Trace.length, Nat.sub_self] at lengths
          omega
      | @extend secondBefore secondEnd secondBeforeTrace secondEarlier secondJoint
          secondLegal secondReached =>
          have leftLast : TracePrefix firstBeforeTrace
              (firstBeforeTrace.extend firstJoint firstLegal firstReached) :=
            .extend .refl firstJoint firstLegal firstReached
          have rightLast : TracePrefix secondBeforeTrace
              (secondBeforeTrace.extend secondJoint secondLegal secondReached) :=
            .extend .refl secondJoint secondLegal secondReached
          obtain ⟨left, leftState, leftNotCommit⟩ := firstNonCommit firstBeforeTrace
            firstEarlier leftLast (by simp only [Trace.length]; omega)
          obtain ⟨right, rightState, rightNotCommit⟩ := secondNonCommit secondBeforeTrace
            secondEarlier rightLast (by simp only [Trace.length]; omega)
          subst firstBefore
          subst secondBefore
          have leftActive : who ∉ left.excluded := fun inactive =>
            firstSurvives (setup.commitRecovery_step_excluded_subset firstJoint firstLegal
              firstReached inactive)
          have rightActive : who ∉ right.excluded := fun inactive =>
            secondSurvives (setup.commitRecovery_step_excluded_subset secondJoint secondLegal
              secondReached inactive)
          have before := setup.commitRecovery_noncommit_predecessor_private who left right
            firstBeforeTrace secondBeforeTrace firstJoint secondJoint firstLegal secondLegal
            firstAfter secondEnd firstReached secondReached leftNotCommit rightNotCommit
            leftActive rightActive after
          have beforeLengths : firstBeforeTrace.length - firstPrior.length =
              secondBeforeTrace.length - secondPrior.length := by
            have leftBound := firstEarlier.length_le
            have rightBound := secondEarlier.length_le
            simp only [Trace.length] at lengths
            omega
          have earlier := ih secondBeforeTrace secondEarlier beforeLengths
            (fun trace early later shorter => firstNonCommit trace early
              (later.trans leftLast) (by simp only [Trace.length]; omega))
            (fun trace early later shorter => secondNonCommit trace early
              (later.trans rightLast) (by simp only [Trace.length]; omega))
            leftActive rightActive before
          have current := congrArg Prod.fst earlier
          rw [setup.commitRecoverySignals_current, setup.commitRecoverySignals_current] at current
          have publicAfter := setup.commitRecovery_noncommit_public_eq who left right
            firstBeforeTrace secondBeforeTrace firstJoint secondJoint firstLegal secondLegal
            firstAfter secondEnd firstReached secondReached leftNotCommit before
            (congrArg Prod.snd current) after
          change ((setup.commitRecoveryPrivate who firstAfter,
              setup.commitRecoveryPublic firstAfter),
            (setup.commitRecoverySignals.infoOf who firstBeforeTrace).1 ::
              (setup.commitRecoverySignals.infoOf who firstBeforeTrace).2) =
            ((setup.commitRecoveryPrivate who secondEnd,
              setup.commitRecoveryPublic secondEnd),
            (setup.commitRecoverySignals.infoOf who secondBeforeTrace).1 ::
              (setup.commitRecoverySignals.infoOf who secondBeforeTrace).2)
          rw [after, publicAfter, earlier]

private theorem noncommit_remaining
    (setup : Setup (Player := Player) (L := L))
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal (some current) joint)
    {after : setup.commitRecoveryProtocol.State}
    (reached : after ∈ (setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩).support)
    (notCommit : ProtocolState.atCommit setup.program current.point = false) :
    after.elim 0 (fun next => ProtocolState.remaining setup.program next.point) + 1 =
      ProtocolState.remaining setup.program current.point := by
  obtain ⟨next, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  obtain ⟨result, raw, rfl⟩ := current.step_noncommit_atPoint
    (setup.commitRecovery_blockFrontier trace) notCommit joint next supported
  exact ProtocolState.recoveryStep_remaining setup.program current.point current.excluded joint
    result legal.1 raw

private theorem noncommit_prefix_length
    (setup : Setup (Player := Player) (L := L))
    {first last : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace first)
    (trace : setup.commitRecoveryProtocol.Trace last)
    (retained : TracePrefix prior trace)
    (nonCommit : ∀ {middle} (earlierTrace : setup.commitRecoveryProtocol.Trace middle),
      TracePrefix prior earlierTrace → TracePrefix earlierTrace trace →
      earlierTrace.length < trace.length →
      ∃ current, middle = some current ∧
        ProtocolState.atCommit setup.program current.point = false) :
    trace.length + last.elim 0 (fun current =>
        ProtocolState.remaining setup.program current.point) =
      prior.length + first.elim 0 (fun current =>
        ProtocolState.remaining setup.program current.point) := by
  induction retained with
  | refl => rfl
  | @extend before after beforeTrace earlier joint legal reached ih =>
      have finalStep : TracePrefix beforeTrace (beforeTrace.extend joint legal reached) :=
        .extend .refl joint legal reached
      obtain ⟨current, rfl, notCommit⟩ := nonCommit beforeTrace earlier finalStep
        (by simp only [Trace.length]; omega)
      have consumed := noncommit_remaining setup current beforeTrace joint legal reached notCommit
      have beforeLength := ih (fun earlierTrace old later shorter =>
        nonCommit earlierTrace old (later.trans finalStep)
          (by simp only [Trace.length]; omega))
      simp only [Trace.length, Option.elim_some] at *
      omega

private theorem source_control_between
    (setup : Setup (Player := Player) (L := L))
    (first last : CommitRecoveryState setup.program)
    (sameGeneration : first.generation = last.generation)
    (middle : setup.commitRecoveryProtocol.State)
    (before : setup.commitRecoveryControl (some first) ≤ setup.commitRecoveryControl middle)
    (after : setup.commitRecoveryControl middle ≤ setup.commitRecoveryControl (some last)) :
    ∃ current, middle = some current ∧ current.generation = first.generation ∧
      ProtocolState.remaining setup.program last.point ≤
        ProtocolState.remaining setup.program current.point ∧
      ProtocolState.remaining setup.program current.point ≤
        ProtocolState.remaining setup.program first.point := by
  cases middle with
  | none =>
      simp only [commitRecoveryControl, Option.elim_some, Option.elim_none] at before
      omega
  | some current =>
      have firstBound := ProtocolState.remaining_le_instructionCount setup.program first.point
      have lastBound := ProtocolState.remaining_le_instructionCount setup.program last.point
      have middleBound := ProtocolState.remaining_le_instructionCount setup.program current.point
      simp only [commitRecoveryControl, Option.elim_some,
        CommitRecoveryState.control] at before after
      have earlierGeneration : first.generation ≤ current.generation := by
        by_contra h
        have jump := Nat.mul_le_mul_right (instructionCount setup.program + 1)
          (show current.generation + 1 ≤ first.generation by omega)
        rw [Nat.add_mul, Nat.one_mul] at jump
        omega
      have laterGeneration : current.generation ≤ last.generation := by
        by_contra h
        have jump := Nat.mul_le_mul_right (instructionCount setup.program + 1)
          (show last.generation + 1 ≤ current.generation by omega)
        rw [Nat.add_mul, Nat.one_mul] at jump
        omega
      have generation : current.generation = first.generation := by omega
      refine ⟨current, rfl, generation, ?_, ?_⟩
      · rw [generation, ← sameGeneration] at after
        omega
      · rw [generation] at before
        omega

private theorem source_control_lt_of_prefix
    (setup : Setup (Player := Player) (L := L))
    {first last : setup.commitRecoveryProtocol.State}
    {prior : setup.commitRecoveryProtocol.Trace first}
    {trace : setup.commitRecoveryProtocol.Trace last}
    (retained : TracePrefix prior trace) (shorter : prior.length < trace.length) :
    setup.commitRecoveryControl first < setup.commitRecoveryControl last := by
  cases retained with
  | refl => omega
  | extend earlier joint legal supported =>
      exact (setup.commitRecoveryControl_le_of_reaches earlier.reachesWithin).trans_lt
        (setup.commitRecoveryControl_step joint legal supported)

/-- Every genuine intermediate source state lies in the same-generation
instruction window determined by its actual chosen endpoint histories. -/
theorem commitRecovery_noncommit_prefix_of_rank_window
    (setup : Setup (Player := Player) (L := L))
    (first last : CommitRecoveryState setup.program)
    (firstTrace : setup.commitRecoveryProtocol.Trace (some first))
    (lastTrace : setup.commitRecoveryProtocol.Trace (some last))
    (generation : first.generation = last.generation)
    (classify : ∀ point : SourceProgram.ProtocolState setup.program,
      ProtocolState.remaining setup.program last.point <
        ProtocolState.remaining setup.program point →
      ProtocolState.remaining setup.program point ≤
        ProtocolState.remaining setup.program first.point →
      ProtocolState.atCommit setup.program point = false)
    {middle} (trace : setup.commitRecoveryProtocol.Trace middle)
    (earlier : TracePrefix firstTrace trace) (later : TracePrefix trace lastTrace)
    (shorter : trace.length < lastTrace.length) :
    ∃ current, middle = some current ∧
      ProtocolState.atCommit setup.program current.point = false := by
  have before := setup.commitRecoveryControl_le_of_reaches earlier.reachesWithin
  have after := setup.commitRecoveryControl_le_of_reaches later.reachesWithin
  obtain ⟨current, rfl, currentGeneration, lower, upper⟩ :=
    source_control_between setup first last generation middle before after
  have strict := source_control_lt_of_prefix setup later shorter
  have currentBound := ProtocolState.remaining_le_instructionCount setup.program current.point
  have lastBound := ProtocolState.remaining_le_instructionCount setup.program last.point
  simp only [commitRecoveryControl, Option.elim_some, CommitRecoveryState.control] at strict
  rw [currentGeneration, ← generation] at strict
  exact ⟨current, rfl, classify current.point (by omega) upper⟩

/-- Actual same-generation source intervals preserve full signal recall under
an instruction window classified by the original source suffix. Interval lengths
and all intermediate noncommitment conditions are derived from the real paths. -/
theorem commitRecovery_noncommit_signals_eq_of_rank_windows
    (setup : Setup (Player := Player) (L := L)) (who : Player)
    (firstStart firstEnd secondStart secondEnd : CommitRecoveryState setup.program)
    (firstPrior : setup.commitRecoveryProtocol.Trace (some firstStart))
    (secondPrior : setup.commitRecoveryProtocol.Trace (some secondStart))
    (firstTrace : setup.commitRecoveryProtocol.Trace (some firstEnd))
    (secondTrace : setup.commitRecoveryProtocol.Trace (some secondEnd))
    (firstPrefix : TracePrefix firstPrior firstTrace)
    (secondPrefix : TracePrefix secondPrior secondTrace)
    (firstGeneration : firstStart.generation = firstEnd.generation)
    (secondGeneration : secondStart.generation = secondEnd.generation)
    (firstClassifies : ∀ point : SourceProgram.ProtocolState setup.program,
      ProtocolState.remaining setup.program firstEnd.point <
        ProtocolState.remaining setup.program point →
      ProtocolState.remaining setup.program point ≤
        ProtocolState.remaining setup.program firstStart.point →
      ProtocolState.atCommit setup.program point = false)
    (secondClassifies : ∀ point : SourceProgram.ProtocolState setup.program,
      ProtocolState.remaining setup.program secondEnd.point <
        ProtocolState.remaining setup.program point →
      ProtocolState.remaining setup.program point ≤
        ProtocolState.remaining setup.program secondStart.point →
      ProtocolState.atCommit setup.program point = false)
    (prior : setup.commitRecoverySignals.infoOf who firstPrior =
      setup.commitRecoverySignals.infoOf who secondPrior)
    (firstSurvives : who ∉ firstEnd.excluded) (secondSurvives : who ∉ secondEnd.excluded)
    (after : setup.commitRecoveryPrivate who (some firstEnd) =
      setup.commitRecoveryPrivate who (some secondEnd)) :
    setup.commitRecoverySignals.infoOf who firstTrace =
      setup.commitRecoverySignals.infoOf who secondTrace := by
  have leftNonCommit := fun {middle}
      (trace : setup.commitRecoveryProtocol.Trace middle) =>
    setup.commitRecovery_noncommit_prefix_of_rank_window
      firstStart firstEnd firstPrior firstTrace firstGeneration firstClassifies trace
  have rightNonCommit := fun {middle}
      (trace : setup.commitRecoveryProtocol.Trace middle) =>
    setup.commitRecovery_noncommit_prefix_of_rank_window
      secondStart secondEnd secondPrior secondTrace secondGeneration secondClassifies trace
  have leftLength := noncommit_prefix_length setup firstPrior firstTrace firstPrefix leftNonCommit
  have rightLength := noncommit_prefix_length setup secondPrior secondTrace secondPrefix
    rightNonCommit
  have current := congrArg Prod.fst prior
  rw [setup.commitRecoverySignals_current, setup.commitRecoverySignals_current] at current
  have beforeView := Option.some.inj (congrArg Prod.fst current)
  have afterView := Option.some.inj after
  change ProtocolState.observe who setup.program firstStart.point =
    ProtocolState.observe who setup.program secondStart.point at beforeView
  change ProtocolState.observe who setup.program firstEnd.point =
    ProtocolState.observe who setup.program secondEnd.point at afterView
  have firstBeforeRank := ProtocolView.position_add_remaining who setup.program firstStart.point
  have secondBeforeRank := ProtocolView.position_add_remaining who setup.program secondStart.point
  have firstAfterRank := ProtocolView.position_add_remaining who setup.program firstEnd.point
  have secondAfterRank := ProtocolView.position_add_remaining who setup.program secondEnd.point
  rw [beforeView] at firstBeforeRank
  rw [afterView] at firstAfterRank
  have beforeRemaining : ProtocolState.remaining setup.program firstStart.point =
      ProtocolState.remaining setup.program secondStart.point := by omega
  have afterRemaining : ProtocolState.remaining setup.program firstEnd.point =
      ProtocolState.remaining setup.program secondEnd.point := by omega
  have lengths : firstTrace.length - firstPrior.length =
      secondTrace.length - secondPrior.length := by
    have firstBound := firstPrefix.length_le
    have secondBound := secondPrefix.length_le
    simp only [Option.elim_some] at leftLength rightLength
    omega
  exact setup.commitRecovery_noncommit_signals_eq_of_prefixes who firstPrior secondPrior
    firstTrace secondTrace firstPrefix secondPrefix prior lengths leftNonCommit rightNonCommit
    firstSurvives secondSurvives after

end Setup
end Vegas.SourceProgram
