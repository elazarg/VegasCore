/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryProtocol
import GameTheory.Protocol.History

/-! # Chronological control of source recovery histories -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

namespace CommitRecoveryState

/-- Generation separates retries, while the instruction position orders a single attempt. -/
def control (state : CommitRecoveryState program) : Nat :=
  state.generation * (instructionCount program + 1) +
    (instructionCount program - ProtocolState.remaining program state.point)

/-- Every actual source instruction strictly advances its chronological control,
including an automatic retry or an exhausted commitment block. -/
theorem step_control_lt (state : CommitRecoveryState program)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (running : ¬ ProtocolState.terminal program state.point)
    (supported : next ∈ (state.step joint).support) : state.control < next.control := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have rawMember : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  have consumed := ProtocolState.recoveryStep_remaining program state.point state.excluded joint
    result.1 running rawMember
  let after := state.install result.1 result.2
  change state.control < after.close.control
  have beforeBound := ProtocolState.remaining_le_instructionCount program state.point
  by_cases retries : after.Finished ∧ after.NewFailure ∧ after.Survives
  · rw [close_of_retry after retries.1 retries.2.1 retries.2.2]
    change state.generation * (instructionCount program + 1) +
        (instructionCount program - ProtocolState.remaining program state.point) <
      (state.generation + 1) * (instructionCount program + 1) +
        (instructionCount program - ProtocolState.remaining program after.retry.point)
    rw [Nat.add_mul]
    omega
  · have rank := after.close_remaining_le retries
    have generation : after.close.generation = state.generation := by
      unfold close
      split
      · split
        · split
          · exact (retries ⟨by assumption, by assumption, by assumption⟩).elim
          · rfl
        · rfl
      · split <;> rfl
    unfold control
    rw [generation]
    change ProtocolState.remaining program after.close.point ≤
      ProtocolState.remaining program result.1.1 at rank
    change ProtocolState.remaining program result.1.1 + 1 =
      ProtocolState.remaining program state.point at consumed
    omega

end CommitRecoveryState

namespace Setup

/-- The setup draw precedes the generation and instruction control of all source play. -/
def commitRecoveryControl (setup : Setup (Player := Player) (L := L))
    (state : setup.commitRecoveryProtocol.State) : Nat :=
  state.elim 0 (fun current => current.control + 1)

/-- Legal source transitions strictly advance control, without a finite-player hypothesis. -/
theorem commitRecoveryControl_step (setup : Setup (Player := Player) (L := L))
    {before after : setup.commitRecoveryProtocol.State}
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support) :
    setup.commitRecoveryControl before < setup.commitRecoveryControl after := by
  cases before with
  | none =>
      obtain ⟨inputs, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact Nat.zero_lt_succ _
  | some current =>
      obtain ⟨next, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact Nat.add_lt_add_right (current.step_control_lt joint next legal.1 member) 1

/-- Reachable source histories never decrease chronological control. -/
theorem commitRecoveryControl_le_of_reaches
    (setup : Setup (Player := Player) (L := L))
    {fuel : Nat} {start last : setup.commitRecoveryProtocol.History}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel start last) :
    setup.commitRecoveryControl start.state ≤ setup.commitRecoveryControl last.state := by
  induction reached with
  | refl => exact le_rfl
  | step joint legal supported rest ih =>
      exact (setup.commitRecoveryControl_step joint legal supported).le.trans ih

/-- Control orders the genuine ancestors of one chosen complete source history. -/
theorem commitRecovery_ancestor_of_control_le
    (setup : Setup (Player := Player) (L := L))
    {firstFuel secondFuel : Nat} {first second target : setup.commitRecoveryProtocol.History}
    (firstReached : setup.commitRecoveryProtocol.ReachesWithin firstFuel first target)
    (secondReached : setup.commitRecoveryProtocol.ReachesWithin secondFuel second target)
    (ordered : setup.commitRecoveryControl first.state ≤ setup.commitRecoveryControl second.state) :
    setup.commitRecoveryProtocol.ReachesWithin firstFuel first second := by
  by_cases lengths : first.trace.length ≤ second.trace.length
  · exact firstReached.ancestor_comparable secondReached lengths
  · have reverse := secondReached.ancestor_comparable firstReached (by omega)
    have sameLength : first.trace.length = second.trace.length := by
      cases reverse with
      | refl => rfl
      | step joint legal supported rest =>
          have strict := setup.commitRecoveryControl_step joint legal supported
          have later := setup.commitRecoveryControl_le_of_reaches rest
          simp only [History.extend] at later
          exact (by omega : False).elim
    omega

/-- Ancestors with the same source control are the same full chosen history. -/
theorem commitRecovery_ancestor_eq_of_control_eq
    (setup : Setup (Player := Player) (L := L))
    {firstFuel secondFuel : Nat} {first second target : setup.commitRecoveryProtocol.History}
    (firstReached : setup.commitRecoveryProtocol.ReachesWithin firstFuel first target)
    (secondReached : setup.commitRecoveryProtocol.ReachesWithin secondFuel second target)
    (same : setup.commitRecoveryControl first.state = setup.commitRecoveryControl second.state) :
    first = second := by
  have ordered := setup.commitRecovery_ancestor_of_control_le firstReached secondReached same.le
  cases ordered with
  | refl => rfl
  | step joint legal supported rest =>
      have strict := setup.commitRecoveryControl_step joint legal supported
      have later := setup.commitRecoveryControl_le_of_reaches rest
      simp only [History.extend] at later
      omega

end Setup
end Vegas.SourceProgram
