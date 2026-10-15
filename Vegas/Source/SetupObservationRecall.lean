/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryObservation
import Vegas.Source.IntendedGame

/-! # Reconstructing setup observations at previous source ranks -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Rank zero precedes the private setup draw; subsequent ranks refer to the
original source protocol. Future source ranks have no reconstructed view. -/
def viewAtRank (who : Player) : Nat → setup.ProtocolView who → Option (setup.ProtocolView who)
  | 0, _ => some none
  | rank + 1, view => view.bind fun current =>
      (ProtocolView.atRank who setup.program rank current).map some

theorem protocol_recover_predecessor (admission : CommitmentInterface setup.program)
    (who : Player) {before after : setup.ProtocolState}
    (prior : (setup.executionProtocol admission).Trace before)
    (joint : Player → Option (OwnAction Player L))
    (supported : after ∈ (setup.protocolStep before joint).support) :
    setup.viewAtRank who prior.length (setup.protocolObserve who after) =
      some (setup.protocolObserve who before) := by
  have count := setup.protocol_history_length admission prior
  cases before with
  | none =>
      have length : prior.length = 0 := by
        change prior.length + (instructionCount setup.program + 1) = _ at count
        omega
      rw [length]
      rfl
  | some before =>
      obtain ⟨after, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      have position := ProtocolView.position_add_remaining who setup.program before
      have length : prior.length =
          ProtocolView.position who setup.program
            (ProtocolState.observe who setup.program before) + 1 := by
        change prior.length + ProtocolState.remaining setup.program before = _ at count
        omega
      rw [length]
      change ((ProtocolView.atRank who setup.program _
        (ProtocolState.observe who setup.program after)).map some) = _
      rw [ProtocolView.atRank_step who setup.program before after joint reached _ le_rfl,
        ProtocolView.atRank_position]
      rfl

theorem intendedTrace_length_eq_of_observe (who : Player)
    {first second : setup.intendedProtocol.State}
    (firstTrace : setup.intendedProtocol.Trace first)
    (secondTrace : setup.intendedProtocol.Trace second)
    (same : setup.protocolObserve who first = setup.protocolObserve who second) :
    firstTrace.length = secondTrace.length := by
  have firstCount := setup.protocol_history_length
    (CommitmentInterface.values setup.program) (restrictAvailable.trace firstTrace)
  have secondCount := setup.protocol_history_length
    (CommitmentInterface.values setup.program) (restrictAvailable.trace secondTrace)
  have remaining := setup.protocolRemaining_eq_of_observe who first second same
  simp only [restrictAvailable.trace_length] at firstCount secondCount
  omega

/-- Equal observations after two legal intended steps also identify the
preceding observations. The source view retains the whole observed past. -/
theorem intended_predecessor_observations_eq (who : Player)
    {first second firstAfter secondAfter : setup.intendedProtocol.State}
    (firstTrace : setup.intendedProtocol.Trace first)
    (secondTrace : setup.intendedProtocol.Trace second)
    (firstJoint secondJoint : Player → Option (OwnAction Player L))
    (firstLegal : setup.intendedProtocol.Legal first firstJoint)
    (secondLegal : setup.intendedProtocol.Legal second secondJoint)
    (firstSupported : firstAfter ∈
      (setup.intendedProtocol.step first ⟨firstJoint, firstLegal⟩).support)
    (secondSupported : secondAfter ∈
      (setup.intendedProtocol.step second ⟨secondJoint, secondLegal⟩).support)
    (same : setup.protocolObserve who firstAfter = setup.protocolObserve who secondAfter) :
    setup.protocolObserve who first = setup.protocolObserve who second := by
  have lengths := setup.intendedTrace_length_eq_of_observe who
    (firstTrace.extend firstJoint firstLegal firstSupported)
    (secondTrace.extend secondJoint secondLegal secondSupported) same
  simp only [Trace.length, Nat.add_right_cancel_iff] at lengths
  have left := setup.protocol_recover_predecessor (CommitmentInterface.values setup.program)
    who (restrictAvailable.trace firstTrace) firstJoint firstSupported
  have right := setup.protocol_recover_predecessor (CommitmentInterface.values setup.program)
    who (restrictAvailable.trace secondTrace) secondJoint secondSupported
  simp only [restrictAvailable.trace_length] at left right
  rw [lengths, same] at left
  exact Option.some.inj (left.symm.trans right)

end Vegas.SourceProgram.Setup
