/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryObservation

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

end Vegas.SourceProgram.Setup
