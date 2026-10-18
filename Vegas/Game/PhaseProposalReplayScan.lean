/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalReplayPath
import Vegas.Game.PhasePublicSourceChronology

/-! # Source replay prestates retain the full native failure scan -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The scan applies at every actual intermediate prestate, including an
excluded owner's automatic instruction. It is not reduced to final exclusions. -/
theorem native_public_path_point_scan
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (inherited : Finset Player)
    (first : ProtocolState setup.program × Finset Player)
    (states : List (ProtocolState setup.program × Finset Player))
    (chain : (first :: states).IsChain (NativePublicSourceStep native 0 setup.program))
    (before : first.2 = inherited ∪ native.failureOwnersBefore
      (instructionCount setup.program - ProtocolState.remaining setup.program first.1)) :
    ∀ point ∈ first :: states, point.2 = inherited ∪ native.failureOwnersBefore
      (instructionCount setup.program - ProtocolState.remaining setup.program point.1) := by
  induction states generalizing first with
  | nil =>
      intro point member
      have same : point = first := List.mem_singleton.mp member
      subst point
      exact before
  | cons middle states ih =>
      have moved := List.isChain_cons_cons.mp chain
      have running := moved.1.1.1
      have bound := ProtocolState.remaining_le_instructionCount setup.program first.1
      have nonzero : ProtocolState.remaining setup.program first.1 ≠ 0 := by
        intro zero
        exact running ((ProtocolState.remaining_zero_iff_terminal setup.program first.1).mp zero)
      have bounded : instructionCount setup.program -
          ProtocolState.remaining setup.program first.1 <
            ((toEventGraph setup.program).withMode mode).order.eventCount := by
        change _ < eventCount setup.program
        rw [eventCount_eq_instructionCount]
        omega
      let event : ((toEventGraph setup.program).withMode mode).EventId :=
        ⟨instructionCount setup.program - ProtocolState.remaining setup.program first.1, bounded⟩
      have next := moved.1.excluded_scan event (by simp only [event, Nat.zero_add]) inherited before
      have ranked := moved.1.position
      have middleScan : middle.2 = inherited ∪ native.failureOwnersBefore
          (instructionCount setup.program - ProtocolState.remaining setup.program middle.1) := by
        simpa only [event, ranked] using next
      intro point member
      rcases List.mem_cons.mp member with same | later
      · subst point
        exact before
      · exact ih middle moved.2 middleScan point later

end Vegas
