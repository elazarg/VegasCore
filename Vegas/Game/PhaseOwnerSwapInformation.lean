/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSwapInformation
import Vegas.Game.OnePacketOwnerSwap

/-! # Foreign owner transpositions preserve actual phased observer information -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup))}

/-- A transposition supported on one foreign owner's private fields and
prepared values preserves the focal player's complete actual phase input.
This uses the physical recalled responses, rather than only the current view. -/
theorem ownerSwap_phaseInput_eq (owner who : Player) (different : who ≠ owner)
    (first second : PlayerView (graph setup)) (bounds : MessageBounds (graph setup))
    (initial : PMF (phaseApplication (runtime setup) leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
    (control : (phaseApplication (runtime setup) leaks).Control)
    (trace : ((PhaseCount.onePacketMenu (runtime setup) leaks bounds).protocol
      initial horizon scheduler).Trace (some control)) :
    (((ownerSwap owner first second).phaseExecution control.execution).recall who,
        ((ownerSwap owner first second).phaseExecution control.execution).observe
          (phaseApplication (runtime setup) leaks) who) =
      (control.execution.recall who,
        control.execution.observe (phaseApplication (runtime setup) leaks) who) := by
  obtain ⟨fields, actions, handles⟩ := ownerSwap_fixes owner first second different
  exact (ownerSwap owner first second).phaseInput_eq_of_fixed bounds initial horizon
    scheduler control trace who fields actions handles

end Vegas
