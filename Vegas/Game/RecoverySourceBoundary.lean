/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceCheckpoint
import GameTheory.Protocol.Backward

/-! # Legal continuation of initialized source recovery traces -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Actual legal source phase paths extend the one initialized setup trace.
The source protocol never redraws the initial private setup. -/
theorem SourceProgram.Setup.recoveryTrace_of_reaches
    (setup : Setup (Player := Player) (L := L))
    (initial : SourceProgram.Config Player L setup.context)
    {first last : CommitRecoveryState setup.program}
    (trace : Nonempty (setup.commitRecoveryProtocol.Trace (some first)))
    (reaches : (SourceProgram.commitRecoveryProtocol setup.program initial).Reaches first last) :
    Nonempty (setup.commitRecoveryProtocol.Trace (some last)) := by
  induction reaches with
  | refl => exact trace
  | @tail middle last previous step ih =>
      obtain ⟨prior⟩ := ih
      obtain ⟨joint, legal, supported⟩ := step
      refine ⟨prior.extend joint legal ?_⟩
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨last, supported, rfl⟩

end Vegas
