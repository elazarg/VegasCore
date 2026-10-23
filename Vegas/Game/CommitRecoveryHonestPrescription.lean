/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryHonestPins
import Vegas.Game.CommitRecoveryRestriction
import Vegas.Game.CommitRecoveryPooledCompletion
import Vegas.Game.ExclusionMoveExtension

/-! # Actual honest domain pins for normalized source completion

A given intended behavioral profile defines legal domain distributions on
its genuine normalized queries. Original honest information is reconstructed
from the key, so choosing a witness does not change the resulting raw law.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Embed an actual intended action as a legal ordinary part at its normalized
source query. Accepted failure and omission are not part of this domain law. -/
def commitRecoveryHonestDomainChoice (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.intendedModel.InfoState who) (choice : setup.intendedModel.Choice who view) :
    setup.CommitRecoveryValueChoice who
      (setup.commitRecoveryErasedInformation who (setup.commitRecoveryNoMissInformation who
        (setup.commitRecoveryInformation wellFormed who view))) :=
  ⟨setup.commitRecoveryNoMissErasedChoice who
    (setup.commitRecoveryInformation wellFormed who view)
    (setup.commitRecoveryChoice wellFormed who view choice), by
      intro move selected
      change CommitRecoveryMove.lift choice.val = some move at selected
      cases chosen : choice.val with
      | none => rw [chosen] at selected; cases selected
      | some action =>
          rw [chosen] at selected
          cases Option.some.inj selected
          exact ⟨rfl, setup.intendedMenu_not_failure who view choice.val choice.property action
            chosen⟩⟩

omit [Fintype Player] in
/-- Normalizing the source query preserves the literal intended raw action. -/
theorem commitRecoveryHonestDomainChoice_raw (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.intendedModel.InfoState who) (choice : setup.intendedModel.Choice who view) :
    (setup.commitRecoveryHonestDomainChoice wellFormed who view choice).val.val =
      CommitRecoveryMove.lift choice.val := rfl

omit [Fintype Player] in
private theorem domain_cast_raw (who : Player)
    {first second : setup.commitRecoveryModel.InfoState who} (same : first = second)
    (choice : setup.CommitRecoveryValueChoice who first) :
    (Eq.mp (congrArg (setup.CommitRecoveryValueChoice who) same) choice).val.val =
      choice.val.val := by cases same; rfl

end Vegas.SourceProgram.Setup
