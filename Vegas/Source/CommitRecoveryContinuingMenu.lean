/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryFiniteness
import Vegas.Source.ExclusionMoveGame

/-! # Nonomitting bindings and mandatory openings in source recovery -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Continuing moves never omit a commitment and never withhold an opening.
An accepted failed binding remains available as a distinct nonomitting action. -/
def CommitRecoveryContinues (who : Player) (info : setup.commitRecoveryModel.InfoState who)
    (choice : Option (CommitRecoveryMove Player L)) : Prop :=
  ∀ move, choice = some move → move.missing = false ∧
    (info.1.1.1.elim false (ProtocolView.atCommit who setup.program) = false →
      ¬ move.action.IsFailure)

def CommitRecoveryContinuingChoice (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) :=
  {choice : setup.commitRecoveryModel.Choice who info //
    setup.CommitRecoveryContinues who info choice.1}

def commitRecoveryContinuingChoice (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) :
    setup.CommitRecoveryContinuingChoice who info ↪ setup.commitRecoveryModel.Choice who info :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem commitRecovery_atCommit_info (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.commitRecoveryModel.infoOf who trace).1.1.1.elim false
        (ProtocolView.atCommit who setup.program) =
      state.elim false (fun current => ProtocolState.atCommit setup.program current.point) := by
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who trace).1.1.1.elim false _ = _
  rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current]
  cases state with
  | none => rfl
  | some current => exact ProtocolState.atCommit_observe setup.program current.point who

end Vegas.SourceProgram.Setup
