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

theorem commitRecoveryContinuingChoice_finite (finite : setup.program.FiniteBindingTypes)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    Finite (setup.CommitRecoveryContinuingChoice who info) := by
  let := setup.commitRecovery_finite_choice finite who info
  exact Finite.of_injective (setup.commitRecoveryContinuingChoice who info)
    (setup.commitRecoveryContinuingChoice who info).injective

theorem commitRecoveryContinuingChoice_nonempty (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) :
    Nonempty (setup.CommitRecoveryContinuingChoice who info) := by
  classical
  by_cases active : setup.commitRecoveryActive who info.1.1
  · cases current : info.1.1.1 with
    | none => simp only [commitRecoveryActive, current, Option.elim_none] at active
    | some view =>
        have acting := active
        simp only [commitRecoveryActive, current, Option.elim_some] at acting
        obtain ⟨choice, legal, continues⟩ := ProtocolView.exists_move_menu who setup.program
          (CommitmentInterface.forfeiture setup.program) view
        cases choice with
        | none => exact (legal acting.1).elim
        | some action =>
            have offered : some (⟨action, false⟩ : CommitRecoveryMove Player L) ∈
                setup.commitRecoveryModel.menu who info := by
              refine ⟨active, ?_⟩
              simp only [current, Option.elim_some]
              refine ⟨legal.2, ?_⟩
              dsimp only
              split
              · intro impossible; cases impossible
              · rfl
            refine ⟨⟨⟨some ⟨action, false⟩, offered⟩, ?_⟩⟩
            intro move selected
            cases Option.some.inj selected
            exact ⟨rfl, fun _ => continues action rfl⟩
  · refine ⟨⟨⟨none, active⟩, ?_⟩⟩
    intro move impossible
    cases impossible

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
