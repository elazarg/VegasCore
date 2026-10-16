/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueAtoms
import Vegas.Game.PhaseTimingPoolPlan

/-! # Original source-value coordinates in actual binding response laws -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

omit [Fintype Player] in
/-- At one decoded source view, the immutable policy is read only at that
view. Its other coordinates cannot change the auxiliary choice law. -/
theorem phaseRecoveryValueAssessment_local (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (who : Player)
    (first second : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (view : setup.ProtocolView who) (same : first view = second view) :
    (setup.commitRecoveryValueAssessment wellFormed assessment who first).strategy who
        (setup.commitRecoveryClearInformation wellFormed who view) =
      (setup.commitRecoveryValueAssessment wellFormed assessment who second).strategy who
        (setup.commitRecoveryClearInformation wellFormed who view) := by
  simp only [Setup.commitRecoveryValueAssessment, InformationModel.BehavioralAssessment.ofStrategy,
    Function.update_self, setup.commitRecoveryValuePolicy_clear, same]

/-- The guarded canonical channel keeps its exact silent atom when the
immutable nonmissing source value changes. Its menu guard is unchanged. -/
theorem phaseRecoveryValueBindingPolicy_silence (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (who : Player)
    (first second : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who first) who event payload
          binding past view ⟨none⟩ =
      phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who second) who event payload
          binding past view ⟨none⟩ := by
  classical
  unfold phaseRecoveryBindingPolicy
  split
  · rfl
  · split
    · simp only [phaseRecoveryBindingLaw, Setup.commitRecoveryValueAssessment,
        InformationModel.BehavioralAssessment.ofStrategy, Function.update_self,
        setup.commitRecoveryValuePolicy_clear, PMF.map_comp, Function.comp_def]
      rw [PMF.map_apply, PMF.map_apply]
      apply tsum_congr
      intro choice
      by_cases missing : CommitRecoveryMove.missed choice.val
      · simp only [missing, ite_true]
      · simp only [missing, Bool.false_eq_true, ite_false]
        have notSilent (member : (setup.informationModel
            (CommitmentInterface.forfeiture setup.program)).Policy who) (serial : Nat) :
            phaseRecoveryBindingResponse setup mode runtime leaks who event payload binding serial
                (setup.commitRecoveryClearChoice wellFormed who
                  (phaseSourceView? setup mode runtime leaks who event view)
                  (member (phaseSourceView? setup mode runtime leaks who event view))).val ≠
              ⟨none⟩ := by
          change phaseRecoveryBindingResponse setup mode runtime leaks who event payload binding
            serial (CommitRecoveryMove.lift (member
              (phaseSourceView? setup mode runtime leaks who event view)).val) ≠ ⟨none⟩
          intro equal
          have transmitted := congrArg
            (fun response : (phaseApplication runtime leaks).Action =>
              response.transmission.isNone) equal
          have flag := CommitRecoveryMove.missed_lift (member
            (phaseSourceView? setup mode runtime leaks who event view)).val
          change (CommitRecoveryMove.lift (member
            (phaseSourceView? setup mode runtime leaks who event view)).val).elim false
              (·.missing) = false at flag
          simp only [phaseRecoveryBindingResponse, phaseRecoveryBindingData, flag,
            Bool.false_eq_true, ite_false, phaseBindingResponse, Option.isNone_some,
            Option.isNone_none, Bool.false_eq_true] at transmitted
        split_ifs
        all_goals first
          | exact (notSilent first _ (by symm; assumption)).elim
          | exact (notSilent second _ (by symm; assumption)).elim
          | rfl
    · rfl

end Vegas
