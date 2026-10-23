/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryErasure

/-! # Reduced decision coordinates on the original recovery protocol

This analytical information carrier indexes shared random choices. Strategies
are lifted back to the original full-information game; no player's actual
observations or recall are changed.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- A recursive coordinate carrier retains the live typed view and every past
public signal, while discarding private retired words and own-play tags. -/
def commitRecoveryErasedSignals : InfoSignals setup.commitRecoveryProtocol where
  PublicSignal := setup.commitRecoverySignals.PublicSignal
  PrivateSignal := setup.commitRecoverySignals.PrivateSignal
  initialPublic := setup.commitRecoverySignals.initialPublic
  initialPrivate := setup.commitRecoverySignals.initialPrivate
  publicSignal := setup.commitRecoverySignals.publicSignal
  privateSignal := setup.commitRecoverySignals.privateSignal
  InfoState := setup.commitRecoveryModel.InfoState
  initInfo who view publicView :=
    (((view.map (ProtocolView.eraseHistory who setup.program), publicView), []), [])
  pushInfo who prior _ view publicView :=
    (((view.map (ProtocolView.eraseHistory who setup.program), publicView),
      (prior.1.1.1.map (ProtocolView.publicOnly who setup.program), prior.1.1.2) :: prior.1.2), [])

/-- Reduced coordinates are derived from the actual complete source trace.
The erased representative need not itself be original played information. -/
theorem commitRecoveryErasedSignals_infoOf (who : Player) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state),
      setup.commitRecoveryErasedSignals.infoOf who trace =
        setup.commitRecoveryErasedInformation who (setup.commitRecoveryModel.infoOf who trace)
  | _, .start => rfl
  | _, .extend prior joint legal supported => by
      rw [InfoSignals.infoOf_extend, commitRecoveryErasedSignals_infoOf who prior]
      simp only [commitRecoveryErasedSignals, commitRecoveryErasedInformation,
        commitRecoveryModel, InfoSignals.infoOf_extend,
        InfoSignals.withOwnPlayRecall, commitRecoverySignals, List.map_cons,
        Option.map_map, Function.comp_def, ProtocolView.publicOnly_eraseHistory]

/-- This auxiliary model is used only to sample shared coordinates; its menus
are exactly those of the original full-information source game. -/
def commitRecoveryErasedModel : InformationModel setup.commitRecoveryProtocol where
  toInfoSignals := setup.commitRecoveryErasedSignals
  menu := setup.commitRecoveryModel.menu
  menu_adequate := by
    intro who state trace choice
    rw [setup.commitRecoveryErasedSignals_infoOf who trace,
      setup.commitRecoveryErasedInformation_menu who]
    exact setup.commitRecoveryModel.menu_adequate who trace choice

theorem commitRecoveryErasedModel_infoOf (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    setup.commitRecoveryErasedModel.infoOf who trace =
      setup.commitRecoveryErasedInformation who (setup.commitRecoveryModel.infoOf who trace) :=
  setup.commitRecoveryErasedSignals_infoOf who trace

/-- Each source transition adds one public signal, including passive steps and
attempt closure. Operational waiting is not a source transition. -/
theorem commitRecoveryErasedModel_word_length (who : Player) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state),
      (setup.commitRecoveryErasedModel.infoOf who trace).1.2.length = trace.length
  | _, .start => rfl
  | _, .extend prior joint legal supported => by
      change (setup.commitRecoveryErasedModel.infoOf who prior).1.2.length + 1 = prior.length + 1
      rw [commitRecoveryErasedModel_word_length who prior]

/-- The selected shared behavioral law remains a policy of the original game. -/
def commitRecoveryErasedProfile
    (profile : ∀ who, setup.commitRecoveryErasedModel.BehavioralPolicy who) :
    ∀ who, setup.commitRecoveryModel.BehavioralPolicy who := fun who info =>
  (profile who (setup.commitRecoveryErasedInformation who info)).map
    (setup.commitRecoveryErasedChoice who info).symm

theorem commitRecoveryErasedProfile_raw
    (profile : ∀ who, setup.commitRecoveryErasedModel.BehavioralPolicy who)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryErasedProfile profile who info).map Subtype.val =
      (profile who (setup.commitRecoveryErasedInformation who info)).map Subtype.val := by
  rw [commitRecoveryErasedProfile, PMF.map_comp]
  rfl

end Setup
end Vegas.SourceProgram
