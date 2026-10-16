/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

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

/-- All original actions remain in the reduced chronological record. Only
their information labels are erased; accepted failures are not dropped. -/
theorem commitRecoveryErasedModel_ownPlay (who : Player) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state),
      setup.commitRecoveryErasedModel.ownPlay who trace =
        (setup.commitRecoveryModel.ownPlay who trace).map fun record =>
          (setup.commitRecoveryErasedInformation who record.1, record.2)
  | _, .start => rfl
  | _, .extend prior joint legal supported => by
      simp only [InfoSignals.ownPlay_extend, setup.commitRecoveryErasedModel_infoOf,
        commitRecoveryErasedModel_ownPlay who prior]
      cases joint who <;> rfl

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

theorem commitRecoveryErasedModel_record_word_length_lt (who : Player) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state)
      (info : setup.commitRecoveryErasedModel.InfoState who),
      info ∈ setup.commitRecoveryErasedModel.actedAt who trace → info.1.2.length < trace.length
  | _, .start, _, member => by cases member
  | _, .extend prior joint legal supported, info, member => by
      cases chosen : joint who with
      | none =>
          simp only [InfoSignals.actedAt, chosen] at member
          have earlier := commitRecoveryErasedModel_record_word_length_lt who prior info member
          change info.1.2.length < prior.length + 1
          omega
      | some action =>
          simp only [InfoSignals.actedAt, chosen, List.mem_cons] at member
          change info.1.2.length < prior.length + 1
          rcases member with rfl | earlier
          · rw [setup.commitRecoveryErasedModel_word_length]
            omega
          · have shorter := commitRecoveryErasedModel_record_word_length_lt who prior info earlier
            omega

/-- No genuine source path queries a reduced coordinate twice, even across
retries or an exhausted restore with unchanged generation. -/
theorem commitRecoveryErasedModel_actsOnce :
    setup.commitRecoveryErasedModel.ActsOnceAtEachInfoState := by
  intro who state trace
  induction trace with
  | start => exact List.nodup_nil
  | extend prior joint legal supported ih =>
      cases chosen : joint who with
      | none => simpa only [InfoSignals.actedAt, chosen] using ih
      | some action =>
          simp only [InfoSignals.actedAt, chosen, List.nodup_cons]
          refine ⟨?_, ih⟩
          intro member
          have shorter := setup.commitRecoveryErasedModel_record_word_length_lt who prior _ member
          rw [setup.commitRecoveryErasedModel_word_length] at shorter
          exact Nat.lt_irrefl _ shorter

/-- Read the original table at a reduced label and transport menu membership
back to the actual full source information state. -/
def commitRecoveryErasedPolicy (who : Player)
    (policy : setup.commitRecoveryErasedModel.Policy who) : setup.commitRecoveryModel.Policy who :=
  fun info => (setup.commitRecoveryErasedChoice who info).symm
    (policy (setup.commitRecoveryErasedInformation who info))

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

theorem commitRecoveryErasedProfile_congr
    (profile : ∀ who, setup.commitRecoveryErasedModel.BehavioralPolicy who)
    (who : Player) (first second : setup.commitRecoveryModel.InfoState who)
    (same : setup.commitRecoveryErasedInformation who first =
      setup.commitRecoveryErasedInformation who second) :
    (setup.commitRecoveryErasedProfile profile who first).map Subtype.val =
      (setup.commitRecoveryErasedProfile profile who second).map Subtype.val := by
  rw [setup.commitRecoveryErasedProfile_raw, setup.commitRecoveryErasedProfile_raw, same]

theorem commitRecoveryErasedPolicy_congr (who : Player)
    (policy : setup.commitRecoveryErasedModel.Policy who)
    (first second : setup.commitRecoveryModel.InfoState who)
    (same : setup.commitRecoveryErasedInformation who first =
      setup.commitRecoveryErasedInformation who second) :
    (setup.commitRecoveryErasedPolicy who policy first).val =
      (setup.commitRecoveryErasedPolicy who policy second).val := by
  change (policy (setup.commitRecoveryErasedInformation who first)).val =
    (policy (setup.commitRecoveryErasedInformation who second)).val
  rw [same]

end Setup
end Vegas.SourceProgram
