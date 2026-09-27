/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.Payoffs
import Vegas.Examples.MonitoredGuessing.Source
import Vegas.Examples.MonitoredGuessing.RestrictedSourceValues

/-! # The actual source protocol for each declared return table

Terminal return expressions affect settlement but are not strategic actions.
For this program family, the complete execution protocol and information model
are equal. Thus histories, behavioral policies, assessments, and consistency
proofs require only equality transport, with no new source executor.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.SourceProgram GameTheory.Protocol GameTheory.Math.Probability

def payoffAdmission (table : PayoffTable) : CommitmentInterface (payoffProgram table) :=
  CommitmentInterface.forfeiture (payoffProgram table)

theorem payoffSetup_step (table : PayoffTable) :
    (payoffSetup table).protocolStep = sourceSetup.protocolStep := by
  funext state joint
  cases state with
  | none => rfl
  | some state =>
      cases state with
      | inl config => rfl
      | inr rest => cases rest <;> rfl

theorem payoffSetup_protocol (table : PayoffTable) :
    (payoffSetup table).executionProtocol (payoffAdmission table) = sourceArena := by
  unfold Setup.executionProtocol sourceArena
  congr 1
  rw [payoffSetup_step]
  rfl

theorem payoffSetup_information (table : PayoffTable) :
    HEq ((payoffSetup table).informationModel (payoffAdmission table)) sourceModel := by
  let arena (kernel : sourceSetup.ProtocolState →
      (Player → Option (OwnAction Player simpleExpr)) → FinDist sourceSetup.ProtocolState) :
      ExecutionProtocol Player :=
    { sourceArena with step state joint := kernel state joint.val }
  let signals kernel : InfoSignals (arena kernel) := {
    PublicSignal := Unit
    PrivateSignal := sourceSetup.ProtocolView
    initialPublic := ()
    initialPrivate := fun _ => none
    publicSignal := fun _ => ()
    privateSignal := fun who event => sourceSetup.protocolObserve who event.target
    InfoState := sourceSetup.ProtocolView
    initInfo := fun _ view _ => view
    pushInfo := fun _ _ _ view _ => view }
  let model kernel : InformationModel (arena kernel) := {
    toInfoSignals := signals kernel
    menu := fun who view => {choice | sourceSetup.protocolMenu sourceAdmission who view choice}
    menu_adequate := by
      intro who state trace choice
      have observed : (signals kernel).infoOf who trace =
          sourceSetup.protocolObserve who state := by cases trace <;> rfl
      rw [observed]
      cases state <;> cases choice <;>
        simp [Setup.protocolMenu, Setup.protocolObserve, ProtocolView.menu, LegalOption,
          arena, sourceArena, Setup.executionProtocol] }
  have base : model sourceSetup.protocolStep = sourceModel := by rfl
  have changed : HEq ((payoffSetup table).informationModel (payoffAdmission table))
      (model (payoffSetup table).protocolStep) := by
    unfold Setup.informationModel Setup.protocolSignals model signals
    dsimp only
    congr 1
    funext who view
    cases view with
    | none => rfl
    | some view => cases view with
      | inl config => rfl
      | inr rest => cases rest <;> rfl
  apply changed.trans
  rw [payoffSetup_step, base]

/-- Equality of the complete protocol/information pair transports every
assessment property, including standard sequential consistency. -/
theorem payoffSetup_model_pair (table : PayoffTable) :
    (⟨(payoffSetup table).executionProtocol (payoffAdmission table),
      (payoffSetup table).informationModel (payoffAdmission table)⟩ :
        Σ arena : ExecutionProtocol Player, InformationModel arena) =
      ⟨sourceArena, sourceModel⟩ :=
  Sigma.ext (payoffSetup_protocol table) (payoffSetup_information table)

/-- Read the player's actual integer return from this family's unique entry.
No return is paid before the source program reaches its terminal position. -/
def declaredSourceUtility (table : PayoffTable)
    (state : (payoffSetup table).ProtocolState) (who : Player) : ℝ :=
  (((payoffSetup table).protocolReadout state).bind fun terminal =>
    ((payoffProgram table).evaluatePayoffs terminal).lookup who).getD 0

theorem declaredSourceUtility_eq (table : PayoffTable)
    (state : (payoffSetup table).ProtocolState) (who : Player) :
    declaredSourceUtility table state who = match state with
      | some (.inr (.inr config)) => (table (sourceResults config.state) who : ℝ)
      | _ => 0 := by
  cases state with
  | none => exact Int.cast_zero
  | some state => cases state with
    | inl config => exact Int.cast_zero
    | inr rest => cases rest with
      | inl config => exact Int.cast_zero
      | inr config =>
          change (((((payoffProgram table).evaluatePayoffs config.state).lookup who).getD 0 :
            Int) : ℝ) = _
          rw [payoffProgram_settlement]
          fin_cases who <;> rfl

theorem declaredSourceUtility_eq_result (table : PayoffTable)
    (state : (payoffSetup table).ProtocolState) :
    declaredSourceUtility table state =
      Restricted.sourceResultUtility (fun result who => (table result who : ℝ)) state := by
  funext who
  rw [declaredSourceUtility_eq]
  cases state with
  | none => rfl
  | some state => cases state with
    | inl config => rfl
    | inr rest => cases rest <;> rfl

instance (table : PayoffTable) :
    Finite ((payoffSetup table).executionProtocol (payoffAdmission table)).History := by
  rw [payoffSetup_protocol]
  infer_instance

instance (table : PayoffTable) (who : Player)
    (site : ((payoffSetup table).informationModel (payoffAdmission table)).InformationSite who) :
    Fintype (((payoffSetup table).informationModel (payoffAdmission table)).InformationHistory
      who site.1) := Fintype.ofFinite _

theorem payoffAntichain (table : PayoffTable) :
    ((payoffSetup table).informationModel (payoffAdmission table)).DecisionInformationAntichain :=
  (congrArg (fun pair : Σ arena : ExecutionProtocol Player, InformationModel arena =>
    pair.2.DecisionInformationAntichain) (payoffSetup_model_pair table)).mpr sourceAntichain

end Vegas.Examples.MonitoredGuessing
