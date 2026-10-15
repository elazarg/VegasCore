/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryProtocol
import GameTheory.Protocol.OwnPlayRecall
import GameTheory.Protocol.BehavioralAssessment

/-! # Source recovery information with complete observed attempt recall -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

def commitRecoveryPublic : setup.commitRecoveryProtocol.State → Finset Player × Nat × Nat
  | none => (∅, 0, 0)
  | some state => (state.excluded, state.generation,
      instructionCount setup.program - ProtocolState.remaining setup.program state.saved)

def commitRecoveryPrivate (who : Player) (state : setup.commitRecoveryProtocol.State) :
    setup.ProtocolView who := state.map (fun current =>
      ProtocolState.observe who setup.program current.point)

/-- The auxiliary source game retains the whole observed attempt transcript.
Only the observer's source view, permanent exclusions and public phase identity
are emitted. Hidden foreign bindings are never part of a signal. -/
def commitRecoverySignals : InfoSignals setup.commitRecoveryProtocol where
  PublicSignal := Finset Player × Nat × Nat
  PrivateSignal := setup.ProtocolView
  initialPublic := (∅, 0, 0)
  initialPrivate _ := none
  publicSignal event := setup.commitRecoveryPublic event.target
  privateSignal who event := setup.commitRecoveryPrivate who event.target
  InfoState who := (setup.ProtocolView who × (Finset Player × Nat × Nat)) ×
    List (setup.ProtocolView who × (Finset Player × Nat × Nat))
  initInfo _ view publicView := ((view, publicView), [])
  pushInfo _ prior _ view publicView := ((view, publicView), prior.1 :: prior.2)

theorem commitRecoverySignals_current (who : Player) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state),
      ((setup.commitRecoverySignals).infoOf who trace).1 =
        (setup.commitRecoveryPrivate who state, setup.commitRecoveryPublic state)
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def commitRecoveryActive (who : Player)
    (signal : setup.ProtocolView who × (Finset Player × Nat × Nat)) : Prop :=
  signal.1.elim False (fun view =>
    ProtocolView.actor who setup.program view = some who ∧ who ∉ signal.2.1)

def commitRecoveryMenu (who : Player)
    (information : (setup.commitRecoverySignals).withOwnPlayRecall.InfoState who)
    (choice : Option (CommitRecoveryMove Player L)) : Prop :=
  match choice with
  | none => ¬ setup.commitRecoveryActive who information.1.1
  | some move => setup.commitRecoveryActive who information.1.1 ∧
      information.1.1.1.elim False (fun view =>
        move ∈ ProtocolView.recoveryAvailable who setup.program view)

theorem commitRecoveryMenu_adequate (who : Player)
    {state : setup.commitRecoveryProtocol.State} (trace : setup.commitRecoveryProtocol.Trace state)
    (choice : Option (CommitRecoveryMove Player L)) :
    setup.commitRecoveryMenu who
      ((setup.commitRecoverySignals).withOwnPlayRecall.infoOf who trace) choice ↔
        LegalOption setup.commitRecoveryProtocol state who choice := by
  rw [InfoSignals.withOwnPlayRecall_infoOf]
  unfold commitRecoveryMenu
  rw [setup.commitRecoverySignals_current who trace]
  cases state with
  | none => cases choice <;> rfl
  | some current =>
      cases choice <;>
        simp only [commitRecoveryActive, commitRecoveryPrivate, commitRecoveryPublic,
          Option.map_some, Option.elim_some, ProtocolState.actor_observe_eq, LegalOption,
          commitRecoveryProtocol, CommitRecoveryState.Active, CommitRecoveryState.available]

/-- The complete recovery source game, including one private setup draw and
all observable retries, has exactly the original source-local choice menus. -/
def commitRecoveryModel : InformationModel setup.commitRecoveryProtocol where
  toInfoSignals := (setup.commitRecoverySignals).withOwnPlayRecall
  menu := setup.commitRecoveryMenu
  menu_adequate := setup.commitRecoveryMenu_adequate

theorem commitRecoveryModel_perfectRecall : setup.commitRecoveryModel.PerfectRecall :=
  (setup.commitRecoverySignals).withOwnPlayRecall_perfectRecall

theorem commitRecoveryModel_decisionAntichain :
    setup.commitRecoveryModel.DecisionInformationAntichain :=
  setup.commitRecoveryModel.decisionInformationAntichain_of_perfectRecall
    setup.commitRecoveryModel_perfectRecall

end Vegas.SourceProgram.Setup
