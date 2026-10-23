/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryObservation

/-! # Complete source recall of proposal-labeled recovery -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

def proposalRecoverySignals : InfoSignals setup.proposalRecoveryProtocol where
  PublicSignal := (Finset Player × Nat × Nat) × Option (ProposalRecoveryProposal L)
  PrivateSignal := setup.ProtocolView
  initialPublic := ((∅, 0, 0), none)
  initialPrivate _ := none
  publicSignal := setup.proposalRecoveryPublic
  privateSignal who event := setup.commitRecoveryPrivate who event.target
  InfoState who :=
    (setup.ProtocolView who ×
      ((Finset Player × Nat × Nat) × Option (ProposalRecoveryProposal L))) ×
    List (setup.ProtocolView who ×
      ((Finset Player × Nat × Nat) × Option (ProposalRecoveryProposal L)))
  initInfo _ view publicView := ((view, publicView), [])
  pushInfo _ prior _ view publicView := ((view, publicView), prior.1 :: prior.2)

theorem proposalRecoverySignals_control (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    let signal := (setup.proposalRecoverySignals.infoOf who trace).1
    (signal.1, signal.2.1) =
      (setup.commitRecoveryPrivate who state, setup.commitRecoveryPublic state) := by
  cases trace <;> rfl

def proposalRecoveryActive (who : Player)
    (signal : setup.ProtocolView who ×
      ((Finset Player × Nat × Nat) × Option (ProposalRecoveryProposal L))) : Prop :=
  setup.commitRecoveryActive who (signal.1, signal.2.1)

def proposalRecoveryMenu (who : Player)
    (information : setup.proposalRecoverySignals.withOwnPlayRecall.InfoState who)
    (choice : Option (ProposalRecoveryMove Player L)) : Prop :=
  match choice with
  | none => ¬ setup.proposalRecoveryActive who information.1.1
  | some move => setup.proposalRecoveryActive who information.1.1 ∧
      information.1.1.1.elim False (fun view =>
        move.semantic ∈ ProtocolView.recoveryAvailable who setup.program view ∧ move.Valid)

theorem proposalRecoveryMenu_adequate (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state)
    (choice : Option (ProposalRecoveryMove Player L)) :
    setup.proposalRecoveryMenu who
      (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who trace) choice ↔
      LegalOption setup.proposalRecoveryProtocol state who choice := by
  rw [InfoSignals.withOwnPlayRecall_infoOf]
  have current := setup.proposalRecoverySignals_control who trace
  cases choice with
  | none =>
      change (¬ setup.commitRecoveryActive who _) ↔ _
      rw [current]
      cases state with
      | none => rfl
      | some state =>
          simp only [commitRecoveryActive, commitRecoveryPrivate, commitRecoveryPublic,
            Option.map_some, Option.elim_some, ProtocolState.actor_observe_eq, LegalOption,
            proposalRecoveryProtocol, commitRecoveryProtocol, CommitRecoveryState.Active]
  | some move =>
      change (setup.commitRecoveryActive who _ ∧ _) ↔ _
      have viewEq := congrArg Prod.fst current
      rw [current, viewEq]
      cases state with
      | none =>
          simp [commitRecoveryActive, commitRecoveryPrivate, commitRecoveryPublic, LegalOption,
            proposalRecoveryProtocol, proposalRecoveryAvailable, commitRecoveryProtocol]
      | some state =>
          simp only [commitRecoveryActive, commitRecoveryPrivate, commitRecoveryPublic,
            Option.map_some, Option.elim_some, ProtocolState.actor_observe_eq, LegalOption,
            proposalRecoveryProtocol, proposalRecoveryAvailable, commitRecoveryProtocol,
            CommitRecoveryState.Active, CommitRecoveryState.available, Set.mem_ofPred_eq]

def proposalRecoveryModel : InformationModel setup.proposalRecoveryProtocol where
  toInfoSignals := setup.proposalRecoverySignals.withOwnPlayRecall
  menu := setup.proposalRecoveryMenu
  menu_adequate := setup.proposalRecoveryMenu_adequate

theorem proposalRecoveryModel_perfectRecall : setup.proposalRecoveryModel.PerfectRecall :=
  setup.proposalRecoverySignals.withOwnPlayRecall_perfectRecall

theorem proposalRecoveryModel_decisionAntichain :
    setup.proposalRecoveryModel.DecisionInformationAntichain :=
  setup.proposalRecoveryModel.decisionInformationAntichain_of_perfectRecall
    setup.proposalRecoveryModel_perfectRecall

/-- The archive is an observed word, not independent semantic recovery state. -/
def proposalRecoveryProposalWord (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who) :
    List (ProposalRecoveryProposal L) :=
  ((information.1.1 :: information.1.2).filterMap fun signal => signal.2.2).reverse

@[simp] theorem proposalRecoveryProposalWord_start (who : Player) :
    setup.proposalRecoveryProposalWord who
      (setup.proposalRecoveryModel.infoOf who (.start :
        setup.proposalRecoveryProtocol.Trace
          setup.proposalRecoveryProtocol.init)) = [] := rfl

theorem proposalRecoveryProposalWord_extend (who : Player)
    {before after : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace before)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support) :
    setup.proposalRecoveryProposalWord who
        (setup.proposalRecoveryModel.infoOf who (.extend trace joint legal supported)) =
      setup.proposalRecoveryProposalWord who (setup.proposalRecoveryModel.infoOf who trace) ++
        (setup.proposalRecoveryProposalOf before joint).toList := by
  simp only [proposalRecoveryProposalWord, proposalRecoveryModel,
    InfoSignals.withOwnPlayRecall_infoOf,
    InfoSignals.infoOf, proposalRecoverySignals, proposalRecoveryPublic, List.filterMap_cons]
  cases setup.proposalRecoveryProposalOf before joint <;> simp

/-- The canonical proposal observation forgets physical completion order. -/
def proposalRecoveryArchive (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who) :
    Finset (ProposalRecoveryProposal L) :=
  (setup.proposalRecoveryProposalWord who information).toFinset

@[simp] theorem proposalRecoveryArchive_start (who : Player) :
    setup.proposalRecoveryArchive who
      (setup.proposalRecoveryModel.infoOf who (.start :
        setup.proposalRecoveryProtocol.Trace setup.proposalRecoveryProtocol.init)) = ∅ := rfl


end Vegas.SourceProgram.Setup
