/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryInformationEmbedding
import Vegas.Source.ProposalRecoveryOrdinaryCommit
import Vegas.Game.CommitRecoveryRestriction

/-! # Structural intended-source restriction of proposal-labeled recovery -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProposalRecoveryMove

def lift (choice : Option (OwnAction Player L)) : Option (ProposalRecoveryMove Player L) :=
  (CommitRecoveryMove.lift choice).map ordinary

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem lift_injective : Function.Injective (lift (Player := Player) (L := L)) := by
  intro first second equal
  apply CommitRecoveryMove.lift_injective
  have semantic := congrArg (Option.map ProposalRecoveryMove.semantic) equal
  simp only [lift, Option.map_map, Function.comp_def, ordinary_semantic] at semantic
  change (CommitRecoveryMove.lift first).map id =
    (CommitRecoveryMove.lift second).map id at semantic
  simpa only [Option.map_id, id_eq] using semantic

end ProposalRecoveryMove

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

private theorem retained_excluded (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.intendedModel.InfoState who) :
    (setup.proposalRecoveryRetainedInformation wellFormed who view).1.1.2.1.1 = ∅ := by
  classical
  unfold proposalRecoveryRetainedInformation
  split
  · next witness =>
      have clear := setup.commitRecoveryLiftHistory_clear wellFormed witness.choose
      change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who
        (setup.proposalRecoveryIntendedLift wellFormed witness.choose).trace).1.1.2.1.1 = ∅
      rw [InfoSignals.withOwnPlayRecall_infoOf]
      have control := congrArg (fun signal => signal.2.1)
        (setup.proposalRecoverySignals_control who
          (setup.proposalRecoveryIntendedLift wellFormed witness.choose).trace)
      dsimp only [Prod.fst, Prod.snd] at control
      refine control.trans ?_
      change (setup.commitRecoveryPublic
        (setup.commitRecoveryLiftHistory wellFormed witness.choose).state).1 = ∅
      cases current : (setup.commitRecoveryLiftHistory wellFormed witness.choose).state with
      | none => rfl
      | some current =>
          rw [current] at clear
          exact clear
  · rfl

theorem proposalRecoveryInformation_menu (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.intendedModel.InfoState who) (choice : Option (OwnAction Player L))
    (permitted : choice ∈ setup.intendedModel.menu who view) :
    ProposalRecoveryMove.lift choice ∈ setup.proposalRecoveryModel.menu who
      (setup.proposalRecoveryInformation wellFormed who view) := by
  have current := setup.proposalRecoveryRetainedInformation_current wellFormed who view
  have excluded := setup.retained_excluded wellFormed who view
  change choice ∈ setup.intendedMenu who view at permitted
  change setup.proposalRecoveryMenu who
    (setup.proposalRecoveryRetainedInformation wellFormed who view)
      (ProposalRecoveryMove.lift choice)
  cases choice with
  | none =>
      change ¬ setup.commitRecoveryActive who _
      unfold commitRecoveryActive
      dsimp only [Prod.fst, Prod.snd]
      rw [current]
      cases view with
      | none => exact not_false
      | some view => exact fun active => permitted active.1
  | some action =>
      change setup.commitRecoveryActive who _ ∧ _
      unfold commitRecoveryActive
      dsimp only [Prod.fst, Prod.snd]
      rw [current, excluded]
      cases view with
      | none => cases permitted
      | some view =>
          simp only [Option.elim_some, Finset.notMem_empty, not_false_eq_true, and_true]
          refine ⟨permitted.1, ⟨?_, ?_⟩⟩
          · refine ⟨ProtocolView.intendedAvailable_subset who setup.program
                (CommitmentInterface.forfeiture setup.program) view permitted.2, ?_⟩
            split
            · intro impossible; cases impossible
            · rfl
          · exact ProposalRecoveryMove.ordinary_valid _

def proposalRecoveryChoice (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.intendedModel.InfoState who) :
    setup.intendedModel.Choice who view ↪
      setup.proposalRecoveryModel.Choice who
        (setup.proposalRecoveryInformation wellFormed who view) where
  toFun choice := ⟨ProposalRecoveryMove.lift choice.1,
    setup.proposalRecoveryInformation_menu wellFormed who view choice.1 choice.2⟩
  inj' := by
    intro first second same
    apply Subtype.ext
    exact ProposalRecoveryMove.lift_injective (congrArg Subtype.val same)

/-- The labeled lift uses exactly the old operational kernel. The added
proposal record is read from the SAME pre-state and does not change chance. -/
theorem proposalRecoveryIntendedLift_step (wellFormed : setup.WellFormed)
    (original : setup.intendedProtocol.History) (joint : Player → Option (OwnAction Player L))
    (legal : setup.intendedProtocol.Legal original.state joint)
    (targetLegal : setup.proposalRecoveryProtocol.Legal
      (setup.proposalRecoveryIntendedLift wellFormed original).state
      (fun who => ProposalRecoveryMove.lift (joint who))) :
    setup.proposalRecoveryProtocol.step
        (setup.proposalRecoveryIntendedLift wellFormed original).state
        ⟨(fun who => ProposalRecoveryMove.lift (joint who)), targetLegal⟩ =
      (setup.intendedProtocol.step original.state ⟨joint, legal⟩).map
        (setup.commitRecoveryLiftSuccessor
          (setup.commitRecoveryLiftHistory wellFormed original).state
          (setup.commitRecoveryLiftHistory_clear wellFormed original)) := by
  have semantic : proposalRecoveryJoint (fun who => ProposalRecoveryMove.lift (joint who)) =
      fun who => CommitRecoveryMove.lift (joint who) := by
    funext who
    simp only [proposalRecoveryJoint, ProposalRecoveryMove.lift, Option.map_map,
      Function.comp_def, ProposalRecoveryMove.ordinary_semantic]
    change (CommitRecoveryMove.lift (joint who)).map id = _
    simpa only [id_eq] using congrFun Option.map_id (CommitRecoveryMove.lift (joint who))
  have oldLegal := setup.proposalRecovery_erase_legal
    (fun who => ProposalRecoveryMove.lift (joint who)) targetLegal
  rw [semantic] at oldLegal
  change setup.commitRecoveryProtocol.step _ ⟨_, _⟩ = _
  have inputEqual :
      (⟨proposalRecoveryJoint (fun who => ProposalRecoveryMove.lift (joint who)),
          targetLegal.1, setup.proposalRecoveryJoint_legal _ targetLegal.2⟩ :
        {actions // setup.commitRecoveryProtocol.Legal
          (setup.commitRecoveryLiftHistory wellFormed original).state actions}) =
        ⟨(fun who => CommitRecoveryMove.lift (joint who)), oldLegal⟩ :=
    Subtype.ext semantic
  rw [inputEqual]
  exact setup.commitRecoveryLiftHistory_step wellFormed original joint legal oldLegal

private theorem recovery_choice_cast_val (who : Player)
    {first second : setup.proposalRecoveryModel.InfoState who} (same : first = second)
    (choice : setup.proposalRecoveryModel.Choice who first) :
    (Eq.mp (congrArg (setup.proposalRecoveryModel.Choice who) same) choice).1 = choice.1 := by
  cases same
  rfl

/-- The full history law commutes with the embedding for every pure local
choice, without assuming a profile or an equilibrium. -/
theorem proposalRecovery_localStep (wellFormed : setup.WellFormed)
    (original : setup.intendedProtocol.History)
    (choices : ∀ who, setup.intendedModel.Choice who
      (setup.intendedModel.infoOf who original.trace)) :
    (setup.intendedModel.localStep original choices).map
        (setup.proposalRecoveryIntendedLift wellFormed) =
      setup.proposalRecoveryModel.localStep (setup.proposalRecoveryIntendedLift wellFormed original)
        (fun who => Eq.mp (congrArg (setup.proposalRecoveryModel.Choice who)
          (setup.proposalRecoveryInformation_observed wellFormed who original).symm)
          (setup.proposalRecoveryChoice wellFormed who
            (setup.intendedModel.infoOf who original.trace) (choices who))) := by
  classical
  let target := setup.proposalRecoveryIntendedLift wellFormed original
  let targetChoices := fun who => Eq.mp (congrArg (setup.proposalRecoveryModel.Choice who)
    (setup.proposalRecoveryInformation_observed wellFormed who original).symm)
    (setup.proposalRecoveryChoice wellFormed who
      (setup.intendedModel.infoOf who original.trace) (choices who))
  change (setup.intendedModel.localStep original choices).map
    (setup.proposalRecoveryIntendedLift wellFormed) =
      setup.proposalRecoveryModel.localStep target targetChoices
  by_cases stopped : setup.intendedProtocol.terminal original.state
  · have targetStopped : setup.proposalRecoveryProtocol.terminal target.state :=
      (setup.commitRecoveryLiftHistory_terminal wellFormed original).mpr stopped
    simp only [InformationModel.localStep, dite_eq_left stopped, dite_eq_left targetStopped,
      PMF.pure_map]
    rfl
  · have targetRunning : ¬ setup.proposalRecoveryProtocol.terminal target.state :=
      fun ended => stopped ((setup.commitRecoveryLiftHistory_terminal wellFormed original).mp ended)
    let joint := fun who => (choices who).1
    have sourceLegal : setup.intendedProtocol.Legal original.state joint :=
      legal_of_legalOption stopped fun who =>
        (setup.intendedModel.menu_adequate who original.trace _).mp (choices who).2
    have targetValues (who : Player) : (targetChoices who).1 =
        ProposalRecoveryMove.lift (joint who) := by
      exact setup.recovery_choice_cast_val who
        (setup.proposalRecoveryInformation_observed wellFormed who original).symm _
    have targetLegal : setup.proposalRecoveryProtocol.Legal target.state
        (fun who => ProposalRecoveryMove.lift (joint who)) :=
      legal_of_legalOption targetRunning fun who => by
        rw [← targetValues]
        exact (setup.proposalRecoveryModel.menu_adequate who target.trace _).mp
          (targetChoices who).2
    rw [setup.intendedModel.localStep_eq_of_joint original choices stopped joint sourceLegal
      (fun _ => rfl)]
    rw [setup.proposalRecoveryModel.localStep_eq_of_joint target targetChoices targetRunning
      (fun who => ProposalRecoveryMove.lift (joint who)) targetLegal targetValues]
    let raw := setup.proposalRecoveryProtocol.step target.state
      ⟨(fun who => ProposalRecoveryMove.lift (joint who)), targetLegal⟩
    let next := fun point : setup.proposalRecoveryProtocol.State =>
      if supported : point ∈ raw.support then
        PMF.pure (target.extend targetLegal supported) else PMF.pure target
    have ordinary : raw.bindOnSupport
        (fun _ supported => PMF.pure (target.extend targetLegal supported)) = raw.bind next := by
      apply bindOnSupport_eq_bind_of_eq_on_support
      intro point supported
      simp only [next, dite_eq_left supported]
    have kernel : raw = (setup.intendedProtocol.step original.state ⟨joint, sourceLegal⟩).map
        (setup.commitRecoveryLiftSuccessor target.state
          (setup.commitRecoveryLiftHistory_clear wellFormed original)) :=
      setup.proposalRecoveryIntendedLift_step wellFormed original joint sourceLegal targetLegal
    rw [ordinary, kernel, PMF.bind_map, map_bindOnSupport]
    apply bindOnSupport_eq_bind_of_eq_on_support
    intro after supported
    rw [PMF.pure_map]
    have targetSupported : setup.commitRecoveryLiftSuccessor target.state
        (setup.commitRecoveryLiftHistory_clear wellFormed original) after ∈ raw.support := by
      rw [kernel]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨after, supported, rfl⟩
    simp only [Function.comp_apply, next, dite_eq_left targetSupported]
    congr 1
    simp only [target, proposalRecoveryIntendedLift, commitRecoveryLiftHistory,
      History.extend, commitRecoveryLiftTrace, proposalRecoveryLiftTrace, ProposalRecoveryMove.lift]
    congr 2
    funext who
    simp only [proposalRecoveryLiftJoint, ProposalRecoveryMove.label_false]

/-- The intended game embeds structurally into the actual auxiliary recovery
game with its full observed transcript and own-play information. -/
def proposalRecoveryRestriction (wellFormed : setup.WellFormed) :
    setup.intendedModel.ActionRestriction setup.proposalRecoveryModel where
  history := ⟨setup.proposalRecoveryIntendedLift wellFormed,
    (by
      intro first second equal
      apply setup.commitRecoveryLiftHistory_injective wellFormed
      have erased := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
        (⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩ :
          setup.commitRecoveryProtocol.History)) equal
      simpa only [proposalRecoveryIntendedLift,
        setup.proposalRecoveryEraseTrace_lift] using erased)⟩
  information := setup.proposalRecoveryInformation wellFormed
  choice := setup.proposalRecoveryChoice wellFormed
  initial := rfl
  length := (by
    intro original
    change (setup.proposalRecoveryLiftTrace (fun _ _ => false)
      (setup.commitRecoveryLiftHistory wellFormed original).trace).length = _
    rw [setup.proposalRecoveryLiftTrace_length]
    exact setup.commitRecoveryLiftHistory_length wellFormed original)
  terminal := setup.commitRecoveryLiftHistory_terminal wellFormed
  active := setup.commitRecoveryLiftHistory_active wellFormed
  observed := setup.proposalRecoveryInformation_observed wellFormed
  step := setup.proposalRecovery_localStep wellFormed

theorem proposalRecovery_choiceAt_val (wellFormed : setup.WellFormed) (who : Player)
    (original : setup.intendedProtocol.History)
    (choice : setup.intendedModel.Choice who (setup.intendedModel.infoOf who original.trace)) :
    ((setup.proposalRecoveryRestriction wellFormed).choiceAt who original choice).val =
      ProposalRecoveryMove.lift choice.val := by
  change (Eq.mp (congrArg (setup.proposalRecoveryModel.Choice who)
    (setup.proposalRecoveryInformation_observed wellFormed who original).symm)
    (setup.proposalRecoveryChoice wellFormed who
      (setup.intendedModel.infoOf who original.trace) choice)).val = _
  exact setup.recovery_choice_cast_val who
    (setup.proposalRecoveryInformation_observed wellFormed who original).symm _

end Setup
end Vegas.SourceProgram
