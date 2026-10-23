/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CommitRecoveryInformationEmbedding

/-! # Structural embedding of the intended game into source recovery -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

theorem commitRecoveryInformation_menu (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.intendedModel.InfoState who) (choice : Option (OwnAction Player L))
    (permitted : choice ∈ setup.intendedModel.menu who view) :
    CommitRecoveryMove.lift choice ∈ setup.commitRecoveryModel.menu who
      (setup.commitRecoveryInformation wellFormed who view) := by
  change setup.commitRecoveryMenu who
    (setup.commitRecoveryInformation wellFormed who view) (CommitRecoveryMove.lift choice)
  have current := setup.commitRecoveryRetainedInfo_current wellFormed who view
  have excluded := setup.commitRecoveryRetainedInfo_excluded wellFormed who view
  change choice ∈ setup.intendedMenu who view at permitted
  cases choice with
  | none =>
      change ¬ setup.commitRecoveryActive who
        (setup.commitRecoveryRetainedInfo wellFormed who view).1
      unfold commitRecoveryActive
      rw [current]
      cases view with
      | none => exact not_false
      | some view => exact fun active => permitted active.1
  | some action =>
      change setup.commitRecoveryActive who
          (setup.commitRecoveryRetainedInfo wellFormed who view).1 ∧
        (setup.commitRecoveryRetainedInfo wellFormed who view).1.1.elim False
          (fun view => (⟨action, false⟩ : CommitRecoveryMove Player L) ∈
            ProtocolView.recoveryAvailable who setup.program view)
      unfold commitRecoveryActive
      rw [current, excluded]
      cases view with
      | none => cases permitted
      | some view =>
          simp only [Option.elim_some, Finset.notMem_empty, not_false_eq_true, and_true]
          refine ⟨permitted.1, ?_⟩
          refine ⟨ProtocolView.intendedAvailable_subset who setup.program
              (CommitmentInterface.forfeiture setup.program) view permitted.2, ?_⟩
          dsimp only
          split
          · intro impossible; cases impossible
          · rfl

def commitRecoveryChoice (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.intendedModel.InfoState who) :
    setup.intendedModel.Choice who view ↪
      setup.commitRecoveryModel.Choice who
        (setup.commitRecoveryInformation wellFormed who view) where
  toFun choice := ⟨CommitRecoveryMove.lift choice.1,
    setup.commitRecoveryInformation_menu wellFormed who view choice.1 choice.2⟩
  inj' := by
    intro first second same
    apply Subtype.ext
    exact CommitRecoveryMove.lift_injective (congrArg Subtype.val same)

/-- Exact full-state kernel at an embedded history; the target carries the
actual automatically closed saved checkpoint. -/
theorem commitRecoveryLiftHistory_step (wellFormed : setup.WellFormed)
    (original : setup.intendedProtocol.History) (joint : Player → Option (OwnAction Player L))
    (legal : setup.intendedProtocol.Legal original.state joint)
    (recoveryLegal : setup.commitRecoveryProtocol.Legal
      (setup.commitRecoveryLiftHistory wellFormed original).state
      (fun who => CommitRecoveryMove.lift (joint who))) :
    setup.commitRecoveryProtocol.step
        (setup.commitRecoveryLiftHistory wellFormed original).state
        ⟨(fun who => CommitRecoveryMove.lift (joint who)), recoveryLegal⟩ =
      (setup.intendedProtocol.step original.state ⟨joint, legal⟩).map
        (setup.commitRecoveryLiftSuccessor
          (setup.commitRecoveryLiftHistory wellFormed original).state
          (setup.commitRecoveryLiftHistory_clear wellFormed original)) := by
  have projected := setup.commitRecoveryLiftHistory_source wellFormed original
  have clear := setup.commitRecoveryLiftHistory_clear wellFormed original
  have offered : setup.intendedProtocol.Legal
      (setup.commitRecoverySourceState (setup.commitRecoveryLiftHistory wellFormed original).state)
      joint := projected.symm ▸ legal
  have intended : (setup.commitRecoverySourceState
      (setup.commitRecoveryLiftHistory wellFormed original).state).elim True
      (ProtocolState.Intended setup.program) := by
    rw [projected]
    have reached := setup.intendedState_trace wellFormed original.trace
    cases state : original.state with
    | none => trivial
    | some current => simpa only [state, IntendedState, Option.elim_some] using reached
  have kernel := setup.commitRecovery_lift_step
    (setup.commitRecoveryLiftHistory wellFormed original).state clear intended joint offered
  have sourceKernel : setup.intendedProtocol.step
      (setup.commitRecoverySourceState (setup.commitRecoveryLiftHistory wellFormed original).state)
      ⟨joint, offered⟩ = setup.intendedProtocol.step original.state ⟨joint, legal⟩ := by
    change setup.protocolStep _ joint = setup.protocolStep _ joint
    rw [projected]
  rw [sourceKernel] at kernel
  exact kernel

private theorem recovery_choice_cast_val (who : Player)
    {first second : setup.commitRecoveryModel.InfoState who} (same : first = second)
    (choice : setup.commitRecoveryModel.Choice who first) :
    (Eq.mp (congrArg (setup.commitRecoveryModel.Choice who) same) choice).1 = choice.1 := by
  cases same
  rfl

/-- The full history law commutes with the embedding for every pure local
choice, without assuming a profile or an equilibrium. -/
theorem commitRecovery_localStep (wellFormed : setup.WellFormed)
    (original : setup.intendedProtocol.History)
    (choices : ∀ who, setup.intendedModel.Choice who
      (setup.intendedModel.infoOf who original.trace)) :
    (setup.intendedModel.localStep original choices).map
        (setup.commitRecoveryLiftHistory wellFormed) =
      setup.commitRecoveryModel.localStep (setup.commitRecoveryLiftHistory wellFormed original)
        (fun who => Eq.mp (congrArg (setup.commitRecoveryModel.Choice who)
          (setup.commitRecoveryInformation_observed wellFormed who original).symm)
          (setup.commitRecoveryChoice wellFormed who
            (setup.intendedModel.infoOf who original.trace) (choices who))) := by
  classical
  let target := setup.commitRecoveryLiftHistory wellFormed original
  let targetChoices := fun who => Eq.mp (congrArg (setup.commitRecoveryModel.Choice who)
    (setup.commitRecoveryInformation_observed wellFormed who original).symm)
    (setup.commitRecoveryChoice wellFormed who
      (setup.intendedModel.infoOf who original.trace) (choices who))
  change (setup.intendedModel.localStep original choices).map
    (setup.commitRecoveryLiftHistory wellFormed) =
      setup.commitRecoveryModel.localStep target targetChoices
  by_cases stopped : setup.intendedProtocol.terminal original.state
  · have targetStopped : setup.commitRecoveryProtocol.terminal target.state :=
      (setup.commitRecoveryLiftHistory_terminal wellFormed original).mpr stopped
    simp only [InformationModel.localStep, dite_eq_left stopped, dite_eq_left targetStopped,
      PMF.pure_map]
    rfl
  · have targetRunning : ¬ setup.commitRecoveryProtocol.terminal target.state :=
      fun ended => stopped ((setup.commitRecoveryLiftHistory_terminal wellFormed original).mp ended)
    let joint := fun who => (choices who).1
    have sourceLegal : setup.intendedProtocol.Legal original.state joint :=
      legal_of_legalOption stopped fun who =>
        (setup.intendedModel.menu_adequate who original.trace _).mp (choices who).2
    have targetValues (who : Player) : (targetChoices who).1 =
        CommitRecoveryMove.lift (joint who) := by
      exact setup.recovery_choice_cast_val who
        (setup.commitRecoveryInformation_observed wellFormed who original).symm _
    have targetLegal : setup.commitRecoveryProtocol.Legal target.state
        (fun who => CommitRecoveryMove.lift (joint who)) :=
      legal_of_legalOption targetRunning fun who => by
        rw [← targetValues]
        exact (setup.commitRecoveryModel.menu_adequate who target.trace _).mp
          (targetChoices who).2
    rw [setup.intendedModel.localStep_eq_of_joint original choices stopped joint sourceLegal
      (fun _ => rfl)]
    rw [setup.commitRecoveryModel.localStep_eq_of_joint target targetChoices targetRunning
      (fun who => CommitRecoveryMove.lift (joint who)) targetLegal targetValues]
    let raw := setup.commitRecoveryProtocol.step target.state
      ⟨(fun who => CommitRecoveryMove.lift (joint who)), targetLegal⟩
    let next := fun point : setup.commitRecoveryProtocol.State =>
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
      setup.commitRecoveryLiftHistory_step wellFormed original joint sourceLegal targetLegal
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

/-- The intended game embeds structurally into the actual auxiliary recovery
game with its full observed transcript and own-play information. -/
def commitRecoveryRestriction (wellFormed : setup.WellFormed) :
    setup.intendedModel.ActionRestriction setup.commitRecoveryModel where
  history := ⟨setup.commitRecoveryLiftHistory wellFormed,
    setup.commitRecoveryLiftHistory_injective wellFormed⟩
  information := setup.commitRecoveryInformation wellFormed
  choice := setup.commitRecoveryChoice wellFormed
  initial := rfl
  length := setup.commitRecoveryLiftHistory_length wellFormed
  terminal := setup.commitRecoveryLiftHistory_terminal wellFormed
  active := setup.commitRecoveryLiftHistory_active wellFormed
  observed := setup.commitRecoveryInformation_observed wellFormed
  step := setup.commitRecovery_localStep wellFormed

end Vegas.SourceProgram.Setup
