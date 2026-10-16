/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryClearChoice

/-! # Immutable ordinary source values with original fresh omission draws -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- An ordinary source policy supplies the nonmissing action. The original
auxiliary policy still draws its omission flag freshly. Other information
values keep the original policy, and no physical runtime state is added. -/
def commitRecoveryValuePolicy (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (who : Player)
    (member : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who) :
    setup.commitRecoveryModel.BehavioralPolicy who := by
  classical
  exact fun information =>
  if aligned : setup.commitRecoveryClearInformation wellFormed who information.1.1.1 =
      information then
    (profile who information).map fun choice =>
      if CommitRecoveryMove.missed choice.1 then choice else
        ⟨CommitRecoveryMove.lift (member information.1.1.1).val, by
          have legal := (setup.commitRecoveryClearChoice wellFormed who information.1.1.1
            (member information.1.1.1)).property
          change CommitRecoveryMove.lift (member information.1.1.1).val ∈
            setup.commitRecoveryModel.menu who
              (setup.commitRecoveryClearInformation wellFormed who information.1.1.1) at legal
          rw [aligned] at legal
          exact legal⟩
  else profile who information

/-- At complete clear information the member changes only the nonmissing
source action. The original omitted choice and its probability are retained. -/
theorem commitRecoveryValuePolicy_clear (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (who : Player)
    (member : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (view : setup.ProtocolView who) :
    setup.commitRecoveryValuePolicy wellFormed profile who member
        (setup.commitRecoveryClearInformation wellFormed who view) =
      (profile who (setup.commitRecoveryClearInformation wellFormed who view)).map
        (fun choice => if CommitRecoveryMove.missed choice.1 then choice else
          setup.commitRecoveryClearChoice wellFormed who view (member view)) := by
  classical
  simp only [commitRecoveryValuePolicy, setup.commitRecoveryClearInformation_current,
    dite_true]
  apply congrArg (fun encode => PMF.map encode
    (profile who (setup.commitRecoveryClearInformation wellFormed who view)))
  funext choice
  split
  · rfl
  · apply Subtype.ext
    simpa [commitRecoveryClearChoice] using
      congrArg CommitRecoveryMove.lift (congrArg (fun selected => (member selected).val)
        (setup.commitRecoveryClearInformation_current wellFormed who view))

/-- Predrawing a nonmissing value never conditions or replaces the original
omission flag, even at an unrealized clear view. -/
theorem commitRecoveryValuePolicy_clear_missing (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (who : Player)
    (member : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (view : setup.ProtocolView who) :
    (setup.commitRecoveryValuePolicy wellFormed profile who member
        (setup.commitRecoveryClearInformation wellFormed who view)).map
          (fun choice => CommitRecoveryMove.missed choice.1) =
      (profile who (setup.commitRecoveryClearInformation wellFormed who view)).map
        (fun choice => CommitRecoveryMove.missed choice.1) := by
  rw [setup.commitRecoveryValuePolicy_clear, PMF.map_comp]
  apply congrArg (fun encode => PMF.map encode
    (profile who (setup.commitRecoveryClearInformation wellFormed who view)))
  funext choice
  dsimp only [Function.comp_def]
  cases flag : CommitRecoveryMove.missed choice.1 with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact CommitRecoveryMove.missed_lift (member view).val
  | true => simp only [flag, ite_true]

private theorem resample_false {Choice : Type} (law : PMF Choice) (flag : Choice → Bool) :
    (fiberPosterior law flag false).bind (fun replacement =>
      law.map fun original => if flag original then original else replacement) = law := by
  let conditional := fiberPosterior law flag false
  calc
    _ = conditional.bind (fun replacement => (law.map flag).bind fun selected =>
        (fiberPosterior law flag selected).map
          (fun original => if flag original then original else replacement)) := by
      apply congrArg (PMF.bind conditional)
      funext replacement
      have moved := congrArg (PMF.map fun original =>
        if flag original then original else replacement) (fiberPosterior_reconstruct law flag)
      simpa only [PMF.map_bind] using moved.symm
    _ = (law.map flag).bind (fun selected => conditional.bind fun replacement =>
        (fiberPosterior law flag selected).map
          (fun original => if flag original then original else replacement)) :=
      PMF.bind_comm _ _ _
    _ = (law.map flag).bind (fiberPosterior law flag) := by
      apply bind_congr_on_support
      intro selected supported
      cases selected with
      | false =>
          calc
            _ = conditional.bind (fun replacement => PMF.pure replacement) := by
              apply bind_congr_on_support
              intro replacement _
              calc
                _ = (fiberPosterior law flag false).map (fun _ => replacement) := by
                  apply map_congr_on_support
                  intro original present
                  have observed := (mem_support_fiberPosterior supported present).1
                  simp only [observed, Bool.false_eq_true, ite_false]
                _ = _ := PMF.map_const _ _
            _ = _ := PMF.bind_pure _
      | true =>
          calc
            _ = conditional.bind (fun _ => fiberPosterior law flag true) := by
              apply bind_congr_on_support
              intro replacement _
              calc
                _ = (fiberPosterior law flag true).map id := by
                  apply map_congr_on_support
                  intro original present
                  have observed := (mem_support_fiberPosterior supported present).1
                  simp only [observed, ite_true, id_eq]
                _ = _ := PMF.map_id _
            _ = _ := PMF.bind_const _ _
    _ = _ := fiberPosterior_reconstruct law flag

/-- Sampling the original conditional ordinary choice and retaining the
original fresh omission draw reconstructs the entire auxiliary local law at
an actual clear source history. Binding failures and false openings remain. -/
theorem commitRecoveryValuePolicy_clear_mixture
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (history : setup.commitRecoveryProtocol.History)
    (clear : setup.CommitRecoveryClear history.state)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) (who : Player)
    (members : PMF ((setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who))
    (readout : members.map (fun member => member (setup.commitRecoveryPrivate who history.state)) =
      setup.commitRecoveryNonmissingSourcePolicy wellFormed assessment.strategy who
        (setup.commitRecoveryPrivate who history.state)) :
    members.bind (fun member => setup.commitRecoveryValuePolicy wellFormed assessment.strategy
      who member (setup.commitRecoveryClearInformation wellFormed who
        (setup.commitRecoveryPrivate who history.state))) =
      assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (setup.commitRecoveryPrivate who history.state)) := by
  let view := setup.commitRecoveryPrivate who history.state
  let information := setup.commitRecoveryClearInformation wellFormed who view
  let original := assessment.strategy who information
  let lift := setup.commitRecoveryClearChoice wellFormed who view
  simp_rw [setup.commitRecoveryValuePolicy_clear]
  change members.bind (fun member => original.map
    (fun choice => if CommitRecoveryMove.missed choice.1 then choice else lift (member view))) = _
  let next := fun choice : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Choice who view =>
    original.map (fun original =>
      if CommitRecoveryMove.missed original.1 then original else lift choice)
  change members.bind (next ∘ fun member => member view) = _
  rw [← PMF.bind_map]
  change members.map (fun member => member view) = _ at readout
  rw [readout]
  have restored := setup.commitRecoveryNonmissingSourcePolicy_clear_law wellFormed assessment
    mixed history clear running who
  have moved := congrArg (fun law => law.bind fun replacement => original.map
    (fun choice => if CommitRecoveryMove.missed choice.1 then choice else replacement)) restored
  rw [PMF.bind_map] at moved
  exact moved.trans (resample_false original (fun choice => CommitRecoveryMove.missed choice.1))

end Vegas.SourceProgram.Setup
