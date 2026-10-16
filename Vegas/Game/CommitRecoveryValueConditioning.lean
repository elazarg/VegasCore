/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryValuePolicy
import GameTheory.Math.Probability.ConditionalObservation

/-! # Original omission conditioning of an immutable ordinary source action -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

open Classical in
/-- Replace only the queried owner's nonmissing source action by its immutable
ordinary policy. Every original omitted action is sampled freshly, and all
other source owners retain their original assessment policy. -/
def commitRecoveryValueAssessment (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (who : Player)
    (member : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who) :
    setup.commitRecoveryModel.BehavioralAssessment :=
  .ofStrategy (Function.update assessment.strategy who
    (setup.commitRecoveryValuePolicy wellFormed assessment.strategy who member))

/-- Conditioning a value member on the original positive nonmissing event
selects exactly its fixed ordinary choice. The event is not a physical WAIT
event and accepted source failure remains an ordinary nonmissing action. -/
theorem commitRecoveryValueAssessment_nonmissing (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (who : Player)
    (member : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who) (view : setup.ProtocolView who)
    (present : false ∈ ((assessment.strategy who
      (setup.commitRecoveryClearInformation wellFormed who view)).map
        (fun choice => CommitRecoveryMove.missed choice.1)).support) :
    setup.commitRecoveryNonmissingProfile
        (setup.commitRecoveryValueAssessment wellFormed assessment who member).strategy who
          (setup.commitRecoveryClearInformation wellFormed who view) =
      PMF.pure (setup.commitRecoveryClearChoice wellFormed who view (member view)) := by
  classical
  let original := assessment.strategy who
    (setup.commitRecoveryClearInformation wellFormed who view)
  let flag := fun choice : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryClearInformation wellFormed who view) =>
    CommitRecoveryMove.missed choice.1
  let chosen := setup.commitRecoveryClearChoice wellFormed who view (member view)
  let transform := fun choice => if flag choice then choice else chosen
  have flagTransform : flag ∘ transform = flag := by
    funext choice
    dsimp only [Function.comp_def, transform]
    cases observed : flag choice with
    | false =>
        simp only [Bool.false_eq_true, ite_false]
        exact CommitRecoveryMove.missed_lift (member view).val
    | true => simpa only [ite_true] using observed
  have source : (setup.commitRecoveryValueAssessment wellFormed assessment who member).strategy
      who (setup.commitRecoveryClearInformation wellFormed who view) = original.map transform := by
    simp only [commitRecoveryValueAssessment, InformationModel.BehavioralAssessment.ofStrategy,
      Function.update_self, setup.commitRecoveryValuePolicy_clear]
    rfl
  change fiberPosterior _ flag false = _
  rw [source]
  have observed : false ∈ (original.map (flag ∘ transform)).support := by
    simpa only [flagTransform] using present
  have moved := map_fiberPosterior_readout original transform flag false observed
  rw [flagTransform] at moved
  rw [← moved]
  calc
    _ = (fiberPosterior original flag false).map (fun _ => chosen) := by
      apply map_congr_on_support
      intro choice supported
      have same := (mem_support_fiberPosterior present supported).1
      change flag choice = false at same
      simp only [transform, same, Bool.false_eq_true, ite_false]
    _ = _ := PMF.map_const _ _

end Vegas.SourceProgram.Setup
