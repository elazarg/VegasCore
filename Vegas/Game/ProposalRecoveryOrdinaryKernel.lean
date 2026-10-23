/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPerturbation

/-! # Literal ordinary source draws in the actual recovery step kernel -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- With prospective flags removed, the actual legal labeled choice is the
ordinary component choice transported to this same full source information.
Keeping the legal choice, rather than only its semantic marginal, permits
continuation through the original history extension operation. -/
theorem proposalRecovery_ordinary_choice_law
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) (information : setup.proposalRecoveryModel.InfoState who) :
    setup.proposalRecoveryNormalizedTrembledProfile
        0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
        who information =
      (values who (setup.proposalRecoveryQuery who information)).map (fun choice =>
        (setup.proposalRecoveryComponentChoice who information).symm
          (setup.proposalRecoveryComponentLabelChoice who
            (setup.proposalRecoveryQuery who information) false choice.val)) := by
  simp only [proposalRecoveryNormalizedTrembledProfile, proposalRecoveryPrescribedProfile,
    proposalRecoveryComponentTrembledLaw, commitRecoveryValueTremble, mix_zero,
    PMF.pure_map, ite_self]
  rw [pmf_bind_pure_eq_map, PMF.map_comp, PMF.map_comp]
  rfl

/-- Removing prospective flags leaves the caller's literal ordinary table at
the current enriched query. No history or past preparation is discarded. -/
theorem proposalRecovery_ordinary_semantic_draw
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) (information : setup.proposalRecoveryModel.InfoState who) :
    (setup.proposalRecoveryNormalizedTrembledProfile
        0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
        who information).map (fun choice => choice.val.map (·.semantic)) =
      (values who (setup.proposalRecoveryQuery who information)).map
        (fun choice => choice.val.val) := by
  let key := setup.proposalRecoveryQuery who information
  let component := setup.proposalRecoveryComponentTrembledLaw who key
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one (values who key)
  have raw := setup.proposalRecoveryPrescribedProfile_raw
    (fun owner coordinate => setup.proposalRecoveryComponentTrembledLaw owner coordinate
      0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one
        (values owner coordinate)) who information
  have transported := congrArg (PMF.map
    (fun choice : Option (ProposalRecoveryMove Player L) => choice.map (·.semantic))) raw
  have semantic := congrArg (PMF.map
    (fun choice : setup.commitRecoveryModel.Choice who key.1 => choice.val))
      (setup.proposalRecoveryComponentTrembledLaw_semantic who key
        0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one (values who key))
  calc
    _ = component.map (fun choice => choice.val.map (·.semantic)) := by
      convert transported using 1 <;>
        simp only [proposalRecoveryNormalizedTrembledProfile, key, component, PMF.map_comp,
          Function.comp_def]
      all_goals rfl
    _ = (setup.commitRecoveryValueTremble who key.1
        0 le_rfl zero_le_one 0 le_rfl zero_le_one (values who key)).map Subtype.val := by
      simpa only [component, proposalRecoveryComponentSemanticChoice, PMF.map_comp,
        Function.comp_def] using semantic
    _ = _ := by
      simp only [commitRecoveryValueTremble, mix_zero, ite_self, PMF.map_comp,
        Function.comp_def, key]
      rfl

section Joint

variable [Fintype Player]

/-- Expanding actual ordinary play keeps its original full history and every
source joint. The draw tables are read at that history, and the original
`localStep` retains the setup and public chance kernels. Iterating this identity
therefore yields the chronological product without predrawing new coordinates
or replacing the initial joint input distribution. -/
theorem proposalRecovery_ordinary_run_succ
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fuel : Nat) (history : setup.proposalRecoveryProtocol.History) :
    let profile := setup.proposalRecoveryNormalizedTrembledProfile
      0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
    setup.proposalRecoveryModel.runBehavioralFrom profile (fuel + 1) history =
      (independentProduct (fun who => values who
        (setup.proposalRecoveryQuery who
          (setup.proposalRecoveryModel.infoOf who history.trace)))).bind (fun draws =>
            (setup.proposalRecoveryModel.localStep history (fun who =>
              (setup.proposalRecoveryComponentChoice who
                (setup.proposalRecoveryModel.infoOf who history.trace)).symm
                  (setup.proposalRecoveryComponentLabelChoice who
                    (setup.proposalRecoveryQuery who
                      (setup.proposalRecoveryModel.infoOf who history.trace)) false
                        (draws who).val))).bind
              (setup.proposalRecoveryModel.runBehavioralFrom profile fuel)) := by
  intro profile
  rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_localStep]
  have laws := fun who => setup.proposalRecovery_ordinary_choice_law values who
    (setup.proposalRecoveryModel.infoOf who history.trace)
  simp_rw [show ∀ who, profile who (setup.proposalRecoveryModel.infoOf who history.trace) =
    (values who (setup.proposalRecoveryQuery who
      (setup.proposalRecoveryModel.infoOf who history.trace))).map (fun choice =>
        (setup.proposalRecoveryComponentChoice who
          (setup.proposalRecoveryModel.infoOf who history.trace)).symm
            (setup.proposalRecoveryComponentLabelChoice who
              (setup.proposalRecoveryQuery who
                (setup.proposalRecoveryModel.infoOf who history.trace)) false choice.val))
      from laws]
  rw [← independentProduct_map, PMF.bind_map, PMF.bind_bind]
  rfl

end Joint
end Vegas.SourceProgram.Setup
