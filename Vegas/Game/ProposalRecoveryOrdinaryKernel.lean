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

/-- At the actual sole source actor, the whole semantic joint draw is exactly
the current ordinary table embedded in that coordinate. Inactive excluded
owners contribute NONE; the original source prefix remains the conditioning
argument, with no independent latent-value selection. -/
theorem proposalRecovery_ordinary_semantic_joint
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (running : ¬ setup.proposalRecoveryProtocol.terminal (some current))
    (who : Player) (actor : ProtocolState.actor setup.program current.point = some who) :
    (setup.proposalRecoveryModel.behavioralJoint
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        trace running).map (fun joint => proposalRecoveryJoint joint.val) =
      (values who (setup.proposalRecoveryQuery who
        (setup.proposalRecoveryModel.infoOf who trace))).map
          (fun choice => setup.commitRecoveryProtocol.singletonJoint who choice.val.val) := by
  let profile := setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
  have unique : ∀ other, setup.proposalRecoveryProtocol.active (some current) other →
      other = who := by
    intro other acting
    exact Option.some.inj (acting.1.symm.trans actor)
  rw [setup.proposalRecoveryModel.behavioralJoint_eq_map_of_at_most_one_active
    profile trace running who unique, PMF.map_comp]
  have marginal := congrArg (PMF.map
    (setup.commitRecoveryProtocol.singletonJoint who))
      (setup.proposalRecovery_ordinary_semantic_draw values who
        (setup.proposalRecoveryModel.infoOf who trace))
  have embed (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who trace)) :
      proposalRecoveryJoint (setup.proposalRecoveryProtocol.singletonJoint who choice.val) =
        setup.commitRecoveryProtocol.singletonJoint who (choice.val.map (·.semantic)) := by
    funext other
    change (setup.proposalRecoveryProtocol.singletonJoint who choice.val other).map
        (·.semantic) =
      setup.commitRecoveryProtocol.singletonJoint who (choice.val.map (·.semantic)) other
    by_cases same : other = who
    · subst other
      rw [ExecutionProtocol.singletonJoint_self, ExecutionProtocol.singletonJoint_self]
    · rw [ExecutionProtocol.singletonJoint_of_ne _ _ _ same,
        ExecutionProtocol.singletonJoint_of_ne _ _ _ same]
      rfl
  change (profile who (setup.proposalRecoveryModel.infoOf who trace)).map
      (fun choice => proposalRecoveryJoint
        (setup.proposalRecoveryProtocol.singletonJoint who choice.val)) = _
  have moved := congrArg
    (fun f => (profile who (setup.proposalRecoveryModel.infoOf who trace)).map f) (funext embed)
  exact moved.trans (by
    simpa only [profile, PMF.map_comp, Function.comp_def] using marginal)

/-- The actual semantic state successor is obtained by one literal ordinary
source draw followed by the existing recovery step. This is the one-step law
used by the chronological commitment comparison; no alternate runner is used. -/
theorem proposalRecovery_ordinary_successor_kernel
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (running : ¬ setup.proposalRecoveryProtocol.terminal (some current))
    (who : Player) (actor : ProtocolState.actor setup.program current.point = some who) :
    (setup.proposalRecoveryModel.behavioralJoint
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        trace running).bind (setup.proposalRecoveryProtocol.step (some current)) =
      (values who (setup.proposalRecoveryQuery who
        (setup.proposalRecoveryModel.infoOf who trace))).bind (fun choice =>
          (current.step (setup.commitRecoveryProtocol.singletonJoint who choice.val.val)).map
            some) := by
  have joint := setup.proposalRecovery_ordinary_semantic_joint values current trace running who
    actor
  have projected := congrArg (PMF.bind · (fun selected => (current.step selected).map some)) joint
  simpa only [PMF.bind_map, Function.comp_def, proposalRecoveryProtocol,
    Setup.commitRecoveryProtocol] using projected

end Joint
end Vegas.SourceProgram.Setup
