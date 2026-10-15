/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryOmissionPosition
import GameTheory.Analysis.Protocol.CounterfactualReach

/-! # Conditional nonmissing source choices and their exact masses -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Condition the existing auxiliary choice law, without replacing its typed
binding result or its updated decision history. Zero-mass fibers retain the
library's total conditional-law convention. -/
def commitRecoveryNonmissingProfile
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∀ who, setup.commitRecoveryModel.BehavioralPolicy who := fun who info =>
  fiberPosterior (profile who info) (fun choice => CommitRecoveryMove.missed choice.1) false

def commitRecoveryNonmissingMass
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) : ENNReal :=
  ((profile who info).map (fun choice => CommitRecoveryMove.missed choice.1)) false

/-- Every actual nonterminal source history admits a nonmissing legal choice.
Full mixing makes its conditioning event positive, even after arbitrary retries. -/
theorem commitRecovery_nonmissing_present
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) (who : Player) :
    false ∈ ((assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace)).map
      (fun choice => CommitRecoveryMove.missed choice.1)).support := by
  obtain ⟨choice⟩ := setup.commitRecoveryContinuingChoice_nonempty who
    (setup.commitRecoveryModel.infoOf who history.trace)
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨choice.1, mixed.support_at_history history running who choice.1, ?_⟩
  cases raw : choice.1.1 with
  | none => rfl
  | some move => exact (choice.2 move raw).1

/-- The original atom is its nonmissing marginal times the normalized atom.
An accepted failed binding with a false omission bit is retained in full. -/
theorem commitRecovery_nonmissing_atom
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who)
    (present : false ∈ ((profile who info).map
      (fun choice => CommitRecoveryMove.missed choice.1)).support)
    (choice : setup.commitRecoveryModel.Choice who info)
    (nonmissing : CommitRecoveryMove.missed choice.1 = false) :
    profile who info choice = setup.commitRecoveryNonmissingMass profile who info *
      setup.commitRecoveryNonmissingProfile profile who info choice := by
  classical
  change _ = _ * fiberPosterior (profile who info)
    (fun choice => CommitRecoveryMove.missed choice.1) false choice
  rw [fiberPosterior_apply _ _ _ present]
  have member : choice ∈ {choice : setup.commitRecoveryModel.Choice who info |
      CommitRecoveryMove.missed choice.1 = false} := nonmissing
  rw [Set.indicator_of_mem member]
  unfold commitRecoveryNonmissingMass
  rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel
    ((PMF.mem_support_iff _ _).mp present) (PMF.apply_ne_top _ _), mul_one]

/-- The conditional source policy has no omission on any supported choice
at a genuine nonterminal history. The full raw auxiliary carrier is unchanged. -/
theorem commitRecovery_nonmissing_supported
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) (who : Player)
    (choice : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryModel.infoOf who history.trace))
    (supported : choice ∈ (setup.commitRecoveryNonmissingProfile assessment.strategy who
      (setup.commitRecoveryModel.infoOf who history.trace)).support) :
    CommitRecoveryMove.missed choice.1 = false :=
  (mem_support_fiberPosterior
    (setup.commitRecovery_nonmissing_present assessment mixed history running who) supported).1

variable [Fintype Player]

/-- The scalar accumulated from the actual information values along a source
trace. It records only the marginal probability of each nonmissing draw. -/
def commitRecoveryNonmissingFactor
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∀ {state : setup.commitRecoveryProtocol.State},
      setup.commitRecoveryProtocol.Trace state → ℝ
  | _, .start => 1
  | _, .extend prior _ _ _ =>
      commitRecoveryNonmissingFactor profile prior *
        ∏ who, (setup.commitRecoveryNonmissingMass profile who
          (setup.commitRecoveryModel.infoOf who prior)).toReal

/-- Full mixing makes every finite no-omission factor strictly positive. -/
theorem commitRecovery_nonmissingFactor_pos
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state),
      0 < setup.commitRecoveryNonmissingFactor assessment.strategy trace
  | _, .start => zero_lt_one
  | _, .extend prior joint legal reached => by
      apply mul_pos (commitRecovery_nonmissingFactor_pos assessment mixed prior)
      apply Finset.prod_pos
      intro who _
      exact ENNReal.toReal_pos
        ((PMF.mem_support_iff _ _).mp
          (setup.commitRecovery_nonmissing_present assessment mixed ⟨_, prior⟩ legal.1 who))
        (PMF.apply_ne_top _ _)

end Vegas.SourceProgram.Setup
