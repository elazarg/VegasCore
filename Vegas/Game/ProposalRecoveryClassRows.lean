/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPerturbation
import Vegas.Source.ProposalRecoveryWordLift
import Vegas.Source.ProposalRecoveryDisclosure
import GameTheory.Math.Probability.Conditioning

/-! # Actual source disclosure classes and their conditional causes -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
/-- An ordinary source coordinate never carries the extra label reserved
for a withheld reveal. Thus summing the conditional label coin keeps its
literal ordinary choice, including at arbitrary ambient normalized keys. -/
theorem proposalRecoveryComponentLabelChoice_value
    (setup : Setup (Player := Player) (L := L)) (owner : Player)
    (key : setup.ProposalRecoveryComponent owner)
    (value : setup.CommitRecoveryValueChoice owner key.1) (requested : Bool) :
    setup.proposalRecoveryComponentLabelChoice owner key requested value.val =
      setup.proposalRecoveryComponentLabelChoice owner key false value.val := by
  apply Subtype.ext
  change value.val.val.map (fun move => ProposalRecoveryMove.label move requested) =
    value.val.val.map (fun move => ProposalRecoveryMove.label move false)
  cases selected : value.val.val with
  | none => rfl
  | some move =>
      have proper := (value.property move selected).2
      cases action : move.action with
      | commit => simp only [Option.map_some, ProposalRecoveryMove.label, action]
      | reveal author name disclose =>
          cases disclose with
          | true => simp only [Option.map_some, ProposalRecoveryMove.label, action]
          | false =>
              exact False.elim (proper (by rw [action]; rfl))

omit [Fintype Player] in
/-- This is the ACTUAL noncommitment component law before any public-result
conditioning: omission first, its conditional proposal-label coin second,
and the literal ordinary component on the remaining branch. In particular
the two failure-with-proposal row weights come from this source law, rather
than from a physical delivery probability. -/
theorem proposalRecoveryComponentTrembledLaw_noncommit
    (setup : Setup (Player := Player) (L := L)) (owner : Player)
    (key : setup.ProposalRecoveryComponent owner)
    (noncommit : key.1.1.1.1.elim false
      (ProtocolView.atCommit owner setup.program) = false)
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (values : PMF (setup.CommitRecoveryValueChoice owner key.1)) :
    setup.proposalRecoveryComponentTrembledLaw owner key omission.val omission.property.1
        omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val
        delivery.property.1 delivery.property.2 values =
      mix omission.val omission.property.1 omission.property.2
        ((mix delivery.val delivery.property.1 delivery.property.2
          (PMF.pure true) (PMF.pure false)).map fun requested =>
            setup.proposalRecoveryComponentLabelChoice owner key requested
              (setup.commitRecoveryFailureChoice owner key.1 true))
        (values.map fun value =>
          setup.proposalRecoveryComponentLabelChoice owner key false value.val) := by
  simp only [proposalRecoveryComponentTrembledLaw, commitRecoveryValueTremble, noncommit,
    Bool.false_eq_true, ite_false, mix_bind, PMF.pure_bind]
  apply congrArg (mix omission.val omission.property.1 omission.property.2 _)
  rw [PMF.bind_map]
  trans values.bind (fun value => PMF.pure
    (setup.proposalRecoveryComponentLabelChoice owner key false value.val))
  · apply bind_congr_on_support
    intro value _supported
    calc
      _ = (mix delivery.val delivery.property.1 delivery.property.2
            (PMF.pure true) (PMF.pure false)).map (fun _ =>
              setup.proposalRecoveryComponentLabelChoice owner key false value.val) := by
                apply congrArg (PMF.map · _)
                funext requested
                exact setup.proposalRecoveryComponentLabelChoice_value owner key value requested
      _ = _ := PMF.map_const _ _
  · exact PMF.bind_pure_comp _ _

/-- Keep every commitment and focal label literal. A foreign publication
retains its address and whether it exposes a proposal, but its semantic
delivery cause can be statistically refined. This is used only on legal
source steps with their actual public successor, never as a new menu. -/
def proposalRecoveryForeignCauseJoint (focal : Player)
    (joint : Player → Option (ProposalRecoveryMove Player L)) :
    Player → Option (ProposalRecoveryMove Player L ⊕ (Player × VarId × Bool)) :=
  fun owner => (joint owner).map fun move =>
    if owner = focal then Sum.inl move else
      match move.semantic.action with
      | .commit .. => Sum.inl move
      | .reveal author name _ => Sum.inr (author, name, move.discloses)

/-- The full surviving focal source information is retained along with the
latest actual instruction class. Thus commitment values stay locked even
when hidden from that observer; only foreign publication causes are summed. -/
def proposalRecoveryForeignCauseRead (setup : Setup (Player := Player) (L := L))
    (focal : Player) (history : setup.proposalRecoveryProtocol.History) :=
  (setup.proposalRecoveryModel.infoOf focal history.trace,
    (setup.proposalRecoveryJointRecall history.trace).head?.map
      (proposalRecoveryForeignCauseJoint focal))

end Vegas.SourceProgram.Setup
