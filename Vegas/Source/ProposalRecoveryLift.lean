/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryInformation

/-! # Actual labeled lifts of semantic recovery histories -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProposalRecoveryMove

/-- Additional proposal labels apply only to withheld semantic reveals. -/
def label (move : CommitRecoveryMove Player L) (requested : Bool) :
    ProposalRecoveryMove Player L :=
  match move.action with
  | .reveal _ _ false => ⟨move, requested⟩
  | _ => ordinary move

omit [DecidableEq Player] [IExpr.ResultTypes L] in
@[simp] theorem label_semantic (move : CommitRecoveryMove Player L) (requested : Bool) :
    (label move requested).semantic = move := by
  rcases move with ⟨action, missing⟩
  cases action with
  | commit => rfl
  | reveal _ _ disclose => cases disclose <;> rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem label_valid (move : CommitRecoveryMove Player L) (requested : Bool) :
    (label move requested).Valid := by
  rcases move with ⟨action, missing⟩
  cases action with
  | commit => exact ordinary_valid _
  | reveal owner name disclose =>
      cases disclose with
      | false => exact fun _ => ⟨owner, name, rfl⟩
      | true => exact ordinary_valid _

end ProposalRecoveryMove

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

def proposalRecoveryLiftJoint
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (event : setup.commitRecoveryProtocol.StepEvent) :
    Player → Option (ProposalRecoveryMove Player L) :=
  fun who => (event.joint who).map fun move => ProposalRecoveryMove.label move (labels event who)

@[simp] theorem proposalRecoveryLiftJoint_semantic
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (event : setup.commitRecoveryProtocol.StepEvent) :
    proposalRecoveryJoint (setup.proposalRecoveryLiftJoint labels event) = event.joint := by
  funext who
  cases selected : event.joint who <;>
    simp only [proposalRecoveryJoint, proposalRecoveryLiftJoint, selected,
      Option.map_none, Option.map_some, ProposalRecoveryMove.label_semantic]

theorem proposalRecoveryLiftJoint_legal
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (event : setup.commitRecoveryProtocol.StepEvent) :
    setup.proposalRecoveryProtocol.Legal event.source
      (setup.proposalRecoveryLiftJoint labels event) := by
  refine ⟨event.isLegal.1, ?_⟩
  intro who
  have offered := event.isLegal.2 who
  cases selected : event.joint who with
  | none =>
      simpa only [proposalRecoveryLiftJoint, selected, Option.map_none,
        proposalRecoveryProtocol] using offered
  | some move =>
      rw [selected] at offered
      simpa only [proposalRecoveryLiftJoint, selected, Option.map_some,
        proposalRecoveryProtocol, proposalRecoveryAvailable, Set.mem_ofPred_eq,
        ProposalRecoveryMove.label_semantic] using
        (show setup.commitRecoveryProtocol.active event.source who ∧
          move ∈ setup.commitRecoveryProtocol.available event.source who ∧
          (ProposalRecoveryMove.label move (labels event who)).Valid from
          ⟨offered.1, offered.2, ProposalRecoveryMove.label_valid _ _⟩)

theorem proposalRecoveryLiftJoint_step
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (event : setup.commitRecoveryProtocol.StepEvent) :
    setup.proposalRecoveryProtocol.step event.source
        ⟨setup.proposalRecoveryLiftJoint labels event,
          setup.proposalRecoveryLiftJoint_legal labels event⟩ =
      setup.commitRecoveryProtocol.step event.source ⟨event.joint, event.isLegal⟩ := by
  apply congrArg (setup.commitRecoveryProtocol.step event.source)
  apply Subtype.ext
  exact setup.proposalRecoveryLiftJoint_semantic labels event

/-- Any semantic trace admits any permitted proposal labels, with its SAME
endpoint and original chance outcomes. Labels never supply the proposed value. -/
def proposalRecoveryLiftTrace
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) :
    ∀ {state : setup.commitRecoveryProtocol.State}, setup.commitRecoveryProtocol.Trace state →
      setup.proposalRecoveryProtocol.Trace state
  | _, .start => .start
  | _, .extend prior joint legal supported =>
      let event : setup.commitRecoveryProtocol.StepEvent := ⟨_, joint, legal, _, supported⟩
      .extend (proposalRecoveryLiftTrace labels prior)
        (setup.proposalRecoveryLiftJoint labels event)
        (setup.proposalRecoveryLiftJoint_legal labels event)
        (by
          change event.target ∈ (setup.proposalRecoveryProtocol.step event.source
            ⟨setup.proposalRecoveryLiftJoint labels event,
              setup.proposalRecoveryLiftJoint_legal labels event⟩).support
          rw [setup.proposalRecoveryLiftJoint_step]
          exact event.realized)

@[simp] theorem proposalRecoveryLiftTrace_length
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryLiftTrace labels trace).length = trace.length := by
  induction trace with
  | start => rfl
  | extend _ _ _ _ ih => exact congrArg Nat.succ ih

@[simp] theorem proposalRecoveryEraseTrace_lift
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    setup.proposalRecoveryEraseTrace (setup.proposalRecoveryLiftTrace labels trace) = trace := by
  induction trace with
  | start => rfl
  | @extend before after prior joint legal supported ih =>
      simp only [proposalRecoveryLiftTrace, proposalRecoveryEraseTrace,
        setup.proposalRecoveryLiftJoint_semantic, ih]

def proposalRecoveryLabeledWord
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) :
    ∀ {state : setup.commitRecoveryProtocol.State}, setup.commitRecoveryProtocol.Trace state →
      List (ProposalRecoveryProposal L)
  | _, .start => []
  | _, .extend prior joint legal supported =>
      let event : setup.commitRecoveryProtocol.StepEvent := ⟨_, joint, legal, _, supported⟩
      proposalRecoveryLabeledWord labels prior ++
        (setup.proposalRecoveryProposalOf event.source
          (setup.proposalRecoveryLiftJoint labels event)).toList

theorem proposalRecoveryProposalWord_lift
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    setup.proposalRecoveryProposalWord who
        (setup.proposalRecoveryModel.infoOf who (setup.proposalRecoveryLiftTrace labels trace)) =
      setup.proposalRecoveryLabeledWord labels trace := by
  induction trace with
  | start => rfl
  | extend _ _ _ _ ih =>
      rw [proposalRecoveryLiftTrace, setup.proposalRecoveryProposalWord_extend, ih]
      rfl

theorem proposalRecoveryArchive_lift
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who (setup.proposalRecoveryLiftTrace labels trace)) =
      (setup.proposalRecoveryLabeledWord labels trace).toFinset := by
  exact congrArg List.toFinset (setup.proposalRecoveryProposalWord_lift labels who trace)

end Setup
end Vegas.SourceProgram
