/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryMove

/-! # Proposal-labeled execution on the existing recovery state -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

def proposalRecoveryAvailable (state : setup.commitRecoveryProtocol.State) (who : Player) :
    Set (ProposalRecoveryMove Player L) :=
  {move | move.semantic ∈ setup.commitRecoveryProtocol.available state who ∧ move.Valid}

def proposalRecoveryJoint
    (joint : Player → Option (ProposalRecoveryMove Player L)) :
    Player → Option (CommitRecoveryMove Player L) :=
  fun who => (joint who).map (·.semantic)

theorem proposalRecoveryJoint_legal {state : setup.commitRecoveryProtocol.State}
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : IsLegalJoint (setup.commitRecoveryProtocol.active state)
      (setup.proposalRecoveryAvailable state) joint) :
    IsLegalJoint (setup.commitRecoveryProtocol.active state)
      (setup.commitRecoveryProtocol.available state) (proposalRecoveryJoint joint) := by
  intro who
  have offered := legal who
  cases selected : joint who with
  | none => simpa only [proposalRecoveryJoint, selected, Option.map_none] using offered
  | some move =>
      rw [selected] at offered
      simpa only [proposalRecoveryJoint, selected, Option.map_some] using
        (show setup.commitRecoveryProtocol.active state who ∧
          move.semantic ∈ setup.commitRecoveryProtocol.available state who from
          ⟨offered.1, offered.2.1⟩)

/-- The operational state, checkpoint and stochastic kernel are the original
recovery ones. Only the action labels and their observations are refined. -/
def proposalRecoveryProtocol : ExecutionProtocol Player where
  State := setup.commitRecoveryProtocol.State
  Action _ := ProposalRecoveryMove Player L
  init := setup.commitRecoveryProtocol.init
  active := setup.commitRecoveryProtocol.active
  available := setup.proposalRecoveryAvailable
  terminal := setup.commitRecoveryProtocol.terminal
  step state joint := setup.commitRecoveryProtocol.step state
    ⟨proposalRecoveryJoint joint.1,
      joint.2.1, setup.proposalRecoveryJoint_legal joint.1 joint.2.2⟩
  progress state running := by
    obtain ⟨joint, legal⟩ := setup.commitRecoveryProtocol.progress state running
    refine ⟨fun who => (joint who).map ProposalRecoveryMove.ordinary, ?_⟩
    intro who
    have offered := legal who
    cases selected : joint who with
    | none => simpa only [selected, Option.map_none] using offered
    | some move =>
        rw [selected] at offered
        simpa only [selected, Option.map_some, proposalRecoveryAvailable,
          Set.mem_ofPred_eq, ProposalRecoveryMove.ordinary_semantic] using
          (show setup.commitRecoveryProtocol.active state who ∧
            move ∈ setup.commitRecoveryProtocol.available state who ∧
            (ProposalRecoveryMove.ordinary move).Valid from
            ⟨offered.1, offered.2, ProposalRecoveryMove.ordinary_valid move⟩)

theorem proposalRecovery_erase_legal {state : setup.proposalRecoveryProtocol.State}
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal state joint) :
    setup.commitRecoveryProtocol.Legal state (proposalRecoveryJoint joint) :=
  ⟨legal.1, setup.proposalRecoveryJoint_legal joint legal.2⟩

theorem proposalRecovery_step (state : setup.proposalRecoveryProtocol.State)
    (joint : {joint // setup.proposalRecoveryProtocol.Legal state joint}) :
    setup.proposalRecoveryProtocol.step state joint =
      setup.commitRecoveryProtocol.step state
        ⟨proposalRecoveryJoint joint.1, setup.proposalRecovery_erase_legal joint.1 joint.2⟩ :=
  rfl

/-- Erasure preserves the actual semantic endpoint and every original draw. -/
def proposalRecoveryEraseTrace : ∀ {state : setup.proposalRecoveryProtocol.State},
    setup.proposalRecoveryProtocol.Trace state → setup.commitRecoveryProtocol.Trace state
  | _, .start => .start
  | _, .extend prior joint legal supported =>
      .extend (proposalRecoveryEraseTrace prior) (proposalRecoveryJoint joint)
        (setup.proposalRecovery_erase_legal joint legal) supported

@[simp] theorem proposalRecoveryEraseTrace_length
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryEraseTrace trace).length = trace.length := by
  induction trace with
  | start => rfl
  | extend _ _ _ _ ih => exact congrArg Nat.succ ih

theorem proposalRecovery_rank_step [Fintype Player]
    {before after : setup.proposalRecoveryProtocol.State}
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support) :
    setup.commitRecoveryRank after < setup.commitRecoveryRank before :=
  setup.commitRecoveryRank_step (proposalRecoveryJoint joint)
    (setup.proposalRecovery_erase_legal joint legal) supported

theorem proposalRecoveryProtocol_bounded [Fintype Player] :
    setup.proposalRecoveryProtocol.BoundedHorizon
      ((Fintype.card Player + 1) * (instructionCount setup.program + 1)) := by
  intro state trace enough
  apply setup.commitRecoveryProtocol_bounded state (setup.proposalRecoveryEraseTrace trace)
  simpa only [setup.proposalRecoveryEraseTrace_length] using enough

theorem proposalRecoveryProtocol_terminates [Finite Player] :
    setup.proposalRecoveryProtocol.WellFoundedPlay := by
  let := Fintype.ofFinite Player
  apply wellFoundedPlay_of_rank (E := setup.proposalRecoveryProtocol) setup.commitRecoveryRank
  intro before after event
  obtain ⟨joint, legal, supported⟩ := event
  exact setup.proposalRecovery_rank_step joint legal supported

end Vegas.SourceProgram.Setup
