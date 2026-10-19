/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryPreparationRepairSource
import Vegas.Source.ProposalRecoveryPreparationRepairMoves

/-! # Whole initialized source histories with a designated preparation repaired -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The relation retains the actual initialized state and every retry field. -/
def PreparationStates (owner : Player) :
    setup.proposalRecoveryProtocol.State → setup.proposalRecoveryProtocol.State → Prop
  | none, none => True
  | some original, some repaired => CommitRecoveryState.FocalRepair owner original repaired
  | _, _ => False

/-- Full enriched information propagates through the same literal observer
choice and matched actual private/public signals. -/
theorem proposalRecovery_preparation_info_extend (observer : Player)
    {before after repairedBefore repairedAfter : setup.proposalRecoveryProtocol.State}
    (prior : setup.proposalRecoveryProtocol.Trace before)
    (image : setup.proposalRecoveryProtocol.Trace repairedBefore)
    (joint translated : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before joint)
    (permitted : setup.proposalRecoveryProtocol.Legal repairedBefore translated)
    (reached : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support)
    (admitted : repairedAfter ∈ (setup.proposalRecoveryProtocol.step repairedBefore
      ⟨translated, permitted⟩).support)
    (information : setup.proposalRecoveryModel.infoOf observer image =
      setup.proposalRecoveryModel.infoOf observer prior)
    (choice : translated observer = joint observer)
    (privateView : setup.commitRecoveryPrivate observer repairedAfter =
      setup.commitRecoveryPrivate observer after)
    (controls : setup.commitRecoveryPublic repairedAfter = setup.commitRecoveryPublic after)
    (proposal : setup.proposalRecoveryProposalOf repairedBefore translated =
      setup.proposalRecoveryProposalOf before joint) :
    setup.proposalRecoveryModel.infoOf observer (image.extend translated permitted admitted) =
      setup.proposalRecoveryModel.infoOf observer (prior.extend joint legal reached) := by
  change setup.proposalRecoverySignals.withOwnPlayRecall.pushInfo observer
      (setup.proposalRecoveryModel.infoOf observer image) (translated observer)
      (setup.commitRecoveryPrivate observer repairedAfter)
      (setup.commitRecoveryPublic repairedAfter,
        setup.proposalRecoveryProposalOf repairedBefore translated) =
    setup.proposalRecoverySignals.withOwnPlayRecall.pushInfo observer
      (setup.proposalRecoveryModel.infoOf observer prior) (joint observer)
      (setup.commitRecoveryPrivate observer after)
      (setup.commitRecoveryPublic after, setup.proposalRecoveryProposalOf before joint)
  rw [information, choice, privateView, controls, proposal]

/-- The repaired response adds no generated preparation failure to the actual
owner word. This statement still permits every literal missing commitment. -/
theorem proposalRecovery_prepared_extend (owner : Player)
    {before after : setup.proposalRecoveryProtocol.State}
    (prior : setup.proposalRecoveryProtocol.Trace before)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before joint)
    (reached : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support)
    (previous : ∀ record ∈ setup.proposalRecoveryModel.ownPlay owner prior,
      ¬ ProposalRecoveryMove.GeneratedPreparationFailure (some record.2))
    (current : ¬ ProposalRecoveryMove.GeneratedPreparationFailure (joint owner)) :
    ∀ record ∈ setup.proposalRecoveryModel.ownPlay owner (prior.extend joint legal reached),
      ¬ ProposalRecoveryMove.GeneratedPreparationFailure (some record.2) := by
  rw [InfoSignals.ownPlay_extend]
  cases selected : joint owner with
  | none => exact previous
  | some move =>
      intro record included
      rcases List.mem_cons.mp included with equal | earlier
      · subst record
        simpa only [selected] using current
      · exact previous record earlier

/-- Every initialized enriched source history has an actual same-fiber
counterpart with no designated generated bad preparation. The culprit may
already be excluded; initializer cells and omissions are never repaired. -/
theorem proposalRecovery_preparation_history (owner : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    ∃ image : setup.proposalRecoveryProtocol.History,
      image.trace.length = trace.length ∧ setup.PreparationStates owner state image.state ∧
      (∀ observer, observer ≠ owner →
        setup.proposalRecoveryModel.infoOf observer image.trace =
          setup.proposalRecoveryModel.infoOf observer trace) ∧
      (∀ record ∈ setup.proposalRecoveryModel.ownPlay owner image.trace,
        ¬ ProposalRecoveryMove.GeneratedPreparationFailure (some record.2)) := by
  induction trace with
  | start => exact ⟨setup.proposalRecoveryProtocol.initHistory, rfl, trivial,
      fun _ _ => rfl, fun _ member => by cases member⟩
  | @extend before after prior joint legal reached ih =>
      obtain ⟨image, length, relation, information, prepared⟩ := ih
      cases before with
      | none =>
          cases image with | mk imageState image =>
            cases imageState with
            | some => exact relation.elim
            | none =>
                obtain ⟨inputs, drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
                have newPrepared :
                    ¬ ProposalRecoveryMove.GeneratedPreparationFailure (joint owner) := by
                  have offered := legal.2 owner
                  cases selected : joint owner with
                  | none => simp [ProposalRecoveryMove.GeneratedPreparationFailure]
                  | some move =>
                      rw [selected] at offered
                      exact offered.1.elim
                refine ⟨⟨_, image.extend joint legal reached⟩,
                  congrArg (· + 1) length, ?_, ?_, ?_⟩
                · have reflexive := ProtocolState.focalRepair_entry owner setup.program
                    (Config.FocalRepair.refl owner (setup.initialConfig inputs))
                  exact ⟨reflexive, reflexive, rfl, rfl, rfl⟩
                · intro observer foreign
                  exact setup.proposalRecovery_preparation_info_extend observer prior image joint
                    joint legal legal reached reached (information observer foreign) rfl rfl rfl rfl
                · exact setup.proposalRecovery_prepared_extend owner image joint legal reached
                    prepared newPrepared
      | some original =>
          cases image with | mk imageState image =>
            cases imageState with
            | none => exact relation.elim
            | some repaired =>
                obtain ⟨target, translated, described, foreign, permitted, admitted,
                  ⟨current, targetEq, related⟩, proposal⟩ :=
                  setup.proposalRecovery_preparation_step owner original repaired relation joint
                    legal after reached
                subst after
                refine ⟨⟨_, image.extend translated permitted admitted⟩,
                  congrArg (· + 1) length, related, ?_, ?_⟩
                · intro observer outside
                  exact setup.proposalRecovery_preparation_info_extend observer prior image joint
                    translated legal permitted reached admitted (information observer outside)
                    (foreign observer outside)
                    (setup.proposalRecovery_private_of_preparation owner observer current target
                      related outside)
                    (setup.proposalRecovery_public_of_preparation owner current target related)
                    proposal
                · apply setup.proposalRecovery_prepared_extend owner image translated permitted
                    admitted prepared
                  rw [described]
                  exact ProtocolState.repairPreparationJoint_prepared owner setup.program
                    original.point original.excluded joint
                      (setup.proposalRecoveryJoint_legal (state := some original) joint legal.2)

end Vegas.SourceProgram.Setup
