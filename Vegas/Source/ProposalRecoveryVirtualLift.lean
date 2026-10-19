/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryVirtualStep

/-! # The same repaired source history with its actual proposal archive -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The recorded paired raw witnesses suffice because every proposal-bearing
instruction is a deterministic reveal for its given prestate and joint. -/
theorem proposalRecovery_virtual_event_delta (focal : Player)
    (left right : setup.commitRecoveryProtocol.StepEvent)
    (paired : setup.CommitRecoveryVirtualEvent focal left right) (labels : Player → Bool) :
    setup.proposalRecoveryProposalOf left.source
        (setup.proposalRecoveryLiftJoint (fun _ => labels) left) =
      setup.proposalRecoveryProposalOf right.source
        (setup.proposalRecoveryLiftJoint (fun _ => labels) right) := by
  rcases paired with same | ⟨original, repaired, after, target, leftSource, rightSource,
      _leftTarget, _rightTarget, before, _after, foreign, _survives, raw⟩
  · subst right
    rfl
  · obtain ⟨leftRaw, rightRaw, leftReached, rightReached, sameExcluded, _related, active⟩ := raw
    have rightActive : focal ∉ rightRaw.2 := by rwa [sameExcluded]
    have actualRight : rightRaw ∈ (ProtocolState.recoveryStep setup.program repaired.point
        original.excluded right.joint).support := by
      simpa only [before.excluded] using rightReached
    have scalar := ProtocolState.recoveryProposal_virtual_eq
      (setup.context.map Prod.fst).toFinset focal setup.program original.point repaired.point
      before.point original.excluded left.joint right.joint foreign leftRaw rightRaw
      leftReached actualRight active rightActive labels
    unfold proposalRecoveryProposalOf
    rw [leftSource, rightSource]
    simp only [Option.bind_some]
    change (ProtocolState.recoveryProposal setup.program original.point
        (fun owner => if owner ∈ original.excluded then none else
          (left.joint owner).map (fun move => ProposalRecoveryMove.label move (labels owner)))).map
            (fun pair => (⟨⟨setup.program.publicationBlockLow pair.1,
              original.generation, pair.1⟩, pair.2.1, pair.2.2⟩ : ProposalRecoveryProposal L)) =
      (ProtocolState.recoveryProposal setup.program repaired.point
        (fun owner => if owner ∈ repaired.excluded then none else
          (right.joint owner).map (fun move => ProposalRecoveryMove.label move (labels owner)))).map
            (fun pair => (⟨⟨setup.program.publicationBlockLow pair.1,
              repaired.generation, pair.1⟩, pair.2.1, pair.2.2⟩ : ProposalRecoveryProposal L))
    rw [before.excluded, before.generation]
    exact congrArg (Option.map fun pair =>
      (⟨⟨setup.program.publicationBlockLow pair.1, original.generation, pair.1⟩,
        pair.2.1, pair.2.2⟩ : ProposalRecoveryProposal L)) scalar

/-- The chosen repaired trace is retained literally. Labels are copied per
paired event; no global selector on changed prestates and no archive-equality
premise is needed. The complete chronological word is preserved, hence so is
its canonical archive for every observer. -/
theorem proposalRecovery_virtual_labeled_trace (focal : Player)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (left : setup.commitRecoveryProtocol.Trace leftState)
    (right : setup.commitRecoveryProtocol.Trace rightState)
    (paired : List.Forall₂ (setup.CommitRecoveryVirtualEvent focal)
      (setup.commitRecoveryEventRecall left) (setup.commitRecoveryEventRecall right))
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) :
    ∃ lifted : setup.proposalRecoveryProtocol.Trace rightState,
      setup.proposalRecoveryEraseTrace lifted = right ∧
      ∀ observer, setup.proposalRecoveryProposalWord observer
          (setup.proposalRecoveryModel.infoOf observer lifted) =
        setup.proposalRecoveryProposalWord observer (setup.proposalRecoveryModel.infoOf observer
          (setup.proposalRecoveryLiftTrace labels left)) := by
  induction right generalizing leftState with
  | start =>
      cases left with
      | start => exact ⟨.start, rfl, fun _ => rfl⟩
      | extend prior joint legal reached => cases paired
  | @extend before after prior joint legal reached ih =>
      cases left with
      | start => cases paired
      | @extend leftBefore leftAfter leftPrior leftJoint leftLegal leftReached =>
          cases paired with
          | cons head tail =>
              obtain ⟨lifted, erased, word⟩ := ih leftPrior tail
              let leftEvent : setup.commitRecoveryProtocol.StepEvent :=
                ⟨leftBefore, leftJoint, leftLegal, leftState, leftReached⟩
              let rightEvent : setup.commitRecoveryProtocol.StepEvent :=
                ⟨before, joint, legal, after, reached⟩
              let selected := setup.proposalRecoveryLiftJoint
                (fun _ => labels leftEvent) rightEvent
              have selectedLegal := setup.proposalRecoveryLiftJoint_legal
                (fun _ => labels leftEvent) rightEvent
              have selectedReached : after ∈
                  (setup.proposalRecoveryProtocol.step before
                    ⟨selected, selectedLegal⟩).support := by
                change rightEvent.target ∈ (setup.proposalRecoveryProtocol.step rightEvent.source
                  ⟨setup.proposalRecoveryLiftJoint (fun _ => labels leftEvent) rightEvent,
                    setup.proposalRecoveryLiftJoint_legal
                      (fun _ => labels leftEvent) rightEvent⟩).support
                rw [setup.proposalRecoveryLiftJoint_step]
                exact reached
              refine ⟨lifted.extend selected selectedLegal selectedReached, ?_, ?_⟩
              · change (setup.proposalRecoveryEraseTrace lifted).extend
                  (proposalRecoveryJoint selected) _ _ = prior.extend joint legal reached
                have semantic := setup.proposalRecoveryLiftJoint_semantic
                  (fun _ => labels leftEvent) rightEvent
                have same : proposalRecoveryJoint selected = joint := semantic
                simp only [erased, same]
              · intro observer
                rw [setup.proposalRecoveryProposalWord_extend]
                change _ = setup.proposalRecoveryProposalWord observer
                  (setup.proposalRecoveryModel.infoOf observer
                    ((setup.proposalRecoveryLiftTrace labels leftPrior).extend _ _ _))
                rw [setup.proposalRecoveryProposalWord_extend, word observer]
                have delta := setup.proposalRecovery_virtual_event_delta focal leftEvent rightEvent
                  head (labels leftEvent)
                have sameLabels : setup.proposalRecoveryLiftJoint
                    (fun _ => labels leftEvent) leftEvent =
                  setup.proposalRecoveryLiftJoint labels leftEvent := rfl
                rw [sameLabels] at delta
                simpa only [selected, leftEvent, rightEvent] using
                  congrArg (fun proposal =>
                    setup.proposalRecoveryProposalWord observer
                      (setup.proposalRecoveryModel.infoOf observer
                        (setup.proposalRecoveryLiftTrace labels leftPrior)) ++ proposal.toList)
                    delta.symm

theorem proposalRecovery_virtual_labeled_archive (focal : Player)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (left : setup.commitRecoveryProtocol.Trace leftState)
    (right : setup.commitRecoveryProtocol.Trace rightState)
    (paired : List.Forall₂ (setup.CommitRecoveryVirtualEvent focal)
      (setup.commitRecoveryEventRecall left) (setup.commitRecoveryEventRecall right))
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) :
    ∃ lifted : setup.proposalRecoveryProtocol.Trace rightState,
      setup.proposalRecoveryEraseTrace lifted = right ∧
      ∀ observer, setup.proposalRecoveryArchive observer
          (setup.proposalRecoveryModel.infoOf observer lifted) =
        setup.proposalRecoveryArchive observer (setup.proposalRecoveryModel.infoOf observer
          (setup.proposalRecoveryLiftTrace labels left)) := by
  obtain ⟨lifted, erased, word⟩ := setup.proposalRecovery_virtual_labeled_trace focal
    left right paired labels
  exact ⟨lifted, erased, fun observer => congrArg List.toFinset (word observer)⟩

/-- A surviving factual source actor gives a genuine decision site of the
enriched game, with its actual trace rather than a synthesized information key. -/
theorem proposalRecovery_isDecisionInfo_of_surviving_actor
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current)) (who : Player)
    (survives : who ∉ current.excluded)
    (actor : ProtocolState.actor setup.program current.point = some who) :
    setup.proposalRecoveryModel.IsDecisionInfo who
      (setup.proposalRecoveryModel.infoOf who trace) := by
  have active : setup.proposalRecoveryProtocol.active (some current) who := ⟨actor, survives⟩
  have running : ¬ setup.proposalRecoveryProtocol.terminal (some current) := by
    intro terminal
    have impossible := ProtocolState.terminal_actor_none who setup.program current.point terminal
    rw [ProtocolState.actor_observe_eq, actor] at impossible
    cases impossible
  obtain ⟨joint, legal⟩ := setup.proposalRecoveryProtocol.progress (some current) running
  have localLegal := legal who
  cases chosen : joint who with
  | none =>
      rw [chosen] at localLegal
      exact (localLegal active).elim
  | some move =>
      rw [chosen] at localLegal
      refine ⟨⟨⟨some current, trace⟩, rfl⟩, running, move, ?_⟩
      exact (setup.proposalRecoveryModel.menu_adequate who trace (some move)).mpr localLegal

end Vegas.SourceProgram.Setup
