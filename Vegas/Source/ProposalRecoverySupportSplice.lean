/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryProjection
import Vegas.Source.ProposalRecoveryErasedStep
import Vegas.Source.ProposalRecoveryWordLift
import Vegas.Source.CommitRecoverySupportSplice

/-! # Genuine proposal-preserving source suffixes after memory substitution -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The complete proposal-delta transcript retains silent source steps too. -/
def proposalRecoveryDeltaRecall : ∀ {state : setup.proposalRecoveryProtocol.State},
    setup.proposalRecoveryProtocol.Trace state → List (Option (ProposalRecoveryProposal L))
  | _, .start => []
  | _, @Trace.extend _ _ before _ prior joint _ _ =>
      setup.proposalRecoveryProposalOf before joint :: proposalRecoveryDeltaRecall prior

def proposalRecoveryErasedHistory (history : setup.proposalRecoveryProtocol.History) :=
  (setup.commitRecoveryErasedHistory
      ⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩,
    setup.proposalRecoveryDeltaRecall history.trace)

theorem proposalRecoveryProposalWord_eq_deltas (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    setup.proposalRecoveryProposalWord who (setup.proposalRecoveryModel.infoOf who trace) =
      (setup.proposalRecoveryDeltaRecall trace).reverse.filterMap id := by
  induction trace with
  | start => rfl
  | extend prior joint legal supported ih =>
      rw [setup.proposalRecoveryProposalWord_extend, ih]
      simp only [proposalRecoveryDeltaRecall, List.reverse_cons, List.filterMap_append,
        List.filterMap_cons, List.filterMap_nil]
      cases setup.proposalRecoveryProposalOf _ joint <;> rfl

theorem proposalRecoveryArchive_eq_of_erased_history
    (first second : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryErasedHistory first =
      setup.proposalRecoveryErasedHistory second) (who : Player) :
    setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who first.trace) =
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who second.trace) := by
  dsimp only [proposalRecoveryArchive]
  rw [setup.proposalRecoveryProposalWord_eq_deltas,
    setup.proposalRecoveryProposalWord_eq_deltas]
  exact congrArg (fun word => (word.reverse.filterMap id).toFinset)
    (congrArg Prod.snd same)

theorem proposalRecoveryQuery_eq_of_erased_history
    (first second : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryErasedHistory first =
      setup.proposalRecoveryErasedHistory second) (who : Player) :
    setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who first.trace) =
      setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who second.trace) := by
  apply Prod.ext
  · dsimp only [proposalRecoveryQuery]
    rw [setup.proposalRecoveryEraseInfo_observed,
      setup.proposalRecoveryEraseInfo_observed,
      setup.commitRecoveryNoMissInformation_erased,
      setup.commitRecoveryNoMissInformation_erased]
    exact congrArg (setup.commitRecoveryNoMissInformation who)
      (congrFun (congrArg Prod.snd (congrArg Prod.fst same)) who)
  · exact setup.proposalRecoveryArchive_eq_of_erased_history first second same who

private theorem legal_of_semantic
    {first second : setup.proposalRecoveryProtocol.State}
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (oldLegal : setup.proposalRecoveryProtocol.Legal first joint)
    (legal : setup.commitRecoveryProtocol.Legal second (proposalRecoveryJoint joint)) :
    setup.proposalRecoveryProtocol.Legal second joint := by
  refine ⟨legal.1, ?_⟩
  intro who
  have offered := legal.2 who
  have original := oldLegal.2 who
  cases selected : joint who with
  | none =>
      change ¬ setup.commitRecoveryProtocol.active second who
      simpa only [proposalRecoveryJoint, selected, Option.map_none] using offered
  | some move =>
      rw [selected] at original
      simp only [proposalRecoveryJoint, selected, Option.map_some] at offered
      exact ⟨offered.1, offered.2, original.2.2⟩

/-- The original supported semantic splice also preserves the actual public
proposal delta. Both histories use the same complete labeled joint action. -/
theorem proposalRecovery_supported_step_of_erased_history_eq
    (first second : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryErasedHistory first =
      setup.proposalRecoveryErasedHistory second)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal first.state joint)
    {target : setup.proposalRecoveryProtocol.State}
    (supported : target ∈
      (setup.proposalRecoveryProtocol.step first.state ⟨joint, legal⟩).support) :
    ∃ rightLegal : setup.proposalRecoveryProtocol.Legal second.state joint,
      ∃ rightTarget : setup.proposalRecoveryProtocol.State,
        ∃ rightSupported : rightTarget ∈
          (setup.proposalRecoveryProtocol.step second.state ⟨joint, rightLegal⟩).support,
          setup.proposalRecoveryErasedHistory (first.extend legal supported) =
            setup.proposalRecoveryErasedHistory (second.extend rightLegal rightSupported) := by
  have oldSame := congrArg Prod.fst same
  have oldLegal := setup.proposalRecovery_erase_legal joint legal
  obtain ⟨rightOldLegal, rightTarget, rightOldSupported, successor⟩ :=
    setup.commitRecovery_supported_step_of_erased_history_eq
      ⟨first.state, setup.proposalRecoveryEraseTrace first.trace⟩
      ⟨second.state, setup.proposalRecoveryEraseTrace second.trace⟩ oldSame
      (proposalRecoveryJoint joint) oldLegal supported
  have rightLegal := setup.legal_of_semantic joint legal rightOldLegal
  have rightSupported : rightTarget ∈
      (setup.proposalRecoveryProtocol.step second.state ⟨joint, rightLegal⟩).support :=
    rightOldSupported
  refine ⟨rightLegal, rightTarget, rightSupported, Prod.ext successor ?_⟩
  change setup.proposalRecoveryProposalOf first.state joint ::
      setup.proposalRecoveryDeltaRecall first.trace =
    setup.proposalRecoveryProposalOf second.state joint ::
      setup.proposalRecoveryDeltaRecall second.trace
  have stateSame := congrArg Prod.fst oldSame
  exact congrArg₂ List.cons (setup.proposalRecoveryProposalOf_eq_of_erased stateSame joint)
    (congrArg Prod.snd same)

/-- A whole genuine suffix retains every labeled action, every proposal
delta, and the original chance support through actual retries and exhaustion.
The literal added word and its length remain available to endpoint readback. -/
theorem proposalRecovery_supported_suffix_of_erased_history_eq
    (first second : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryErasedHistory first =
      setup.proposalRecoveryErasedHistory second)
    {targetState : setup.proposalRecoveryProtocol.State}
    (targetTrace : setup.proposalRecoveryProtocol.Trace targetState)
    (retained : TracePrefix first.trace targetTrace) :
    ∃ (right : setup.proposalRecoveryProtocol.History)
      (word : List (Player → Option (ProposalRecoveryMove Player L))),
      TracePrefix second.trace right.trace ∧
      setup.proposalRecoveryErasedHistory ⟨targetState, targetTrace⟩ =
        setup.proposalRecoveryErasedHistory right ∧
      setup.proposalRecoveryJointRecall targetTrace =
        word ++ setup.proposalRecoveryJointRecall first.trace ∧
      setup.proposalRecoveryJointRecall right.trace =
        word ++ setup.proposalRecoveryJointRecall second.trace ∧
      targetTrace.length = first.trace.length + word.length ∧
      right.trace.length = second.trace.length + word.length := by
  induction retained with
  | refl => exact ⟨second, [], .refl, same, rfl, rfl, rfl, rfl⟩
  | @extend before after earlier kept joint legal supported ih =>
      obtain ⟨right, word, rightRetained, erased, leftWord, rightWord,
        leftLength, rightLength⟩ := ih
      obtain ⟨rightLegal, rightTarget, rightSupported, nextErased⟩ :=
        setup.proposalRecovery_supported_step_of_erased_history_eq
          ⟨before, earlier⟩ right erased joint legal supported
      refine ⟨right.extend rightLegal rightSupported, joint :: word,
        .extend rightRetained joint rightLegal rightSupported, nextErased, ?_, ?_, ?_, ?_⟩
      · change joint :: setup.proposalRecoveryJointRecall earlier = _
        rw [leftWord]
        rfl
      · change joint :: setup.proposalRecoveryJointRecall right.trace = _
        rw [rightWord]
        rfl
      · simp only [Trace.length, List.length_cons]
        omega
      · simp only [History.extend, Trace.length, List.length_cons]
        omega

end Vegas.SourceProgram.Setup
