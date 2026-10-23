/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryPooledCompletion
import Vegas.Game.ProposalRecoveryOmissionKernel
import Vegas.Source.ProposalRecoveryNoMissFixed

/-! # Deterministic ordinary classes of actual enriched information agents -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  [Fintype setup.proposalRecoveryProtocol.History]

omit [Fintype Player] [Fintype setup.proposalRecoveryProtocol.History] in
private theorem key_committing (who : Player)
    (info : setup.proposalRecoveryModel.InfoState who) :
    (setup.proposalRecoveryQuery who info).1.1.1.1.elim false
        (ProtocolView.atCommit who setup.program) =
      info.1.1.1.elim false (ProtocolView.atCommit who setup.program) := by
  let old := setup.proposalRecoveryEraseInfo who info
  have typed : (setup.commitRecoveryNoMissInformation who old).1.1.1 = old.1.1.1 := by
    unfold commitRecoveryNoMissInformation
    split
    · exact (setup.commitRecoveryWithAttemptExclusions_controls who _ _ old).1
    · rfl
  change ((setup.commitRecoveryNoMissInformation who old).1.1.1.map
    (ProtocolView.eraseHistory who setup.program)).elim false
      (ProtocolView.atCommit who setup.program) = _
  rw [typed]
  change (info.1.1.1.map (ProtocolView.eraseHistory who setup.program)).elim false
    (ProtocolView.atCommit who setup.program) = _
  cases observed : info.1.1.1 with
  | none => rfl
  | some view => exact ProtocolView.atCommit_eraseHistory who setup.program view

open Classical in
def proposalRecoveryOrdinaryAgents (focal : Player)
    (source : setup.proposalRecoveryModel.InformationSite focal) :
    Finset (setup.proposalRecoveryModel.InformationAgent
      setup.proposalRecoveryModel.playedInformation) :=
  let _ := Fintype.ofFinite (setup.proposalRecoveryModel.InformationSite focal)
  ((Finset.univ : Finset (setup.proposalRecoveryModel.InformationSite focal)).filter
    (fun site => setup.commitRecoveryErasedInformation focal
        (setup.proposalRecoveryEraseInfo focal site.1) =
          setup.commitRecoveryErasedInformation focal
            (setup.proposalRecoveryEraseInfo focal source.1) ∧
      setup.proposalRecoveryArchive focal site.1 =
        setup.proposalRecoveryArchive focal source.1)).image
        setup.proposalRecoveryModel.agentAt

open Classical in
theorem proposalRecoveryOrdinaryAgents_subset_pool (focal : Player)
    (source : setup.proposalRecoveryModel.InformationSite focal) :
    setup.proposalRecoveryOrdinaryAgents focal source ⊆ Finset.univ.filter
      (fun agent => setup.proposalRecoveryAgentPool agent =
        setup.proposalRecoveryAgentPool (setup.proposalRecoveryModel.agentAt source)) := by
  intro agent member
  obtain ⟨site, selected, rfl⟩ := Finset.mem_image.mp member
  obtain ⟨semantic, archive⟩ := (Finset.mem_filter.mp selected).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  apply congrArg (Sigma.mk focal)
  apply Subtype.ext
  apply Prod.ext
  · change setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal
          (setup.proposalRecoveryEraseInfo focal site.1)) =
      setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal
          (setup.proposalRecoveryEraseInfo focal source.1))
    rw [setup.commitRecoveryNoMissInformation_erased,
      setup.commitRecoveryNoMissInformation_erased, semantic]
  · exact archive

open Classical in
omit [Fintype Player] in
theorem proposalRecovery_agentAt_mem_ordinary (focal : Player)
    (source : setup.proposalRecoveryModel.InformationSite focal) :
    setup.proposalRecoveryModel.agentAt source ∈
      setup.proposalRecoveryOrdinaryAgents focal source := by
  let _ := Fintype.ofFinite (setup.proposalRecoveryModel.InformationSite focal)
  exact Finset.mem_image.mpr ⟨source,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩, rfl⟩

open Classical in
omit [Fintype Player] in
/-- Complement membership is a property of the FULL original information
site, not of a selected subset of its belief. Every history in that site is
therefore actually known-failed and can use the checked failed-context law. -/
theorem proposalRecovery_pool_complement_known_failed
    (focal : Player) (source : setup.proposalRecoveryModel.InformationSite focal)
    (first : CommitRecoveryState setup.program)
    (firstTrace : setup.proposalRecoveryProtocol.Trace (some first))
    (sourceAt : setup.proposalRecoveryModel.infoOf focal firstTrace = source.1)
    (firstCommit : ProtocolState.atCommit setup.program first.point = true)
    (unchanged : first.excluded = first.entryExcluded)
    (agent : setup.proposalRecoveryModel.InformationAgent
      setup.proposalRecoveryModel.playedInformation)
    (samePool : setup.proposalRecoveryAgentPool agent =
      setup.proposalRecoveryAgentPool (setup.proposalRecoveryModel.agentAt source))
    (outside : agent ∉ setup.proposalRecoveryOrdinaryAgents focal source)
    (decision : setup.proposalRecoveryModel.IsDecisionInfo agent.1 agent.2.val) :
    ∀ history : setup.proposalRecoveryModel.InformationHistory agent.1 agent.2.val,
      ∃ current : CommitRecoveryState setup.program,
        history.1.state = some current ∧
        ProtocolState.atCommit setup.program current.point = true ∧ current.NewFailure := by
  classical
  let _ := Fintype.ofFinite (setup.proposalRecoveryModel.InformationSite focal)
  rcases agent with ⟨owner, info⟩
  have ownerEq := congrArg Sigma.fst samePool
  change owner = focal at ownerEq
  subst owner
  let target : setup.proposalRecoveryModel.InformationSite focal := ⟨info.val, decision⟩
  have agentEq : (⟨focal, info⟩ : setup.proposalRecoveryModel.InformationAgent
      setup.proposalRecoveryModel.playedInformation) = setup.proposalRecoveryModel.agentAt target :=
    rfl
  rw [agentEq] at samePool outside
  have keys : setup.proposalRecoveryQuery focal target.1 =
      setup.proposalRecoveryQuery focal source.1 :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp samePool).2)
  have sourceClock : source.1.1.1.1.elim false
      (ProtocolView.atCommit focal setup.program) = true := by
    rw [← sourceAt]
    change (setup.proposalRecoveryEraseInfo focal
      (setup.proposalRecoveryModel.infoOf focal firstTrace)).1.1.1.elim false _ = true
    rw [setup.proposalRecoveryEraseInfo_current]
    simpa only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
      ProtocolState.atCommit_observe] using firstCommit
  intro history
  rcases history with ⟨⟨lastState, lastTrace⟩, targetAt⟩
  have active := InformationModel.InformationSite.active setup.proposalRecoveryModel
    target ⟨⟨lastState, lastTrace⟩, targetAt⟩
  cases lastState with
  | none =>
      change False at active
      exact active.elim
  | some last =>
      have targetClock := congrArg (fun key => key.1.1.1.1.elim false
        (ProtocolView.atCommit focal setup.program)) keys
      rw [setup.key_committing, setup.key_committing] at targetClock
      have clock := targetClock.trans sourceClock
      rw [← targetAt] at clock
      change (setup.proposalRecoveryEraseInfo focal
        (setup.proposalRecoveryModel.infoOf focal lastTrace)).1.1.1.elim false _ = true at clock
      rw [setup.proposalRecoveryEraseInfo_current] at clock
      have lastCommit : ProtocolState.atCommit setup.program last.point = true := by
        simpa only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
          ProtocolState.atCommit_observe] using clock
      have same := keys.symm
      rw [← sourceAt, ← targetAt] at same
      rcases setup.proposalRecovery_query_fiber_cases focal first last firstTrace lastTrace
          unchanged same with ordinary | failed
      · have fields : setup.commitRecoveryErasedInformation focal
              (setup.proposalRecoveryEraseInfo focal target.1) =
            setup.commitRecoveryErasedInformation focal
              (setup.proposalRecoveryEraseInfo focal source.1) ∧
          setup.proposalRecoveryArchive focal target.1 =
            setup.proposalRecoveryArchive focal source.1 := by
          rw [← sourceAt, ← targetAt]
          exact ⟨ordinary.1.symm, ordinary.2.symm⟩
        exact (outside (Finset.mem_image.mpr ⟨target,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, fields⟩, rfl⟩)).elim
      · exact ⟨last, rfl, lastCommit, failed⟩

end Vegas.SourceProgram.Setup
