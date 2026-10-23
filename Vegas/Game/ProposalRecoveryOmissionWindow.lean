/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryCommitWindow
import Vegas.Game.ProposalRecoveryContinuation
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryAtom
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryInvariant
import Vegas.Source.CommitRecoveryAttemptReset

/-! # Actual enriched commitment-window laws from neutral omission kernels -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

abbrev proposalRecoveryOmissionWord (history : setup.proposalRecoveryProtocol.History) :=
  setup.omissionRecall (setup.proposalRecoveryEraseTrace history.trace)

omit [Fintype Player] in
private theorem word_length (history : setup.proposalRecoveryProtocol.History) :
    (setup.proposalRecoveryOmissionWord history).length = history.trace.length := by
  simp only [proposalRecoveryOmissionWord, omissionRecall, List.length_map,
    setup.recoveryJointRecall_length, setup.proposalRecoveryEraseTrace_length]

omit [Fintype Player] in
private theorem inside_running
    (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (history : setup.proposalRecoveryProtocol.History) (kept : TracePrefix prior history.trace)
    (inside : history.trace.length + ProtocolState.commitEnd setup.program first.point <
      prior.length + ProtocolState.remaining setup.program first.point) :
    ¬ setup.proposalRecoveryProtocol.terminal history.state := by
  obtain ⟨current, same, currentCommit, _end, _rank⟩ :=
    setup.commitRecovery_prefix_inside_commit first (setup.proposalRecoveryEraseTrace prior)
      committing (setup.proposalRecoveryEraseTrace history.trace)
      (setup.proposalRecoveryEraseTrace_prefix kept)
      (by simpa only [setup.proposalRecoveryEraseTrace_length] using inside)
  rw [same]
  intro ended
  have zero := (ProtocolState.remaining_zero_iff_terminal setup.program current.point).mpr ended
  have positive := ProtocolState.commitEnd_lt_remaining setup.program current.point currentCommit
  omega

private theorem oneStep_word
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (history : setup.proposalRecoveryProtocol.History)
    (running : ¬ setup.proposalRecoveryProtocol.terminal history.state) :
    (setup.proposalRecoveryModel.runBehavioralFrom profile 1 history).map
        setup.proposalRecoveryOmissionWord =
      ((setup.proposalRecoveryModel.behavioralJoint profile history.trace running).map
        (fun draw who => CommitRecoveryMove.missed ((draw.val who).map (·.semantic)))).map
          (fun missed => missed :: setup.proposalRecoveryOmissionWord history) := by
  rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_of_not_terminal profile 0 running,
    PMF.map_bind, PMF.map_comp]
  conv_rhs => rw [← PMF.bind_pure_comp]
  apply congrArg (PMF.bind _)
  funext draw
  apply map_bindOnSupport_const
  intro target supported
  simp only [InformationModel.runBehavioralFrom, runRandomizedFor, PMF.pure_map]
  rfl

omit [Fintype Player] in
private theorem coupled_words
    (left right : PMF setup.proposalRecoveryProtocol.History)
    (images : left.map setup.proposalRecoveryOmissionWord =
      right.map setup.proposalRecoveryOmissionWord) :
    ∃ joint : PMF (setup.proposalRecoveryProtocol.History ×
        setup.proposalRecoveryProtocol.History),
      joint.map Prod.fst = left ∧ joint.map Prod.snd = right ∧
      ∀ next ∈ joint.support,
        setup.proposalRecoveryOmissionWord next.1 = setup.proposalRecoveryOmissionWord next.2 ∧
          next.1 ∈ left.support ∧ next.2 ∈ right.support := by
  let read := setup.proposalRecoveryOmissionWord
  let joint := left.bind fun prior =>
    (fiberPosterior right read (read prior)).map fun later => (prior, later)
  refine ⟨joint, ?_, ?_, ?_⟩
  · change (left.bind fun prior =>
      (fiberPosterior right read (read prior)).map fun later => (prior, later)).map Prod.fst = left
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    change (left.bind fun prior =>
      (fiberPosterior right read (read prior)).map (Function.const _ prior)) = left
    simp only [PMF.map_const, PMF.bind_pure]
  · change (left.bind fun prior =>
      (fiberPosterior right read (read prior)).map fun later => (prior, later)).map Prod.snd = right
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    change (left.bind fun prior => (fiberPosterior right read (read prior)).map id) = right
    simp only [PMF.map_id]
    change left.bind (fiberPosterior right read ∘ read) = right
    rw [← PMF.bind_map, images, fiberPosterior_reconstruct]
  · intro next supported
    obtain ⟨prior, priorSupport, laterSupport⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
    obtain ⟨later, fiberSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp laterSupport
    have observed : read prior ∈ (right.map read).support := by
      rw [← images]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨prior, priorSupport, rfl⟩
    have fiber := mem_support_fiberPosterior observed fiberSupport
    exact ⟨fiber.1.symm, priorSupport, fiber.2⟩

/-- Equal operational omission kernels determine the whole actual stopped
commitment word, including hidden value changes and arbitrary proposal labels.
The existing stopped-kernel theorem supplies the recursion. -/
theorem proposalRecovery_stopped_window_omission_eq
    (leftProfile rightProfile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (matched : ∀ (left right : setup.proposalRecoveryProtocol.History)
      (_leftKept : TracePrefix prior left.trace) (_rightKept : TracePrefix prior right.trace)
      (_word : setup.proposalRecoveryOmissionWord left = setup.proposalRecoveryOmissionWord right)
      (_inside : left.trace.length + ProtocolState.commitEnd setup.program first.point <
        prior.length + ProtocolState.remaining setup.program first.point)
      (leftRunning : ¬ setup.proposalRecoveryProtocol.terminal left.state)
      (rightRunning : ¬ setup.proposalRecoveryProtocol.terminal right.state),
      (setup.proposalRecoveryModel.behavioralJoint leftProfile left.trace leftRunning).map
          (fun draw who => CommitRecoveryMove.missed ((draw.val who).map (·.semantic))) =
        (setup.proposalRecoveryModel.behavioralJoint rightProfile right.trace rightRunning).map
          (fun draw who => CommitRecoveryMove.missed ((draw.val who).map (·.semantic)))) :
    let stopped := fun history : setup.proposalRecoveryProtocol.History =>
      prior.length + ProtocolState.remaining setup.program first.point ≤
        history.trace.length + ProtocolState.commitEnd setup.program first.point
    (setup.proposalRecoveryModel.runBehavioralUntil certificate leftProfile stopped
        ⟨some first, prior⟩).map setup.proposalRecoveryOmissionWord =
      (setup.proposalRecoveryModel.runBehavioralUntil certificate rightProfile stopped
        ⟨some first, prior⟩).map setup.proposalRecoveryOmissionWord := by
  classical
  intro stopped
  let related := fun left right : setup.proposalRecoveryProtocol.History =>
    TracePrefix prior left.trace ∧ TracePrefix prior right.trace ∧
      setup.proposalRecoveryOmissionWord left = setup.proposalRecoveryOmissionWord right ∧
        left.trace.length + ProtocolState.commitEnd setup.program first.point ≤
          prior.length + ProtocolState.remaining setup.program first.point
  apply setup.proposalRecoveryModel.runBehavioralUntil_map_eq_of_paired_steps
    setup.proposalRecoveryModel certificate certificate leftProfile rightProfile stopped stopped
    setup.proposalRecoveryOmissionWord setup.proposalRecoveryOmissionWord related
    ?_ ?_ ?_ ⟨some first, prior⟩ ⟨some first, prior⟩
      ⟨.refl, .refl, rfl, by
        have positive := ProtocolState.commitEnd_lt_remaining setup.program first.point committing
        change prior.length + ProtocolState.commitEnd setup.program first.point ≤
          prior.length + ProtocolState.remaining setup.program first.point
        omega⟩
  · intro left right equal
    obtain ⟨leftKept, rightKept, word, within⟩ := equal
    have lengths := congrArg List.length word
    rw [setup.word_length, setup.word_length] at lengths
    have stopEq : stopped left ↔ stopped right := by dsimp only [stopped]; omega
    by_cases halt : stopped left
    · have rightHalt := stopEq.mp halt
      exact ⟨fun _ => Or.inl rightHalt, fun _ => Or.inl halt⟩
    · have leftRunning := setup.inside_running first prior committing left leftKept (by
        dsimp only [stopped] at halt
        omega)
      have rightRunning := setup.inside_running first prior committing right rightKept (by
        dsimp only [stopped] at halt
        omega)
      exact or_congr stopEq (iff_of_false leftRunning rightRunning)
  · intro left right equal _halt
    exact equal.2.2.1
  · intro left right equal going leftRunning
    obtain ⟨leftKept, rightKept, word, within⟩ := equal
    have lengths := congrArg List.length word
    rw [setup.word_length, setup.word_length] at lengths
    have inside : left.trace.length + ProtocolState.commitEnd setup.program first.point <
        prior.length + ProtocolState.remaining setup.program first.point := by
      dsimp only [stopped] at going
      omega
    have rightRunning := setup.inside_running first prior committing right rightKept (by omega)
    have images :
        (setup.proposalRecoveryModel.runBehavioralFrom leftProfile 1 left).map
            setup.proposalRecoveryOmissionWord =
          (setup.proposalRecoveryModel.runBehavioralFrom rightProfile 1 right).map
            setup.proposalRecoveryOmissionWord := by
      rw [setup.oneStep_word leftProfile left leftRunning,
        setup.oneStep_word rightProfile right rightRunning,
        matched left right leftKept rightKept word inside leftRunning rightRunning, word]
    obtain ⟨joint, leftMarginal, rightMarginal, fiber⟩ := setup.coupled_words _ _ images
    refine ⟨joint, leftMarginal, rightMarginal, ?_⟩
    intro next supported
    obtain ⟨sameWord, leftSupport, rightSupport⟩ := fiber next supported
    have leftPrefix := ReachesWithin.tracePrefix
      (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin leftProfile 1 left
        next.1 leftSupport)
    have rightPrefix := ReachesWithin.tracePrefix
      (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin rightProfile 1 right
        next.2 rightSupport)
    have consumed := setup.proposalRecoveryModel.length_of_mem_support_runBehavioralFrom_one
      leftProfile leftRunning leftSupport
    exact ⟨leftKept.trans leftPrefix, rightKept.trans rightPrefix, sameWord, by omega⟩

/-- Every supported stopped endpoint is the actual close of this same
commitment window, including exhausted and reset outcomes. -/
theorem proposalRecovery_stopped_window_boundary
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (final : setup.proposalRecoveryProtocol.History)
    (supported : final ∈ (setup.proposalRecoveryModel.runBehavioralUntil certificate profile
      (fun history => prior.length + ProtocolState.remaining setup.program first.point ≤
        history.trace.length + ProtocolState.commitEnd setup.program first.point)
          ⟨some first, prior⟩).support) :
    TracePrefix prior final.trace ∧
      final.trace.length + ProtocolState.commitEnd setup.program first.point =
        prior.length + ProtocolState.remaining setup.program first.point := by
  let stopped := fun history : setup.proposalRecoveryProtocol.History =>
    prior.length + ProtocolState.remaining setup.program first.point ≤
      history.trace.length + ProtocolState.commitEnd setup.program first.point
  have kept := setup.proposalRecoveryModel.runBehavioralUntil_support_prefix certificate
    profile stopped ⟨some first, prior⟩ final supported
  have bounded := setup.proposalRecoveryModel.runBehavioralUntil_support_history_closed
    certificate profile stopped
    (fun history => history.trace.length + ProtocolState.commitEnd setup.program first.point ≤
      prior.length + ProtocolState.remaining setup.program first.point) (by
        intro history going running _within next member
        have length := setup.proposalRecoveryModel.length_of_mem_support_runBehavioralFrom_one
          profile running member
        dsimp only [stopped] at going
        omega)
    ⟨some first, prior⟩ (by
      have positive := ProtocolState.commitEnd_lt_remaining setup.program first.point committing
      change prior.length + ProtocolState.commitEnd setup.program first.point ≤
        prior.length + ProtocolState.remaining setup.program first.point
      omega) final supported
  refine ⟨kept, ?_⟩
  have halted := setup.proposalRecoveryModel.mem_support_runBehavioralUntil certificate profile
    stopped ⟨some first, prior⟩ final supported
  rcases halted with reached | ended
  · dsimp only [stopped] at reached
    omega
  · by_contra different
    have running := setup.inside_running first prior committing final kept (by omega)
    exact running ended

end Vegas.SourceProgram.Setup
