/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryOmissionKernel
import Vegas.Game.ProposalRecoveryFailedWindow

/-! # Actual local interventions inside a failed enriched commitment attempt -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
open Classical in
private theorem withLaw_at_later_clock
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (focal : Player) (origin later : setup.proposalRecoveryProtocol.History)
    (law : PMF (setup.proposalRecoveryModel.Choice focal
      (setup.proposalRecoveryModel.infoOf focal origin.trace)))
    (different : later.trace.length ≠ origin.trace.length) (who : Player) :
    (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) profile focal
      ((profile focal).withLaw (setup.proposalRecoveryModel.infoOf focal origin.trace) law)) who
        (setup.proposalRecoveryModel.infoOf who later.trace) =
      profile who (setup.proposalRecoveryModel.infoOf who later.trace) := by
  classical
  by_cases own : who = focal
  · subst who
    rw [Profile.update_same]
    apply InformationModel.BehavioralPolicy.withLaw_of_ne
    intro same
    have lengths := congrArg (fun info => info.1.2.length) same
    rw [setup.proposalRecoveryModel_word_length,
      setup.proposalRecoveryModel_word_length] at lengths
    exact different lengths
  · simp only [Profile.update_of_ne _ _ own]

variable
  (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
  (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
  (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
  (values : (who : Player) → (key : setup.ProposalRecoveryComponent who) →
    PMF (setup.CommitRecoveryValueChoice who key.1))

local notation "baseline" => setup.proposalRecoveryNormalizedTrembledProfile omission
  omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded values

open Classical in
/-- Same-current-omission local interventions have the same actual stopped
omission word. Later archive-dependent domains need not have the same laws. -/
theorem proposalRecoveryNormalizedTrembledProfile_local_window_omissions
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (leftLaw rightLaw : PMF (setup.proposalRecoveryModel.Choice focal
      (setup.proposalRecoveryModel.infoOf focal prior)))
    (marginals : leftLaw.map
        (fun choice => CommitRecoveryMove.missed (choice.val.map (·.semantic))) =
      rightLaw.map (fun choice => CommitRecoveryMove.missed (choice.val.map (·.semantic)))) :
    let altered := fun law => Profile.update
      (sig := setup.proposalRecoveryModel.behavioralSignature) baseline focal
        ((baseline focal).withLaw (setup.proposalRecoveryModel.infoOf focal prior) law)
    let stopped := fun history : setup.proposalRecoveryProtocol.History =>
      prior.length + ProtocolState.remaining setup.program first.point ≤
        history.trace.length + ProtocolState.commitEnd setup.program first.point
    (setup.proposalRecoveryModel.runBehavioralUntil certificate (altered leftLaw) stopped
        ⟨some first, prior⟩).map setup.proposalRecoveryOmissionWord =
      (setup.proposalRecoveryModel.runBehavioralUntil certificate (altered rightLaw) stopped
        ⟨some first, prior⟩).map setup.proposalRecoveryOmissionWord := by
  classical
  intro altered stopped
  apply setup.proposalRecovery_stopped_window_omission_eq _ _ certificate first prior committing
  intro left right leftKept rightKept word inside leftRunning rightRunning
  have clock : left.trace.length = right.trace.length := by
    have lengths := congrArg List.length word
    simpa only [proposalRecoveryOmissionWord, omissionRecall, List.length_map,
      setup.recoveryJointRecall_length, setup.proposalRecoveryEraseTrace_length] using lengths
  by_cases same : left.trace.length = prior.length
  · have leftEq : left = ⟨some first, prior⟩ := (leftKept.eq_of_length same.symm).symm
    have rightEq : right = ⟨some first, prior⟩ :=
      (rightKept.eq_of_length (same.symm.trans clock)).symm
    subst left
    subst right
    rw [setup.proposalRecovery_joint_missed_law, setup.proposalRecovery_joint_missed_law]
    apply congrArg independentProduct
    funext who
    by_cases own : who = focal
    · subst who
      simpa only [altered, Profile.update_same,
        InformationModel.BehavioralPolicy.withLaw_self] using marginals
    · simp only [altered, Profile.update_of_ne _ _ own]
  · have different : right.trace.length ≠ prior.length := fun equal => same (clock.trans equal)
    have leftJoint := setup.proposalRecoveryModel.behavioralJoint_congr left.trace leftRunning
      (fun who => setup.withLaw_at_later_clock baseline focal ⟨some first, prior⟩ left leftLaw
        same who)
    have rightJoint := setup.proposalRecoveryModel.behavioralJoint_congr right.trace rightRunning
      (fun who => setup.withLaw_at_later_clock baseline focal ⟨some first, prior⟩ right rightLaw
        different who)
    change (setup.proposalRecoveryModel.behavioralJoint (altered leftLaw)
      left.trace leftRunning).map _ =
        (setup.proposalRecoveryModel.behavioralJoint (altered rightLaw)
          right.trace rightRunning).map _
    rw [leftJoint, rightJoint]
    obtain ⟨currentLeft, currentRight, leftState, rightState, _leftSaved, _rightSaved,
        _leftEntry, _rightEntry, _leftGen, _rightGen, excluded, observed, _past⟩ :=
      setup.inside_attempt_public_eq focal first (setup.proposalRecoveryEraseTrace prior)
        committing (setup.proposalRecoveryEraseTrace left.trace)
        (setup.proposalRecoveryEraseTrace right.trace)
        (setup.proposalRecoveryEraseTrace_prefix leftKept)
        (setup.proposalRecoveryEraseTrace_prefix rightKept) word (by
          simpa only [setup.proposalRecoveryEraseTrace_length] using inside)
    obtain ⟨point, pointState, leftCommit, _end, _rank⟩ :=
      setup.commitRecovery_prefix_inside_commit first (setup.proposalRecoveryEraseTrace prior)
        committing (setup.proposalRecoveryEraseTrace left.trace)
        (setup.proposalRecoveryEraseTrace_prefix leftKept) (by
          simpa only [setup.proposalRecoveryEraseTrace_length] using inside)
    have equal := Option.some.inj (leftState.symm.trans pointState)
    subst point
    obtain ⟨other, otherState, rightCommit, _end, _rank⟩ :=
      setup.commitRecovery_prefix_inside_commit first (setup.proposalRecoveryEraseTrace prior)
        committing (setup.proposalRecoveryEraseTrace right.trace)
        (setup.proposalRecoveryEraseTrace_prefix rightKept) (by
          simp only [setup.proposalRecoveryEraseTrace_length]
          omega)
    have equal := Option.some.inj (rightState.symm.trans otherState)
    subst other
    have actor : ProtocolState.actor setup.program currentLeft.point =
        ProtocolState.actor setup.program currentRight.point := by
      have sameActor := congrArg (ProtocolView.actor focal setup.program) (observed focal)
      simpa only [ProtocolView.actor_publicOnly, ProtocolState.actor_observe_eq] using sameActor
    rcases left with ⟨leftState', leftTrace⟩
    rcases right with ⟨rightState', rightTrace⟩
    dsimp only at leftState rightState
    subst leftState'
    subst rightState'
    exact setup.proposalRecoveryNormalizedTrembledProfile_joint_missed_eq omission
      omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded values values currentLeft currentRight
      leftTrace rightTrace leftRunning rightRunning leftCommit rightCommit excluded actor

open Classical in
/-- Terminal play under a current local intervention splits at the actual
commitment close. Strictly later clocks then use the SAME selected baseline. -/
theorem proposalRecoveryNormalizedTrembledProfile_local_terminal_window
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (law : PMF (setup.proposalRecoveryModel.Choice focal
      (setup.proposalRecoveryModel.infoOf focal prior))) :
    let altered := Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature)
      baseline focal ((baseline focal).withLaw (setup.proposalRecoveryModel.infoOf focal prior) law)
    let stopped := fun history : setup.proposalRecoveryProtocol.History =>
      prior.length + ProtocolState.remaining setup.program first.point ≤
        history.trace.length + ProtocolState.commitEnd setup.program first.point
    setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate altered ⟨some first, prior⟩ =
      (setup.proposalRecoveryModel.runBehavioralUntil certificate altered stopped
        ⟨some first, prior⟩).bind
          (setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate baseline) := by
  classical
  intro altered stopped
  rw [setup.proposalRecoveryModel.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil
    certificate altered stopped]
  apply bind_congr_on_support
  intro boundary supported
  obtain ⟨_kept, length⟩ := setup.proposalRecovery_stopped_window_boundary
    altered certificate first prior committing boundary supported
  have positive := ProtocolState.commitEnd_lt_remaining setup.program first.point committing
  apply setup.proposalRecoveryModel.runBehavioralTerminalFrom_congr certificate boundary
  intro later reached _running who
  obtain ⟨depth, reaches⟩ := reached
  have lower := reaches.trace_length_le
  exact setup.withLaw_at_later_clock baseline focal ⟨some first, prior⟩ later law (by
    change later.trace.length ≠ prior.length
    omega) who

open Classical in
/-- In an already failed attempt, arbitrary current value/label laws with
the same omission marginal induce the same whole enriched terminal image.
The actual stopped word and shared retry continuation are both derived. -/
theorem proposalRecoveryNormalizedTrembledProfile_failed_local_terminal_eq
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (failed : first.NewFailure)
    (site : setup.proposalRecoveryModel.InfoState focal)
    (atSite : setup.proposalRecoveryModel.infoOf focal prior = site)
    (leftLaw rightLaw : PMF (setup.proposalRecoveryModel.Choice focal site))
    (marginals : leftLaw.map
        (fun choice => CommitRecoveryMove.missed (choice.val.map (·.semantic))) =
      rightLaw.map (fun choice => CommitRecoveryMove.missed (choice.val.map (·.semantic)))) :
    let altered := fun law => Profile.update
      (sig := setup.proposalRecoveryModel.behavioralSignature) baseline focal
        ((baseline focal).withLaw site law)
    (setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate (altered leftLaw)
        ⟨some first, prior⟩).map setup.proposalRecoveryErasedHistory =
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate (altered rightLaw)
        ⟨some first, prior⟩).map setup.proposalRecoveryErasedHistory := by
  subst site
  intro altered
  rw [setup.proposalRecoveryNormalizedTrembledProfile_local_terminal_window omission
      omissionNonnegative omissionBounded bad badNonnegative badBounded delivery
      deliveryNonnegative deliveryBounded values certificate focal first prior committing,
    setup.proposalRecoveryNormalizedTrembledProfile_local_terminal_window omission
      omissionNonnegative omissionBounded bad badNonnegative badBounded delivery
      deliveryNonnegative deliveryBounded values certificate focal first prior committing]
  apply setup.proposalRecovery_failed_stopped_terminal_eq _ _
    (fun who key => setup.proposalRecoveryComponentTrembledLaw who key
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded (values who key))
    certificate focal first prior committing failed
  exact setup.proposalRecoveryNormalizedTrembledProfile_local_window_omissions omission
    omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded values certificate focal first prior committing
    leftLaw rightLaw marginals

end Vegas.SourceProgram.Setup
