/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryOmissionKernel
import GameTheory.Math.Probability.ExpectationMap

/-! # Actual local continuation laws inside an already failed source attempt -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
private theorem original_clock (who : Player) (history : setup.commitRecoveryProtocol.History) :
    (setup.commitRecoveryModel.infoOf who history.trace).1.2.length = history.trace.length := by
  have clock := setup.commitRecoveryErasedModel_word_length who history.trace
  rw [setup.commitRecoveryErasedModel_infoOf] at clock
  simpa only [commitRecoveryErasedInformation, List.length_map] using clock

omit [Fintype Player] in
open Classical in
private theorem local_law_at_other_clock
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (focal : Player) (origin later : setup.commitRecoveryProtocol.History)
    (law : PMF (setup.commitRecoveryModel.Choice focal
      (setup.commitRecoveryModel.infoOf focal origin.trace)))
    (different : later.trace.length ≠ origin.trace.length) (who : Player) :
    (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) profile focal
      ((profile focal).withLaw (setup.commitRecoveryModel.infoOf focal origin.trace) law)) who
        (setup.commitRecoveryModel.infoOf who later.trace) =
      profile who (setup.commitRecoveryModel.infoOf who later.trace) := by
  classical
  by_cases own : who = focal
  · subst who
    rw [Profile.update_same]
    apply InformationModel.BehavioralPolicy.withLaw_of_ne
    intro same
    have lengths := congrArg (fun info => info.1.2.length) same
    rw [setup.original_clock, setup.original_clock] at lengths
    exact different lengths
  · simp only [Profile.update_of_ne _ _ own]

variable
  (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
  (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
  (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
    PMF (setup.CommitRecoveryValueChoice who info))

local notation "baseline" => setup.commitRecoveryNormalizedTrembledProfile omission
  omissionNonnegative omissionBounded bad badNonnegative badBounded values

open Classical in
/-- Original local interventions with the same missed-bit marginal have the
same whole commitment-window omission law, including after their values alter
later private queries. This is a direct raw-kernel comparison. -/
theorem commitRecoveryNormalizedTrembledProfile_local_window_omissions
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (leftLaw rightLaw : PMF (setup.commitRecoveryModel.Choice focal
      (setup.commitRecoveryModel.infoOf focal prior)))
    (marginals : leftLaw.map (fun choice => CommitRecoveryMove.missed choice.val) =
      rightLaw.map (fun choice => CommitRecoveryMove.missed choice.val))
    (fuel : Nat)
    (within : fuel + ProtocolState.commitEnd setup.program first.point ≤
      ProtocolState.remaining setup.program first.point) :
    let altered := fun law => Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
      baseline focal ((baseline focal).withLaw (setup.commitRecoveryModel.infoOf focal prior) law)
    (setup.commitRecoveryModel.runBehavioralFrom (altered leftLaw) fuel ⟨some first, prior⟩).map
        (fun history => setup.omissionRecall history.trace) =
      (setup.commitRecoveryModel.runBehavioralFrom (altered rightLaw) fuel ⟨some first, prior⟩).map
        (fun history => setup.omissionRecall history.trace) := by
  classical
  intro altered
  apply setup.commitRecovery_window_omission_law_eq _ _ first prior committing ?_
    fuel ⟨some first, prior⟩ ⟨some first, prior⟩ .refl .refl rfl (by dsimp only; omega)
  intro left right leftKept rightKept word inside leftRunning rightRunning
  have clock : left.trace.length = right.trace.length := by
    have lengths := congrArg List.length word
    simpa only [omissionRecall, List.length_map, setup.recoveryJointRecall_length] using lengths
  by_cases same : left.trace.length = prior.length
  · have leftEq : left = ⟨some first, prior⟩ := (leftKept.eq_of_length same.symm).symm
    have rightEq : right = ⟨some first, prior⟩ :=
      (rightKept.eq_of_length (same.symm.trans clock)).symm
    subst left
    subst right
    rw [setup.commitRecovery_joint_missed_law, setup.commitRecovery_joint_missed_law]
    apply congrArg independentProduct
    funext who
    by_cases own : who = focal
    · subst who
      simpa only [altered, Profile.update_same,
        InformationModel.BehavioralPolicy.withLaw_self] using marginals
    · simp only [altered, Profile.update_of_ne _ _ own]
  · have different : right.trace.length ≠ prior.length := fun equal => same (clock.trans equal)
    have leftJoint := setup.commitRecoveryModel.behavioralJoint_congr left.trace leftRunning
      (fun who => setup.local_law_at_other_clock baseline focal ⟨some first, prior⟩ left leftLaw
        same who)
    have rightJoint := setup.commitRecoveryModel.behavioralJoint_congr right.trace rightRunning
      (fun who => setup.local_law_at_other_clock baseline focal ⟨some first, prior⟩ right rightLaw
        different who)
    change (setup.commitRecoveryModel.behavioralJoint (altered leftLaw) left.trace leftRunning).map
      _ = (setup.commitRecoveryModel.behavioralJoint (altered rightLaw)
        right.trace rightRunning).map
        _
    rw [leftJoint, rightJoint]
    obtain ⟨currentLeft, currentRight, leftState, rightState, _leftSaved, _rightSaved,
      _leftEntry, _rightEntry, _leftGeneration, _rightGeneration, excluded, observed, _past⟩ :=
      setup.inside_attempt_public_eq focal first prior committing left.trace right.trace
        leftKept rightKept word inside
    obtain ⟨point, pointState, leftCommit, _end, _rank⟩ :=
      setup.commitRecovery_prefix_inside_commit first prior committing left.trace leftKept inside
    have equal := Option.some.inj (leftState.symm.trans pointState)
    subst point
    obtain ⟨other, otherState, rightCommit, _end, _rank⟩ :=
      setup.commitRecovery_prefix_inside_commit first prior committing right.trace rightKept
        (by omega)
    have equal := Option.some.inj (rightState.symm.trans otherState)
    subst other
    rcases left with ⟨leftState', leftTrace⟩
    rcases right with ⟨rightState', rightTrace⟩
    dsimp only at leftState rightState
    subst leftState'
    subst rightState'
    exact setup.commitRecoveryNormalizedTrembledProfile_joint_missed_eq omission
      omissionNonnegative omissionBounded bad badNonnegative badBounded values values currentLeft
      currentRight leftTrace rightTrace leftRunning rightRunning leftCommit rightCommit excluded
      observed

open Classical in
/-- Split the original locally intervened runner at its actual remaining
commitment window. Its strictly later logical clocks cannot query the old
site again, so the continuation is the SAME selected normalized baseline. -/
theorem commitRecoveryNormalizedTrembledProfile_local_terminal_window
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (fuel : Nat)
    (distance : fuel + ProtocolState.commitEnd setup.program first.saved =
      ProtocolState.remaining setup.program first.point)
    (law : PMF (setup.commitRecoveryModel.Choice focal
      (setup.commitRecoveryModel.infoOf focal prior))) :
    let altered := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
      baseline focal ((baseline focal).withLaw (setup.commitRecoveryModel.infoOf focal prior) law)
    setup.commitRecoveryModel.runBehavioralTerminalFrom certificate altered ⟨some first, prior⟩ =
      (setup.commitRecoveryModel.runBehavioralFrom altered fuel ⟨some first, prior⟩).bind
        (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate baseline) := by
  classical
  intro altered
  have ending : ProtocolState.commitEnd setup.program first.point =
      ProtocolState.commitEnd setup.program first.saved := by
    rcases setup.commitRecovery_blockFrontier prior with ⟨_saved, _live, ending⟩ | same
    · exact ending
    · rw [same]
  have positive := ProtocolState.commitEnd_lt_remaining setup.program first.point committing
  have fuelPositive : 0 < fuel := by omega
  rw [setup.commitRecoveryModel.runBehavioralTerminalFrom_eq_bind_runBehavioralFrom certificate
    altered fuel]
  apply bind_congr_on_support
  intro boundary supported
  let initial := setup.initialConfig setup.initialLaw.support_nonempty.choose
  obtain ⟨_last, _joints, _addresses, _lastState, _length, _path, consumed, _word, _signals⟩ :=
    setup.commitRecovery_run_commit_window_instructions altered initial fuel first prior
      committing distance.le boundary supported
  apply setup.commitRecoveryModel.runBehavioralTerminalFrom_congr certificate boundary
  intro later reached _running who
  obtain ⟨depth, reaches⟩ := reached
  have laterLength := reaches.trace_length_le
  exact setup.local_law_at_other_clock baseline focal ⟨some first, prior⟩ later law
    (by change later.trace.length ≠ prior.length; omega) who

open Classical in
/-- At an actual already failed commitment history, changing the current raw
law while preserving its omission marginal preserves the full original
terminal readout and payoff-vector law. The real retry or exhausted close,
future normalized play and exact remaining window are derived internally. -/
theorem commitRecoveryNormalizedTrembledProfile_failed_local_terminal_joint_eq
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (failed : first.NewFailure) (site : setup.commitRecoveryModel.InfoState focal)
    (atSite : setup.commitRecoveryModel.infoOf focal prior = site)
    (leftLaw rightLaw : PMF (setup.commitRecoveryModel.Choice focal site))
    (marginals : leftLaw.map (fun choice => CommitRecoveryMove.missed choice.val) =
      rightLaw.map (fun choice => CommitRecoveryMove.missed choice.val)) :
    let read := fun history : setup.commitRecoveryProtocol.History =>
      (setup.protocolReadout (setup.commitRecoverySourceState history.state),
        fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)
    (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
      (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) baseline focal
        ((baseline focal).withLaw site leftLaw)) ⟨some first, prior⟩).map read =
      (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) baseline focal
          ((baseline focal).withLaw site rightLaw)) ⟨some first, prior⟩).map read := by
  classical
  subst site
  intro read
  let altered := fun law => Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
    baseline focal ((baseline focal).withLaw (setup.commitRecoveryModel.infoOf focal prior) law)
  let fuel := ProtocolState.remaining setup.program first.point -
    ProtocolState.commitEnd setup.program first.saved
  have ending : ProtocolState.commitEnd setup.program first.point =
      ProtocolState.commitEnd setup.program first.saved := by
    rcases setup.commitRecovery_blockFrontier prior with ⟨_saved, _live, ending⟩ | same
    · exact ending
    · rw [same]
  have positive := ProtocolState.commitEnd_lt_remaining setup.program first.point committing
  have distance : fuel + ProtocolState.commitEnd setup.program first.saved =
      ProtocolState.remaining setup.program first.point := by dsimp only [fuel]; omega
  have omissions := setup.commitRecoveryNormalizedTrembledProfile_local_window_omissions omission
    omissionNonnegative omissionBounded
    bad badNonnegative badBounded values focal first prior committing leftLaw rightLaw marginals
    fuel (by omega)
  have shared := setup.commitRecovery_failed_window_terminal_joint_eq (altered leftLaw)
    (altered rightLaw)
    (fun who info => setup.commitRecoveryValueTremble who info omission omissionNonnegative
      omissionBounded bad badNonnegative badBounded (values who info))
    utility excludedPayoff focal first prior committing failed fuel distance omissions
  have split (law : PMF (setup.commitRecoveryModel.Choice focal
      (setup.commitRecoveryModel.infoOf focal prior))) :
      (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate (altered law)
        ⟨some first, prior⟩).map read =
      (setup.commitRecoveryModel.runBehavioralFrom (altered law) fuel ⟨some first, prior⟩).bind
        (fun boundary => (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
          baseline boundary).map read) := by
    have split := setup.commitRecoveryNormalizedTrembledProfile_local_terminal_window omission
      omissionNonnegative omissionBounded bad badNonnegative badBounded values certificate focal
      first prior committing fuel distance law
    simpa only [PMF.map_bind] using congrArg (PMF.map read) split
  change (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate (altered leftLaw)
    ⟨some first, prior⟩).map read = _
  rw [split leftLaw, split rightLaw]
  exact shared

open Classical in
/-- A prescription on genuine original histories suffices for each locally
modified terminal law. Unplayed full-information inputs are not constrained. -/
theorem commitRecoveryNormalizedTrembledProfile_local_terminal_of_prescribed
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (prescribed : ∀ who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        baseline who (setup.commitRecoveryModel.infoOf who history.trace))
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (site : setup.commitRecoveryModel.InfoState focal)
    (law : PMF (setup.commitRecoveryModel.Choice focal site))
    (history : setup.commitRecoveryProtocol.History) :
    setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
      (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
        assessment.strategy focal ((assessment.strategy focal).withLaw site law)) history =
      setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
          baseline focal ((baseline focal).withLaw site law)) history := by
  classical
  apply setup.commitRecoveryModel.runBehavioralTerminalFrom_congr certificate history
  intro later _reached running who
  by_cases own : who = focal
  · subst who
    rw [Profile.update_same, Profile.update_same]
    by_cases here : setup.commitRecoveryModel.infoOf focal later.trace = site
    · rw [here, InformationModel.BehavioralPolicy.withLaw_self,
        InformationModel.BehavioralPolicy.withLaw_self]
    · rw [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ here,
        InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ here]
      exact prescribed focal later running
  · rw [Profile.update_of_ne _ _ own, Profile.update_of_ne _ _ own]
    exact prescribed who later running

open Classical in
/-- The same raw-law comparison holds under the ACTUAL belief of an original
source assessment at a known-failed site. Every information history supplies
its genuine failed state; no Bayes relation to a no-miss representative is used. -/
theorem commitRecovery_normalized_failed_belief_terminal_joint_eq
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (prescribed : ∀ who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        baseline who (setup.commitRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (failed : ∀ history : setup.commitRecoveryModel.InformationHistory focal site.1,
      ∃ first, history.1.state = some first ∧
        ProtocolState.atCommit setup.program first.point = true ∧ first.NewFailure)
    (leftLaw rightLaw : PMF (setup.commitRecoveryModel.Choice focal site.1))
    (marginals : leftLaw.map (fun choice => CommitRecoveryMove.missed choice.val) =
      rightLaw.map (fun choice => CommitRecoveryMove.missed choice.val)) :
    let read := fun history : setup.commitRecoveryProtocol.History =>
      (setup.protocolReadout (setup.commitRecoverySourceState history.state),
        fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)
    ((assessment.belief focal site).bind fun history =>
      setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
          assessment.strategy focal ((assessment.strategy focal).withLaw site.1 leftLaw))
          history.1).map read =
      ((assessment.belief focal site).bind fun history =>
        setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
          (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
            assessment.strategy focal ((assessment.strategy focal).withLaw site.1 rightLaw))
            history.1).map read := by
  classical
  intro read
  have actual := setup.commitRecoveryNormalizedTrembledProfile_local_terminal_of_prescribed
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded values assessment
    prescribed certificate focal site.1
  simp only [PMF.map_bind]
  apply bind_congr_on_support
  intro history _supported
  rw [actual leftLaw history.1, actual rightLaw history.1]
  obtain ⟨first, state, committing, newFailure⟩ := failed history
  rcases history with ⟨⟨current, trace⟩, atSite⟩
  dsimp only at state atSite
  subst current
  exact setup.commitRecoveryNormalizedTrembledProfile_failed_local_terminal_joint_eq omission
    omissionNonnegative omissionBounded bad badNonnegative badBounded values utility excludedPayoff
    certificate focal first trace committing newFailure site.1 atSite leftLaw rightLaw marginals

open Classical in
/-- Known-failed members have equal actual conditional values for any two
current raw laws with the same omission marginal, including mixed domain laws
and accepted failure. Their original assessment belief is integrated directly. -/
theorem commitRecovery_normalized_failed_conditional_value_eq
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (prescribed : ∀ who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        baseline who (setup.commitRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (failed : ∀ history : setup.commitRecoveryModel.InformationHistory focal site.1,
      ∃ first, history.1.state = some first ∧
        ProtocolState.atCommit setup.program first.point = true ∧ first.NewFailure)
    (leftLaw rightLaw : PMF (setup.commitRecoveryModel.Choice focal site.1))
    (marginals : leftLaw.map (fun choice => CommitRecoveryMove.missed choice.val) =
      rightLaw.map (fun choice => CommitRecoveryMove.missed choice.val)) :
    (assessment.continuationContext certificate site
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((assessment.strategy focal).withLaw site.1 leftLaw) =
      (assessment.continuationContext certificate site
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          ((assessment.strategy focal).withLaw site.1 rightLaw) := by
  have joint := setup.commitRecovery_normalized_failed_belief_terminal_joint_eq omission
    omissionNonnegative omissionBounded bad badNonnegative badBounded values assessment prescribed
    utility excludedPayoff certificate focal site failed leftLaw rightLaw marginals
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    InformationModel.BehavioralAssessment.continuationContext_value]
  exact expect_observed_law_eq _ _ _ _ (fun result => result.2 focal) joint

end Vegas.SourceProgram.Setup
