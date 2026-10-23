/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.IntendedCommitGain

/-! # Source points reached by one legal intended commitment -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- A legal source choice at its owner's actual turn reaches a point of the
intended game. Only the active coordinate of the joint source action matters. -/
theorem intendedChoice_sourceStep_reached {who : Player}
    (site : setup.intendedModel.InformationSite who)
    (choice : setup.intendedModel.Choice who site.1)
    (history : setup.intendedModel.InformationHistory who site.1)
    {point : ProtocolState setup.program} (state : history.1.state = some point)
    (acts : ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) =
      some who) (target : ProtocolState setup.program)
    (member : target ∈ (ProtocolState.step setup.program point (fun _ => choice.1)).support) :
    IntendedReached setup target := by
  let M := setup.intendedModel
  let E := setup.intendedProtocol
  obtain ⟨info, decision⟩ := site
  obtain ⟨start, observed⟩ := history
  change M.infoOf who start.trace = info at observed
  subst observed
  change start.state = some point at state
  have running : ¬ E.terminal start.state := by
    rw [state]
    exact ProtocolState.not_terminal_of_actor who who setup.program point acts
  have active : E.active start.state who := by
    rw [state]
    exact acts
  let draw := M.jointOfChoice (setup.protocol_singleMover
    (CommitmentInterface.values setup.program)) start running who active choice
  have chosen : draw.1 who = choice.1 := by
    change E.singletonJoint who choice.1 who = choice.1
    exact E.singletonJoint_self who choice.1
  have reached : some target ∈ (E.step start.state draw).support := by
    let joint : Player → Option (OwnAction Player L) := draw.1
    have law := congrArg (fun current : setup.ProtocolState => setup.protocolStep current joint)
      state
    change some target ∈ (setup.protocolStep start.state joint).support
    rw [law]
    change some target ∈ ((ProtocolState.step setup.program point joint).map some).support
    apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨target, ?_, rfl⟩
    have chosenJoint : joint who = choice.1 := chosen
    rw [ProtocolState.step_eq_of_actor who who setup.program point joint acts, chosenJoint]
    exact member
  exact ⟨start.extend draw.2 reached, rfl⟩

/-- An intended source deviation cannot improve on exclusion merely by causing
its future continuation to fail: every reachable continuation is worth at least
that exclusion payoff. The utility assumption concerns actual intended terminals. -/
theorem intendedChoice_sourceStep_value_lower [Finite Player]
    (wellFormed : setup.WellFormed)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    {who : Player} (upper : ℝ) (le_upper : ∀ outcome, utility outcome who ≤ upper)
    (site : setup.intendedModel.InformationSite who)
    (choice : setup.intendedModel.Choice who site.1)
    (history : setup.intendedModel.InformationHistory who site.1)
    {point : ProtocolState setup.program} (state : history.1.state = some point)
    (acts : ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) =
      some who) {bound : ℝ}
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound) :
    excludedPayoff who ≤ expect (ProtocolState.step setup.program point (fun _ => choice.1))
      (sourcePointValue setup parameter utility excludedPayoff
        (setup.intendedOpeningProfile assessment.strategy) who) := by
  classical
  let := Fintype.ofFinite Player
  let law := ProtocolState.step setup.program point (fun _ => choice.1)
  let value := sourcePointValue setup parameter utility excludedPayoff
    (setup.intendedOpeningProfile assessment.strategy) who
  have valueBounded : ∀ target, |value target| ≤ bound := fun _ =>
    expect_abs_le_of_bounded ((abs_nonneg _).trans (readoutBounded none)) readoutBounded
  have lower : ∀ target ∈ law.support, excludedPayoff who ≤ value target := by
    intro target member
    exact (sourcePointValue_mem_Icc setup parameter utility excludedPayoff
      (setup.intendedOpeningProfile assessment.strategy) who upper le_upper
      (fun point reached => excludedPayoff_le_of_reached setup parameter utility excludedPayoff
        wellFormed below assessment.strategy point reached who) target
      (intendedChoice_sourceStep_reached site choice history state acts target member)).1
  have mean := expect_mono (μ := law) (f := fun _ => excludedPayoff who) lower
    (payoffIntegrable_constant _ _) (payoffIntegrable_of_bounded _ _ valueBounded)
  simpa only [expect_constant] using mean
/-- Uniformly bounded source readouts bound every source continuation gain. -/
theorem intended_historyGain_abs_le_of_readoutBounded [Fintype Player]
    (assessment : setup.intendedModel.BehavioralAssessment)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {who : Player} {bound : ℝ}
    (nonnegative : 0 ≤ bound)
    (bounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound)
    (deviation : setup.intendedModel.AssessmentDeviation who)
    (history : setup.intendedModel.InformationHistory who deviation.1.1) :
    |setup.intendedModel.historyGain
      (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
      (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
      assessment deviation history| ≤ 2 * bound := by
  have each : ∀ final : setup.intendedProtocol.History,
      |payoffComponent setup
        (intendedReadoutExclusion setup parameter utility excludedPayoff final) who| ≤ bound :=
    fun _ => bounded _
  unfold InformationModel.historyGain
  rw [expect_map, expect_map]
  simp only [Function.comp_def]
  have first := expect_abs_le_of_bounded (μ := setup.intendedModel.truncatedRunner
    (instructionCount setup.program + 1) (Profile.update
      (sig := setup.intendedModel.behavioralSignature) assessment.strategy who deviation.2)
    history.1) nonnegative each
  have second := expect_abs_le_of_bounded (μ := setup.intendedModel.truncatedRunner
    (instructionCount setup.program + 1) (Profile.update
      (sig := setup.intendedModel.behavioralSignature) assessment.strategy who
      (assessment.strategy who)) history.1) nonnegative each
  exact (abs_sub _ _).trans (by linarith)

end Vegas
