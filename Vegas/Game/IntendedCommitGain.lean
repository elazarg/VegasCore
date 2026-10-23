/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketPrescribedCompletion
import Vegas.Game.AsyncDeviationForeign

/-! # The gain of a commitment in the intended game

**Intended play from a history reads out the opening's continuation value.**
For a well-formed setup, the expected exclusion payoff of intended play of a
profile from a history, for enough steps, is the expected exclusion payoff of
the continuation of its intended effective opening from the history's state
(`Vegas.intended_expect_readout_runFrom`).

**The gain of committing a choice.** At a history of the intended game at a
point where who acts, committing a choice at the history's information state
gains, against intended play of an assessment, the expected source continuation
value of the assessment's intended effective opening after the source step of
that choice, less its value at the point
(`Vegas.intendedCommit_historyGain`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- **Intended play from a history reads out the opening's continuation
value.** For a well-formed setup, from every history of the intended game,
the expected exclusion payoff of who under intended play of a profile, for
enough steps, is the expected exclusion payoff of who at the readout of the
continuation of the profile's intended effective opening from the history's
state. -/
theorem intended_expect_readout_runFrom (wellFormed : setup.WellFormed)
    (policies : ∀ who, setup.intendedModel.BehavioralPolicy who) (fuel : Nat)
    (history : setup.intendedProtocol.History)
    (enough : setup.protocolRemaining history.state ≤ fuel) (who : Player) :
    expect ((setup.intendedModel.runBehavioralFrom policies fuel history).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff))
        (payoffComponent setup · who) =
      expect ((setup.continuationLaw (setup.intendedOpeningProfile policies)
          history.state).map some)
        (fun readout => exclusionReadoutUtility setup parameter utility excludedPayoff readout
          who) := by
  rw [expect_map, ← setup.intendedOpeningProfile_runFrom wellFormed policies fuel history enough,
    expect_map]
  rfl

omit [Fintype Player] in
/-- A point's remaining instructions are at most the program's. -/
private theorem remaining_le_instructionCount (point : ProtocolState setup.program)
    (who : Player) :
    setup.protocolRemaining (some point) ≤ instructionCount setup.program := by
  have total := ProtocolView.position_add_remaining who setup.program point
  change ProtocolState.remaining setup.program point ≤ _
  omega

open Classical in
/-- **The gain of committing a choice.** For a well-formed setup, with the
exclusion payoff of who bounded at every readout, at a history of the
intended game at a point where who acts, committing a choice at the
history's information state gains, against intended play of an assessment
truncated after as many steps as the program has instructions plus one, the
expected source continuation value of the assessment's intended effective
opening after the source step of that choice, less its value at the point. -/
theorem intendedCommit_historyGain (wellFormed : setup.WellFormed)
    (assessment : setup.intendedModel.BehavioralAssessment) {who : Player}
    (site : setup.intendedModel.InformationSite who)
    (choice : setup.intendedModel.Choice who site.1)
    (history : setup.intendedModel.InformationHistory who site.1)
    {point : ProtocolState setup.program} (state : history.1.state = some point)
    (acts : ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) =
      some who)
    {bound : ℝ} (readoutBounded : ∀ readout, |exclusionReadoutUtility setup parameter utility
      excludedPayoff readout who| ≤ bound) :
    setup.intendedModel.historyGain
        (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
        (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
        assessment (site, (assessment.strategy who).commit site.1 choice) history =
      expect (ProtocolState.step setup.program point
          (fun _ => (choice.1 : Option (OwnAction Player L))))
          (sourcePointValue setup parameter utility excludedPayoff
            (setup.intendedOpeningProfile assessment.strategy) who) -
        sourcePointValue setup parameter utility excludedPayoff
          (setup.intendedOpeningProfile assessment.strategy) who point := by
  let M := setup.intendedModel
  let E := setup.intendedProtocol
  let fuel := instructionCount setup.program
  let value := fun readout => exclusionReadoutUtility setup parameter utility excludedPayoff
    readout who
  obtain ⟨info, decision⟩ := site
  obtain ⟨current, atSite⟩ := history
  change M.infoOf who current.trace = info at atSite
  subst atSite
  change current.state = some point at state
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans (readoutBounded none)
  have hterm : ¬ E.terminal current.state := by
    rw [state]
    exact ProtocolState.not_terminal_of_actor who who setup.program point acts
  have hactive : E.active current.state who := by
    rw [state]
    exact acts
  have actsOnce := (setup.intendedModel_decisionRecall).actsOnceWhereItMatters
  have enough : setup.protocolRemaining current.state ≤ fuel + 1 := by
    rw [state]
    exact (remaining_le_instructionCount setup point who).trans (Nat.le_succ _)
  -- The baseline: intended play from the history.
  have baseline := intended_expect_readout_runFrom setup parameter utility excludedPayoff
    wellFormed (Profile.update (sig := M.behavioralSignature) assessment.strategy who
      (assessment.strategy who)) (fuel + 1) current enough who
  rw [Profile.update_eq_self, state] at baseline
  -- After the commitment, play is intended play.
  let committed := Profile.update (sig := M.behavioralSignature) assessment.strategy who
    ((assessment.strategy who).commit (M.infoOf who current.trace) choice)
  have after : ∀ (draw : { joint : ∀ i, Option (E.Action i) // E.Legal current.state joint })
      (target : E.State) (realized : target ∈ (E.step current.state draw).support),
      M.runBehavioralFrom committed fuel (current.extend draw.2 realized) =
        M.runBehavioralFrom assessment.strategy fuel (current.extend draw.2 realized) := by
    intro draw target realized
    refine M.runBehavioralFrom_congr fuel _ fun later reach running player => ?_
    by_cases same : player = who
    · subst player
      simp only [committed, Profile.update_same]
      have agree := M.withLaw_eq_commit_after_actsOnce actsOnce (assessment.strategy who)
        (M.infoOf who current.trace) (assessment.strategy who (M.infoOf who current.trace))
        choice rfl hactive draw.2 realized later reach running
      rw [BehavioralPolicy.withLaw_eq_self] at agree
      exact agree.symm
    · simp only [committed, Profile.update_of_ne _ _ same]
  have readoutBounded' : ∀ final : E.History,
      |payoffComponent setup (intendedReadoutExclusion setup parameter utility excludedPayoff
        final) who| ≤ bound := fun final => readoutBounded _
  have readout : ∀ later : E.History, setup.protocolRemaining later.state ≤ fuel →
      expect (M.runBehavioralFrom assessment.strategy fuel later) (fun final =>
        payoffComponent setup (intendedReadoutExclusion setup parameter utility excludedPayoff
          final) who) =
        expect ((setup.continuationLaw (setup.intendedOpeningProfile assessment.strategy)
          later.state).map some) value := fun later enoughLater =>
    (expect_map _ _ _).symm.trans (intended_expect_readout_runFrom setup parameter utility
      excludedPayoff wellFormed assessment.strategy fuel later enoughLater who)
  have afterValue : ∀ (draw : { joint : ∀ i, Option (E.Action i) // E.Legal current.state joint })
      (target : E.State) (realized : target ∈ (E.step current.state draw).support),
      expect (M.runBehavioralFrom committed fuel (current.extend draw.2 realized)) (fun final =>
        payoffComponent setup (intendedReadoutExclusion setup parameter utility excludedPayoff
          final) who) =
        expect ((setup.continuationLaw (setup.intendedOpeningProfile assessment.strategy)
          target).map some) value := by
    intro draw target realized
    rw [after]
    have consumed := setup.protocol_remaining_step current.state target draw.1 hterm realized
    exact readout (current.extend draw.2 realized) (by
      change setup.protocolRemaining target ≤ fuel
      omega)
  -- The deviation: one step of the commitment, then intended play.
  have deviation : expect ((M.runBehavioralFrom committed (fuel + 1) current).map
      (intendedReadoutExclusion setup parameter utility excludedPayoff))
      (payoffComponent setup · who) =
      expect (ProtocolState.step setup.program point
          (fun _ => (choice.1 : Option (OwnAction Player L))))
        (sourcePointValue setup parameter utility excludedPayoff
          (setup.intendedOpeningProfile assessment.strategy) who) := by
    rw [expect_map, M.runBehavioralFrom_succ_of_not_terminal _ fuel hterm]
    change expect _ (fun final => payoffComponent setup
      (intendedReadoutExclusion setup parameter utility excludedPayoff final) who) = _
    rw [expect_bind_tower_bounded _ _ _ readoutBounded']
    have joint := M.behavioralJoint_eq_map_of_at_most_one_active committed current.trace hterm
      who (fun player active => setup.protocol_singleMover
        (CommitmentInterface.values setup.program) current.state active hactive)
    have committedWho : committed who (M.infoOf who current.trace) = PMF.pure choice := by
      simp only [committed, Profile.update_same, BehavioralPolicy.commit_self]
    rw [joint, committedWho, PMF.pure_map, expect_pure]
    rw [expect_bindOnSupport_tower_on_support _ _ _
      (payoffIntegrable_of_bounded _ _ readoutBounded')
      (fun target => expect ((setup.continuationLaw
        (setup.intendedOpeningProfile assessment.strategy) target).map some) value)
      (fun target realized => ?_)]
    · change expect (setup.protocolStep current.state (E.singletonJoint who choice.1)) _ = _
      generalize choice.1 = action
      rw [state]
      change expect ((ProtocolState.step setup.program point
        (E.singletonJoint who action)).map some) _ = _
      have single : E.singletonJoint who action who = action := by
        simp [ExecutionProtocol.singletonJoint]
      rw [expect_map, ProtocolState.step_eq_of_actor who who setup.program point _ acts, single]
      rfl
    · exact (afterValue _ target realized).symm
  unfold InformationModel.historyGain
  change expect ((M.runBehavioralFrom committed (fuel + 1) current).map _) _ -
    expect ((M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
      assessment.strategy who (assessment.strategy who)) (fuel + 1) current).map _) _ = _
  rw [deviation, Profile.update_eq_self, baseline]
  rfl

end Vegas
