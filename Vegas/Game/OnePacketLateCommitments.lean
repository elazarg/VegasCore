module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.IntendedCommitGain
public import Vegas.Game.OnePacketDecodedActor
public import Vegas.Game.OnePacketCompletionPotential
public import Vegas.Game.OnePacketLateDecomposition
public import Vegas.Game.OnePacketProjectedDecision
public import Vegas.Game.OnePacketReplayInputs
public import Vegas.Game.OnePacketBeliefWiring
public import Vegas.Game.OnePacketForcedPrefix
public import Vegas.Game.IntendedChoiceReach

@[expose] public section

/-! # Source gains of committed values

A committed source choice has the intended history gain at the replay of a
forced debt-free history. Averaging gives a source gain with posterior and
unforced-history errors. One-packet commitments use the bounded prepared slots.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon scheduler

omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
open Classical in
/-- **Committing at a forced history is a source gain.** For a well-formed setup,
at a decision input of `who` showing its own turn, from a history in a forced
state at which `who` owes no failure, the value of committing a source choice
less the value at the decoded point is the intended history gain of committing
that choice at the projected site, at the history's replay. -/
theorem decodedCommitValue_sub_eq_historyGain (wellFormed : setup.WellFormed)
    (assessment : setup.intendedModel.BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) {past : List (application setup timeouts
      leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup timeouts leaks who
      site.1))
    (choice : setup.intendedModel.Choice who (projectView setup timeouts leaks who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    (forced : ForcedState setup timeouts leaks who history.1.state)
    (notOwed : ∀ point, nativeDecodedState setup timeouts leaks history.1.state = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound) :
    decodedCommitValue setup timeouts leaks bounds horizon scheduler parameter utility
      excludedPayoff
        (setup.intendedOpeningProfile assessment.strategy) who (siteRank (timeouts := timeouts)
          site.1) choice.1
        history.1 -
      decodedPointValue setup timeouts leaks bounds horizon scheduler parameter utility
        excludedPayoff
        (setup.intendedOpeningProfile assessment.strategy) who (siteRank (timeouts := timeouts)
          site.1) history.1 =
      setup.intendedModel.historyGain
        (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
        (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
        assessment (projectedSite setup timeouts leaks decision,
          (assessment.strategy who).commit (projectView setup timeouts leaks who site.1) choice)
        (replayProjection setup timeouts leaks bounds horizon scheduler (projectedSite setup
          timeouts leaks decision)
          site atSite rfl history) := by
  obtain ⟨native, seen⟩ := history
  have seenSite : (onePacketInformation setup timeouts leaks bounds horizon scheduler).infoOf who
      native.trace = some (past, view) := seen.trans atSite
  obtain ⟨state, trace⟩ := native
  change (onePacketInformation setup timeouts leaks bounds horizon scheduler).infoOf who trace = _
    at seenSite
  rw [onePacket_infoOf] at seenSite
  cases state with
  | none => cases seenSite
  | some control =>
  rcases control with ⟨remaining, actor, execution⟩
  by_cases active : actor = some who
  swap
  · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seenSite
    cases seenSite
  subst active
  simp only [ReactiveApplication.observe, ↓reduceIte] at seenSite
  obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj seenSite)
  subst pastEq viewEq
  change ForcedState setup timeouts leaks who (some ⟨remaining, some who, execution⟩) at forced
  obtain ⟨point, decoded, forcedPoint⟩ := (forcedState_iff_decodedPoint (timeouts := timeouts) _).mp
    forced
  have free : ∀ point', decodedPoint setup execution.application.config = some point' →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point' := by
    intro found foundDecoded player
    rw [decoded, Option.some.injEq] at foundDecoded
    subst foundDecoded
    by_cases same : player = who
    · subst same
      exact notOwed point decoded
    · exact (forcedPoint.2 player same).2
  obtain ⟨replay, replayed⟩ := intendedHistory?_isSome_of_debtFree (timeouts := timeouts) wellFormed
    trace _ rfl free
  have replayState : replay.state = some point :=
    (intendedHistory?_state (timeouts := timeouts) trace replayed).trans decoded
  have projectEq := replayProjection_eq (timeouts := timeouts) (sourceSite := projectedSite setup
    timeouts leaks decision)
    atSite rfl ⟨⟨_, trace⟩, seen⟩ replayed
  -- The site's rank is the configuration's completed prefix.
  have rawTrace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon
      scheduler trace
  obtain ⟨rank, ordered, _⟩ := pendingAt_history (timeouts := timeouts) rawTrace
  have rankEq : siteRank (timeouts := timeouts) site.1 = rank := by
    rw [atSite]
    change (execution.application.config.history.map EventCompletion.event).length = rank
    rw [List.length_map]
    exact history_length_of_isPrefix _ ordered
  have prefixEq : sourceServicePrefix? setup (siteRank (timeouts := timeouts) site.1)
    execution.application.config =
      some point := by
    rw [rankEq, ← decodedPoint_eq_of_isPrefix ordered]
    exact decoded
  obtain ⟨publicReady, owned⟩ := PublicView.ownTurn?_spec _ who event turn
  have ready : execution.application.config.cut.Ready event :=
    (State.publicView_eventReady _ event).mp publicReady
  have acting : ProtocolView.actor who setup.program
      (ProtocolState.observe who setup.program point) = some who :=
    (decodedPoint_actor_of_history who rawTrace ready decoded).trans owned
  have gain := intendedCommit_historyGain setup parameter utility excludedPayoff wellFormed
    assessment (projectedSite setup timeouts leaks decision) choice
    (replayProjection setup timeouts leaks bounds horizon scheduler (projectedSite setup timeouts
      leaks decision)
      site atSite rfl ⟨⟨_, trace⟩, seen⟩) (by rw [projectEq]; exact replayState) acting
    readoutBounded
  refine Eq.trans ?_ gain.symm
  have reached : IntendedReached setup point := ⟨replay, replayState⟩
  unfold decodedCommitValue decodedPointValue
  simp only [prefixEq, reached, ↓reduceIte]

omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- The value of committing a choice at a site history is bounded by a bound on
the exclusion payoff and the readout utility. -/
theorem abs_decodedCommitValue_le (profile : BehavioralProfile setup.program) (who : Player)
    (rank : Nat) (choice : Option (OwnAction Player L))
    (history : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).History) {bound : ℝ}
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound) :
    |decodedCommitValue setup timeouts leaks bounds horizon scheduler parameter utility
      excludedPayoff
        profile who rank choice history| ≤ bound := by
  classical
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans excludedBounded
  have pointBound : ∀ point, |sourcePointValue setup parameter utility excludedPayoff profile
      who point| ≤ bound := fun point => expect_abs_le_of_bounded boundNonneg readoutBounded
  unfold decodedCommitValue
  split
  · exact excludedBounded
  · split
    · exact excludedBounded
    · split
      · exact expect_abs_le_of_bounded boundNonneg pointBound
      · exact excludedBounded

omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- The value at the decoded point of a site history is bounded by a bound on the
exclusion payoff and the readout utility. -/
theorem abs_decodedPointValue_le (profile : BehavioralProfile setup.program) (who : Player)
    (rank : Nat)
    (history : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).History) {bound : ℝ}
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound) :
    |decodedPointValue setup timeouts leaks bounds horizon scheduler parameter utility
      excludedPayoff
        profile who rank history| ≤ bound := by
  classical
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans excludedBounded
  unfold decodedPointValue
  split
  · exact excludedBounded
  · split
    · exact excludedBounded
    · split
      · exact expect_abs_le_of_bounded boundNonneg readoutBounded
      · exact excludedBounded

omit [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
open Classical in
/-- **The value of committing at a site is a source gain.** For a well-formed
setup, at a decision input of `who` showing its own turn at which `who` owes no
failure, the value of committing a source choice at the site less the site's
continuation value is within the following of the intended gain of committing
it at the projected site: twice the bound times the `ℓ¹` distance of the
projected belief from the intended belief, plus four times the bound times the
belief mass outside the forced region. -/
theorem abs_siteCommitValue_sub_le [Finite setup.intendedProtocol.History]
    (wellFormed : setup.WellFormed)
    (target : (onePacketN).BehavioralAssessment)
    (source : setup.intendedModel.BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) {past : List (application setup timeouts
      leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup timeouts leaks who
      site.1))
    (choice : setup.intendedModel.Choice who (projectView setup timeouts leaks who site.1))
    (debtFree : SiteDebtFree setup timeouts leaks bounds horizon scheduler site)
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound) :
    |siteCommitValue setup timeouts leaks bounds horizon scheduler parameter utility excludedPayoff
      target
        (setup.intendedOpeningProfile source.strategy) site choice.1 -
      siteValue setup timeouts leaks bounds horizon scheduler parameter utility excludedPayoff
        target
        (setup.intendedOpeningProfile source.strategy) site -
      intendedSiteGain setup parameter utility excludedPayoff source
        (projectedSite setup timeouts leaks decision,
          (source.strategy who).commit (projectView setup timeouts leaks who site.1) choice)| ≤
      2 * bound * ∑' point, |(((target.belief who site).map
          (replayProjection setup timeouts leaks bounds horizon scheduler
            (projectedSite setup timeouts leaks decision) site atSite rfl)) point).toReal -
        ((source.belief who (projectedSite setup timeouts leaks decision)) point).toReal| +
      4 * bound * expect (target.belief who site) (fun history =>
        if ForcedState setup timeouts leaks who history.1.state then (0 : ℝ) else 1) := by
  let := Fintype.ofFinite (setup.intendedModel.InformationHistory who
    (projectedSite setup timeouts leaks decision).1)
  rw [tsum_fintype]
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans excludedBounded
  set project := replayProjection setup timeouts leaks bounds horizon scheduler
    (projectedSite setup timeouts leaks decision) site atSite rfl
  set gain := setup.intendedModel.historyGain
    (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
    (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
    source (projectedSite setup timeouts leaks decision,
      (source.strategy who).commit (projectView setup timeouts leaks who site.1) choice)
  set outside := fun history : (onePacketN).InformationHistory who site.1 =>
    if ForcedState setup timeouts leaks who history.1.state then (0 : ℝ) else 1
  set difference := fun history : (onePacketN).InformationHistory who site.1 =>
    decodedCommitValue setup timeouts leaks bounds horizon scheduler parameter utility
      excludedPayoff
        (setup.intendedOpeningProfile source.strategy) who (siteRank (timeouts := timeouts) site.1)
          choice.1
        history.1 -
      decodedPointValue setup timeouts leaks bounds horizon scheduler parameter utility
        excludedPayoff
        (setup.intendedOpeningProfile source.strategy) who (siteRank (timeouts := timeouts) site.1)
          history.1
  have finalBounded : ∀ final : setup.intendedProtocol.History,
      |payoffComponent setup (intendedReadoutExclusion setup parameter utility excludedPayoff
        final) who| ≤ bound := fun final => readoutBounded _
  have gainBound : ∀ point, |gain point| ≤ 2 * bound := by
    intro point
    simp only [gain, InformationModel.historyGain]
    rw [expect_map, expect_map]
    calc _ ≤ _ := abs_sub _ _
      _ ≤ bound + bound := add_le_add
          (expect_abs_le_of_bounded boundNonneg fun final => finalBounded final)
          (expect_abs_le_of_bounded boundNonneg fun final => finalBounded final)
      _ = 2 * bound := by ring
  -- Forced histories transport exactly; the rest is bounded by the belief mass.
  have pointwise : ∀ history, |difference history - gain (project history)| ≤
      4 * bound * outside history := by
    intro history
    by_cases forced : ForcedState setup timeouts leaks who history.1.state
    · simp only [outside, forced, ↓reduceIte, mul_zero, abs_nonpos_iff, sub_eq_zero]
      exact decodedCommitValue_sub_eq_historyGain setup timeouts leaks bounds horizon scheduler
        parameter utility excludedPayoff wellFormed source site atSite turn decision choice
        history forced (debtFree history) readoutBounded
    · simp only [outside, forced, ↓reduceIte, mul_one]
      have commit := abs_le.mp (abs_decodedCommitValue_le setup timeouts leaks bounds horizon
        scheduler
        parameter utility excludedPayoff (setup.intendedOpeningProfile source.strategy) who
        (siteRank (timeouts := timeouts) site.1) choice.1 history.1 readoutBounded excludedBounded)
      have value := abs_le.mp (abs_decodedPointValue_le setup timeouts leaks bounds horizon
        scheduler
        parameter utility excludedPayoff (setup.intendedOpeningProfile source.strategy) who
        (siteRank (timeouts := timeouts) site.1) history.1 readoutBounded excludedBounded)
      have projected := abs_le.mp (gainBound (project history))
      simp only [difference]
      rw [abs_le]
      constructor <;> linarith [commit.1, commit.2, value.1, value.2, projected.1, projected.2]
  have siteEq : siteCommitValue setup timeouts leaks bounds horizon scheduler parameter utility
      excludedPayoff target (setup.intendedOpeningProfile source.strategy) site choice.1 -
      siteValue setup timeouts leaks bounds horizon scheduler parameter utility excludedPayoff
        target
        (setup.intendedOpeningProfile source.strategy) site =
      expect (target.belief who site) difference := by
    unfold siteCommitValue siteValue
    exact (expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).symm
  have sourceEq : intendedSiteGain setup parameter utility excludedPayoff source
      (projectedSite setup timeouts leaks decision,
        (source.strategy who).commit (projectView setup timeouts leaks who site.1) choice) =
      expect (source.belief who (projectedSite setup timeouts leaks decision)) gain :=
    setup.intendedModel.gain_eq_expect_historyGain _ _ _ source _
  rw [siteEq, sourceEq]
  -- The histories outside the forced region.
  have upper := expect_mono (μ := target.belief who site)
    (f := fun history => difference history - gain (project history))
    (g := fun history => 4 * bound * outside history)
    (fun history _ => (abs_le.mp (pointwise history)).2)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  have lower := expect_mono (μ := target.belief who site)
    (f := fun history => -(4 * bound * outside history))
    (g := fun history => difference history - gain (project history))
    (fun history _ => (abs_le.mp (pointwise history)).1)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  rw [expect_const_mul] at upper
  rw [expect_neg, expect_const_mul] at lower
  rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)] at upper lower
  -- The projected belief against the intended belief.
  have transport : |expect (target.belief who site) (fun history => gain (project history)) -
      expect (source.belief who (projectedSite setup timeouts leaks decision)) gain| ≤
      2 * bound * ∑ point, |(((target.belief who site).map project) point).toReal -
        ((source.belief who (projectedSite setup timeouts leaks decision)) point).toReal| := by
    rw [show (fun history => gain (project history)) = gain ∘ project from rfl, ← expect_map,
      expect_eq_sum, expect_eq_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun point _ => ?_)
    rw [← sub_mul, abs_mul, mul_comm (2 * bound)]
    exact mul_le_mul_of_nonneg_left (gainBound point) (abs_nonneg _)
  have bounds := abs_le.mp transport
  exact abs_le.mpr ⟨by linarith [bounds.1], by linarith [bounds.2]⟩

omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **One-packet commitments use the bounded slots.** A transmitting response of
the one-packet menu committing an event to a prepared slot commits to one of
the first `candidateCount` slots. -/
theorem onePacket_commitment_serial_lt {who : Player}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} {response : (application setup timeouts
      leaks).Action}
    (member : response ∈ bounds.onePacketActions timeouts leaks who past view)
    {material : (application setup timeouts leaks).Submission}
    (sends : response.transmission = some material) {event : (graph setup).EventId}
    {owner : Player} {serial : Nat}
    (packet : material.call.packet = .commitment event (owner, .prepared serial)) :
    serial < bounds.candidateCount := by
  obtain ⟨inMenu, _⟩ := (bounds.mem_onePacketActions timeouts leaks who past view
    response).mp member
  have allowed := (bounds.menu_mem timeouts leaks who past view response).mp inMenu
  rw [sends] at allowed
  have handle := allowed.1.1.1
  rw [packet] at handle
  exact handle

end Vegas
