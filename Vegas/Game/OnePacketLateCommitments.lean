/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateDecomposition
import Vegas.Game.IntendedCommitGain

/-! # Late commitments of intended values

**The value of committing a choice at a site.** The belief average, over the
histories of a site, of the source continuation value after the source step of
a choice at the decoded point of the site's rank (`Vegas.siteCommitValue`).

**Value-blind late commitments.** At a forced late delivery at which the player
owes no failure, a choice committing an intended value at a prepared slot fails
as the late option sending at that slot does, and its completion value is its
success probability times the value of committing that value at the site, up to
an error (`Vegas.LateCommitBlind`). This is the value blindness of late success
for a single committed value: the success of a late packet depends neither on
the committed value nor, under the belief, on the hidden values the
continuation depends on.
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
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

open Classical in
/-- **The value of committing a choice at a site history.** The expected source
continuation value of `profile` after the source step of `choice` at the point
the history's configuration decodes to after `rank` events, when that point is a
point of the intended game; the exclusion payoff otherwise. -/
def decodedCommitValue (profile : BehavioralProfile setup.program) (who : Player) (rank : Nat)
    (choice : Option (OwnAction Player L))
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History) : ℝ :=
  match history.state with
  | none => excludedPayoff who
  | some control =>
      match sourceServicePrefix? setup rank control.execution.application.config with
      | none => excludedPayoff who
      | some point =>
          if IntendedReached setup point then
            expect (ProtocolState.step setup.program point fun _ => choice)
              (sourcePointValue setup parameter utility excludedPayoff profile who)
          else excludedPayoff who

/-- **The value of committing a choice at a site.** The belief average, over the
histories of a site, of the value of committing the choice at their decoded
point of the site's rank. -/
def siteCommitValue (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (choice : Option (OwnAction Player L)) : ℝ :=
  expect (assessment.belief who site) fun history =>
    decodedCommitValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
      profile who (siteRank site.1) choice history.1

/-- **Value-blind late commitments.** At every forced late delivery at which the
player owes no failure, every choice at the player's own turn committing, at a
prepared slot below `slots`, a value whose decoded source choice is intended
fails within `blindError n` of the late option sending at that slot, and its
completion value is within `blindError n` of its success probability times the
value of committing that source choice at the site. -/
def LateCommitBlind (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (blindError : ℕ → ℝ) : Prop :=
  ∀ n who (site : (onePacketN).InformationSite who),
    ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
    ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
      ((onePacketN).agentAt site) →
    SiteDebtFree setup leaks bounds horizon scheduler site →
    ∀ (choice : (onePacketN).Choice who site.1)
      (past : List (application setup leaks).PlayerEntry)
      (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
      (material : (application setup leaks).Submission) (event : (graph setup).EventId)
      (serial : Nat) (payload : L.Ty)
      (outputEq : (graph setup).outputLayout event = .binding who payload) (value : L.Val payload),
      site.1 = some (past, view) → choice.1 = some response →
      response.transmission = some material →
      material.call.packet = .commitment event (who, .prepared serial) →
      view.application.publicView.ownTurn? who = some event →
      material.call.candidateAfter who view.application.candidates (.prepared serial) =
        .openable ⟨payload, value⟩ →
      sourceOfValue setup event outputEq value ∈
        setup.intendedMenu who (projectView setup leaks who site.1) →
      ∀ inRange : serial < slots,
        |onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (PMF.pure choice) -
          onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n ((onePacketN).agentAt site)
              (some ⟨serial, inRange⟩))| ≤ blindError n ∧
        |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
            (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
            (PMF.pure choice) -
          (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (PMF.pure choice)) *
            siteCommitValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
              (sourceOfValue setup event outputEq value)| ≤ blindError n

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
open Classical in
/-- **Committing at a forced history is a source gain.** For a well-formed setup,
at a decision input of `who` showing its own turn, from a history in a forced
state at which `who` owes no failure, the value of committing a source choice
less the value at the decoded point is the intended history gain of committing
that choice at the projected site, at the history's replay. -/
theorem decodedCommitValue_sub_eq_historyGain (wellFormed : setup.WellFormed)
    (assessment : setup.intendedModel.BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1))
    (choice : setup.intendedModel.Choice who (projectView setup leaks who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    (forced : ForcedState setup leaks who history.1.state)
    (notOwed : ∀ point, nativeDecodedState setup leaks history.1.state = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound) :
    decodedCommitValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        (setup.intendedOpeningProfile assessment.strategy) who (siteRank site.1) choice.1
        history.1 -
      decodedPointValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        (setup.intendedOpeningProfile assessment.strategy) who (siteRank site.1) history.1 =
      setup.intendedModel.historyGain
        (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
        (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
        assessment (projectedSite setup leaks decision,
          (assessment.strategy who).commit (projectView setup leaks who site.1) choice)
        (replayProjection setup leaks bounds horizon scheduler (projectedSite setup leaks decision)
          site atSite rfl history) := by
  obtain ⟨native, seen⟩ := history
  have seenSite : (onePacketInformation setup leaks bounds horizon scheduler).infoOf who
      native.trace = some (past, view) := seen.trans atSite
  obtain ⟨state, trace⟩ := native
  change (onePacketInformation setup leaks bounds horizon scheduler).infoOf who trace = _
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
  change ForcedState setup leaks who (some ⟨remaining, some who, execution⟩) at forced
  obtain ⟨point, decoded, forcedPoint⟩ := (forcedState_iff_decodedPoint _).mp forced
  have free : ∀ point', decodedPoint setup execution.application.config = some point' →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point' := by
    intro found foundDecoded player
    rw [decoded, Option.some.injEq] at foundDecoded
    subst foundDecoded
    by_cases same : player = who
    · subst same
      exact notOwed point decoded
    · exact (forcedPoint.2 player same).2
  obtain ⟨replay, replayed⟩ := intendedHistory?_isSome_of_debtFree wellFormed trace _ rfl free
  have replayState : replay.state = some point :=
    (intendedHistory?_state trace replayed).trans decoded
  have projectEq := replayProjection_eq (sourceSite := projectedSite setup leaks decision)
    atSite rfl ⟨⟨_, trace⟩, seen⟩ replayed
  -- The site's rank is the configuration's completed prefix.
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
      scheduler trace
  obtain ⟨rank, ordered, _⟩ := pendingAt_history rawTrace
  have rankEq : siteRank site.1 = rank := by
    rw [atSite]
    change (execution.application.config.history.map EventGraph.Completion.event).length = rank
    rw [List.length_map]
    exact history_length_of_isPrefix _ ordered
  have prefixEq : sourceServicePrefix? setup (siteRank site.1) execution.application.config =
      some point := by
    rw [rankEq, ← decodedPoint_eq_of_isPrefix ordered]
    exact decoded
  obtain ⟨publicReady, owned⟩ := PublicView.ownTurn?_spec _ who event turn
  have ready : execution.application.config.cut.Ready event :=
    (State.publicView_eventReady _ event).mp publicReady
  have acting : ProtocolView.actor who setup.program
      (ProtocolState.observe who setup.program point) = some who :=
    (decodedPoint_actor who ready decoded).trans owned
  have gain := intendedCommit_historyGain setup parameter utility excludedPayoff wellFormed
    assessment (projectedSite setup leaks decision) choice
    (replayProjection setup leaks bounds horizon scheduler (projectedSite setup leaks decision)
      site atSite rfl ⟨⟨_, trace⟩, seen⟩) (by rw [projectEq]; exact replayState) acting
    readoutBounded
  refine Eq.trans ?_ gain.symm
  have reached : IntendedReached setup point := ⟨replay, replayState⟩
  unfold decodedCommitValue decodedPointValue
  simp only [prefixEq, reached, ↓reduceIte]

end Vegas
