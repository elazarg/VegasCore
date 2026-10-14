/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateBadMass

/-! # The completion value from a late history

**Failure, completion and bad stops.** From a history of a site at which a
binding is pending and decided by the site's key, failure is store failure of
the event (`Vegas.onePacketFailed_iff_decisionFailed_of_pending`), and every
stop of play until the event completes has completed the event;
terminal play from it fails the event exactly when the stop has, and a stop
with a completion point has not failed. So one less the failure probability
from the history is the completion mass plus the mass of bad stops, and the
stops without a completion point that are not sure to fail are bad
(`Vegas.lateStop_split`).

**The completion value.** With the completion-point law at a late binding and
the bad mass, the completion value from the history is one less its failure
probability times the history's continuation value, up to the completion-point
error plus twice the bad mass, times the payoff bound
(`Vegas.lateBinding_historyNear`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

/-- **Event-level failure is store-level failure of the pending event.** Under a
scheduler completing play, at a site with a pending event decided by its key,
every final history of play for the horizon from a history of the site is an
event-level failed history of the site's agent exactly when its store records a
failure of the event the key decides. -/
theorem onePacketFailed_iff_decisionFailed_of_pending
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    {who : Player} (site : (onePacketN).InformationSite who) {key : LateKey setup leaks}
    {event : (graph setup).EventId} (decided : decidedEvent key = some event)
    (pending : pendingEvent setup leaks who site.1 = some event)
    (history : (onePacketN).InformationHistory who site.1)
    (profile : ∀ player, (onePacketN).BehavioralPolicy player)
    (final : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (reached : final ∈ ((onePacketN).runBehavioralFrom profile (2 * horizon + 1)
      history.1).support) :
    final ∈ onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ↔
      DecisionFailed key final.state := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  have bounded := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := bounded.wellFoundedHistories
  have owned : (graph setup).actor? event = some who := by
    obtain ⟨info, decision⟩ := site
    cases info with
    | none => cases pending
    | some input => exact (pendingEvent_spec (setup := setup) pending).2.2.1
  have terminalReached : final ∈ ((onePacketN).runBehavioralTerminalFrom certificate profile
      history.1).support := by
    rw [(onePacketN).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
      bounded]
    exact reached
  have stopped := (onePacketN).runBehavioralTerminalFrom_support_terminal certificate profile
    history.1 final terminalReached
  have failedEq : onePacketFailed setup leaks bounds horizon scheduler
      ((onePacketN).agentAt site) =
      EventFailedHistory setup leaks bounds horizon scheduler who event := by
    unfold onePacketFailed
    change (match pendingEvent setup leaks who site.1 with
      | none => ∅
      | some event => EventFailedHistory setup leaks bounds horizon scheduler who event) = _
    rw [pending]
  rw [failedEq]
  have finalTrace := final.trace
  cases finalState : final.state with
  | none => rw [finalState] at stopped; exact stopped.elim
  | some control =>
      have rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler finalTrace
      rw [finalState] at rawTrace stopped
      have cutTerminal := completes control rawTrace stopped
      unfold DecisionFailed
      rw [decided]
      constructor
      · intro failedHistory
        change sourceReadout setup leaks final.state ∈ EventFailedReadout setup who event
          at failedHistory
        rw [finalState] at failedHistory
        obtain ⟨terminal, read, _, cellFailed⟩ := failedHistory
        exact ⟨by rw [cutTerminal]; exact Finset.mem_univ _,
          storeEventFailed_of_readout setup leaks control event read cellFailed⟩
      · rintro ⟨_, storeFailed⟩
        exact eventFailedHistory_of_storeEventFailed bounds horizon scheduler
          (failureProfile setup.program) completes certificate profile final
          (by rw [finalState]; exact stopped) finalState owned storeFailed

open Classical in
/-- **Failure, completion and bad stops at a stop.** From a history of a late
delivery of the binding `event`, the ready event of the site's rank, every stop
of play until the event completes splits one into terminal failure, the
completion indicator and the bad indicator; and the stops without a completion
point at which terminal play does not surely fail are bad. -/
theorem lateStop_split
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) {key : LateKey setup leaks}
    {event : (graph setup).EventId} (decided : decidedEvent key = some event)
    (pending : pendingEvent setup leaks who site.1 = some event)
    (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (ordered : execution.application.config.cut.IsPrefix (siteRank site.1))
    (ready : execution.application.config.cut.Ready event) :
    let installed := Profile.update (sig := (onePacketN).behavioralSignature)
      assessment.strategy who ((assessment.strategy who).withLaw site.1 law)
    let certificate := ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup)
      horizon scheduler).wellFoundedHistories
    let failed := onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)
    ∀ stop ∈ ((onePacketN).runBehavioralUntil certificate installed
        (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) history.1).support,
      (1 - expect ((onePacketN).runBehavioralTerminalFrom certificate installed stop)
          (fun final => if final ∈ failed then (1 : ℝ) else 0) =
        completionIndicator setup leaks bounds horizon scheduler (siteRank site.1)
            (siteFresh who site.1) stop +
          lateBadStop setup leaks bounds horizon scheduler (siteRank site.1)
            (siteFresh who site.1) event stop) ∧
      ((completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
          (siteFresh who site.1) stop = none ∧
        ¬ ∀ final ∈ ((onePacketN).runBehavioralTerminalFrom certificate installed stop).support,
          final ∈ failed) →
        lateBadStop setup leaks bounds horizon scheduler (siteRank site.1)
          (siteFresh who site.1) event stop = 1) := by
  intro installed certificate failed stop member
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketN
  have horizonBound := menu.bounded (initialLaw setup) horizon scheduler
  have freshIff : ∀ control, siteFresh who site.1 control ↔
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [siteFresh, pending]
  -- The stop has completed the event.
  have rankEq : event.val = siteRank site.1 :=
    (ready_iff_rank setup _ _ ordered event).mp ready
  have ends := model.mem_support_runBehavioralUntil certificate installed _ history.1 stop member
  obtain ⟨stopControl, stopState⟩ : ∃ control, stop.state = some control :=
    model.runBehavioralUntil_support_closed certificate installed _
      (fun reachedState => ∃ control, reachedState = some control)
      (fun state joint legal target holds reached => by
        obtain ⟨control, rfl⟩ := holds
        obtain ⟨next, rfl, _⟩ := (application setup leaks).transition_recall_prefix
          (initialLaw setup) horizon scheduler control target joint reached
        exact ⟨next, rfl⟩)
      history.1 ⟨_, current⟩ stop member
  obtain ⟨final, finalState, done⟩ : ∃ final, stop.state = some final ∧
      event ∈ final.execution.application.config.cut.completed := by
    rcases ends with ⟨control, state, prefixed⟩ | ended
    · exact ⟨control, state, (prefixed.2 event).mpr (by omega)⟩
    · rw [stopState] at ended
      have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
          scheduler).Trace (some stopControl) :=
        menu.toRawTrace (initialLaw setup) horizon scheduler (stopState ▸ stop.trace)
      refine ⟨stopControl, stopState, ?_⟩
      rw [completes stopControl rawTrace ended]
      exact Finset.mem_univ _
  -- Terminal play from the stop keeps the event's output.
  have terminalSplit := model.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate
    installed (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) history.1
  have terminalRun := model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
    horizonBound installed history.1
  obtain ⟨stored, storedEq⟩ := Option.isSome_iff_exists.mp
    ((final.execution.application.config.output_available event).mpr done)
  have finals : ∀ later ∈ (model.runBehavioralTerminalFrom certificate installed stop).support,
      (later ∈ failed ↔ StoreEventFailed final.execution.application.config.store event) := by
    intro later laterMember
    have reachedFromStart : later ∈ (model.runBehavioralFrom installed (2 * horizon + 1)
        history.1).support := by
      rw [← terminalRun, terminalSplit, PMF.mem_support_bind_iff]
      exact ⟨stop, member, laterMember⟩
    rw [onePacketFailed_iff_decisionFailed_of_pending setup leaks bounds horizon scheduler
      completes site decided pending history installed later reachedFromStart]
    obtain ⟨laterControl, laterState, keeps⟩ := model.runBehavioralTerminalFrom_support_closed
      certificate installed
      (fun reachedState => ∃ reachedControl, reachedState = some reachedControl ∧
        reachedControl.execution.application.config.store (.inr event) = some stored)
      (fun state joint legal target holds reached => by
        obtain ⟨reachedControl, rfl, keeps⟩ := holds
        obtain ⟨next, rfl, _⟩ := (application setup leaks).transition_recall_prefix
          (initialLaw setup) horizon scheduler reachedControl target joint reached
        have keptStore := (keepsStore_step (runtime setup) leaks).transition
          (initialLaw setup) horizon scheduler reachedControl next joint reached
        exact ⟨next, rfl, keptStore (.inr event) stored keeps⟩)
      stop ⟨final, finalState, by rw [EventGraph.Config.store_output, storedEq]⟩ later laterMember
    have laterDone : event ∈ laterControl.execution.application.config.cut.completed :=
      (laterControl.execution.application.config.output_available event).mp
        (by rw [← EventGraph.Config.store_output, keeps]; rfl)
    rw [laterState]
    simp only [DecisionFailed, decided]
    constructor
    · rintro ⟨_, value, valueEq, isFailed⟩
      rw [keeps] at valueEq
      cases Option.some.inj valueEq
      exact ⟨stored, by rw [EventGraph.Config.store_output, storedEq], isFailed⟩
    · rintro ⟨value, valueEq, isFailed⟩
      rw [EventGraph.Config.store_output, storedEq] at valueEq
      cases Option.some.inj valueEq
      exact ⟨laterDone, stored, keeps, isFailed⟩
  by_cases failedHere : StoreEventFailed final.execution.application.config.store event
  · have pointNone : completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
        (siteFresh who site.1) stop = none :=
      completionPoint_eq_none_of_not_fresh finalState (fun freshHere =>
        (freshIff final).mp freshHere failedHere)
    have always : expect (model.runBehavioralTerminalFrom certificate installed stop)
        (fun final => if final ∈ failed then (1 : ℝ) else 0) = 1 := by
      rw [expect_congr_on_support (g := fun _ => 1) (fun later laterMember => by
        simp only [(finals later laterMember).mpr failedHere, ↓reduceIte]), expect_constant]
    refine ⟨?_, fun ⟨_, notSure⟩ => (notSure fun later laterMember =>
      (finals later laterMember).mpr failedHere).elim⟩
    rw [always]
    simp only [completionIndicator, pointNone, Option.elim_none, lateBadStop]
    rw [ite_eq_right_iff.mpr fun bad => by
      obtain ⟨⟨control, controlState, _, notFailed⟩, _⟩ := bad
      rw [finalState] at controlState
      cases Option.some.inj controlState
      exact (notFailed failedHere).elim]
    ring
  · have never : expect (model.runBehavioralTerminalFrom certificate installed stop)
        (fun final => if final ∈ failed then (1 : ℝ) else 0) = 0 := by
      rw [expect_congr_on_support (g := fun _ => 0) (fun later laterMember => by
        simp only [show later ∉ failed from fun inFailed =>
          failedHere ((finals later laterMember).mp inFailed), ↓reduceIte]), expect_constant]
    rw [never, sub_zero]
    cases pointEq : completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
        (siteFresh who site.1) stop with
    | none =>
        have bad : lateBadStop setup leaks bounds horizon scheduler (siteRank site.1)
            (siteFresh who site.1) event stop = 1 := by
          simp only [lateBadStop, pointEq]
          rw [ite_eq_left_iff.mpr fun notBad => (notBad ⟨⟨final, finalState, done, failedHere⟩,
            trivial⟩).elim]
        refine ⟨?_, fun _ => bad⟩
        rw [bad]
        simp only [completionIndicator, pointEq, Option.elim_none, zero_add]
    | some target =>
        refine ⟨?_, fun ⟨pointNone, _⟩ => by cases pointNone⟩
        simp only [completionIndicator, lateBadStop, pointEq, Option.elim_some, reduceCtorEq,
          and_false, ↓reduceIte, add_zero]

section Value

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- **The completion value from a late history.** Under a scheduler completing
play, with every binding value bounded and a positive candidate capacity, let a
history of a late delivery of the binding `event` of `who` decode at the site's
rank to an intended point reached by the intended game, with nothing sent for
the event. If the profile installing `law` at the site plays the late owner
shape and its completion mass after committing at a permitted slot depends, up
to `η`, on the slot alone, the completion value from the history is one less
its failure probability times the history's continuation value, up to twice
the cube of the scale plus `η`, plus twice the cube of the scale, per step of
the horizon, times the payoff bound. -/
theorem lateBinding_historyNear [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).History]
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) {scale : ℝ} (positive : 0 < scale)
    (le_one : scale ≤ 1) {slots : Nat} (slotsLe : slots ≤ bounds.candidateCount)
    (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) {key : LateKey setup leaks}
    {event : (graph setup).EventId} (decided : decidedEvent key = some event)
    (pending : pendingEvent setup leaks who site.1 = some event)
    (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall who) event = false)
    (ordered : execution.application.config.cut.IsPrefix (siteRank site.1))
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank site.1) execution.application.config =
      some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (reachedPoint : IntendedReached setup point)
    (shape : LateOwnerShapeFrom setup leaks bounds horizon scheduler source positive.le le_one
      slots (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
        ((assessment.strategy who).withLaw site.1 law)) who event execution)
    {η : ℝ} (η_nonneg : 0 ≤ η)
    (successFree : ∀ (later : ((bounds.onePacketMenu (runtime setup) leaks).protocol
        (initialLaw setup) horizon scheduler).History) (laterRemaining : Nat)
        (reached : (application setup leaks).Execution),
      later.state = some ⟨laterRemaining, some who, reached⟩ →
      LateUnsent setup leaks who event execution.application.config (execution.recall who)
        later.state →
      (reached.recall who = execution.recall who →
        reached.observe (application setup leaks) who =
          execution.observe (application setup leaks) who) →
      (reached.recall who ≠ execution.recall who → ∃ response,
        execution.recall who ++ [respondEntry setup leaks execution who response] <+:
          reached.recall who) →
      ∀ slot < bounds.candidateCount,
        countPermits ((application setup leaks).outputs (reached.recall who))
          (slotEnvelope setup leaks who (reached.recall who)
            (reached.observe (application setup leaks) who) event slot) = true →
        ∃ factor : ℝ, ∀ choice ∈ (asIfHonestProfile setup leaks source who
            (some (reached.recall who, reached.observe (application setup leaks) who))).support,
          ∀ next : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
              horizon scheduler).History,
            next.state = some ⟨laterRemaining, none, reached.respond (application setup leaks)
              who (slotResponse setup leaks who (reached.recall who)
                (reached.observe (application setup leaks) who) event slot choice)⟩ →
            |expect ((onePacketN).runBehavioralUntil
                ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
                  scheduler).wellFoundedHistories
                (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy
                  who ((assessment.strategy who).withLaw site.1 law))
                (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) next)
                (completionIndicator setup leaks bounds horizon scheduler (siteRank site.1)
                  (siteFresh who site.1)) - factor| ≤ η)
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound) :
    |historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment (setup.intendedOpeningProfile source.strategy) site law history.1 -
      (1 - siteHistoryFailure setup leaks bounds horizon scheduler assessment site law history) *
        decodedPointValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          (setup.intendedOpeningProfile source.strategy) who (siteRank site.1) history.1| ≤
      (2 * (scale ^ 3 + η) * (2 * horizon + 1) + 2 * (scale ^ 3 * (2 * horizon + 1))) *
        bound := by
  classical
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketN
  have horizonBound := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := horizonBound.wellFoundedHistories
  let installed := Profile.update (sig := (onePacketN).behavioralSignature)
    assessment.strategy who ((assessment.strategy who).withLaw site.1 law)
  let profile := setup.intendedOpeningProfile source.strategy
  let stopped := LateStopped setup leaks bounds horizon scheduler (siteRank site.1)
  let untilLaw := model.runBehavioralUntil certificate installed stopped history.1
  let failed := onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)
  let bad := lateBadStop setup leaks bounds horizon scheduler (siteRank site.1)
    (siteFresh who site.1) event
  have freshIff : ∀ control, siteFresh who site.1 control ↔
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [siteFresh, pending]
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans (readoutBounded none)
  have pointLaw := lateBinding_completionPointLaw completes covers capacity source positive
    le_one slotsLe installed history.1 current node turn unrecorded ordered decoded intendedPoint
    (fun control failedHere freshHere => (freshIff control).mp freshHere failedHere) shape
    η_nonneg successFree
  have badMass := lateBinding_badMass completes covers capacity source positive le_one slotsLe
    installed history.1 current node turn unrecorded ordered decoded intendedPoint freshIff shape
  have split := lateStop_split setup leaks bounds horizon scheduler completes assessment site
    decided pending law history current ordered ready
  have badBounded : ∀ stop, |bad stop| ≤ 1 := by
    intro stop
    simp only [bad, lateBadStop]
    split <;> norm_num
  have badNonneg : ∀ stop, 0 ≤ bad stop := by
    intro stop
    simp only [bad, lateBadStop]
    split <;> norm_num
  -- The stops without a completion point that are not sure to fail are bad.
  have badLaw : expect untilLaw (fun stop => if completionPoint setup leaks bounds horizon
        scheduler (siteRank site.1) (siteFresh who site.1) stop = none ∧
      ¬ ∀ final ∈ (model.runBehavioralTerminalFrom certificate installed stop).support,
        final ∈ failed then 1 else 0) ≤ scale ^ 3 * (2 * horizon + 1) := by
    refine le_trans (expect_mono (fun stop member => ?_) (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)) badMass
    split
    · rename_i unsure
      rw [(split stop member).2 unsure]
    · exact badNonneg stop
  have near := abs_historyStopValue_sub_le_of_completionPointLaw setup leaks bounds horizon
    scheduler parameter utility excludedPayoff assessment profile site law history.1 _ _
    readoutBounded pointLaw badLaw
  rw [expect_sourcePointValue_behavioralStateStep setup parameter utility excludedPayoff profile
    who readoutBounded point] at near
  -- The continuation value at the history is the source value at the decoded point.
  have pointValue : decodedPointValue setup leaks bounds horizon scheduler parameter utility
      excludedPayoff profile who (siteRank site.1) history.1 =
      sourcePointValue setup parameter utility excludedPayoff profile who point := by
    unfold decodedPointValue
    rw [current]
    dsimp only
    rw [decoded]
    dsimp only
    rw [ite_eq_left reachedPoint ..]
  have valueBounded : |sourcePointValue setup parameter utility excludedPayoff profile who point|
      ≤ bound := expect_abs_le_of_bounded boundNonneg fun readout => readoutBounded readout
  -- One less the failure probability is the completion mass plus the bad mass.
  have failureEq : 1 - siteHistoryFailure setup leaks bounds horizon scheduler assessment site
      law history = expect untilLaw (completionIndicator setup leaks bounds horizon scheduler
        (siteRank site.1) (siteFresh who site.1)) + expect untilLaw bad := by
    have runEq : localHistoryRun (2 * horizon + 1) assessment site law history =
        untilLaw.bind (model.runBehavioralTerminalFrom certificate installed) := by
      change model.runBehavioralFrom installed (2 * horizon + 1) history.1 = _
      rw [← model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
        horizonBound installed history.1]
      exact model.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate installed
        stopped history.1
    unfold siteHistoryFailure
    rw [runEq, expect_bind_tower_bounded _ _ _ (C := 1) (fun final => by
        split <;> norm_num),
      ← expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
    have oneSub : ∀ f : (menu.protocol (initialLaw setup) horizon scheduler).History → ℝ,
        1 - expect untilLaw f = expect untilLaw (fun stop => 1 - f stop) := fun f => by
      rw [expect_sub (payoffIntegrable_constant _ 1) (payoffIntegrable_of_finite _ _),
        expect_constant]
    rw [oneSub]
    exact expect_congr_on_support fun stop member => (split stop member).1
  rw [pointValue, failureEq]
  calc _ ≤ |historyStopValue setup leaks bounds horizon scheduler parameter utility
          excludedPayoff assessment profile site law history.1 -
        expect untilLaw (completionIndicator setup leaks bounds horizon scheduler
          (siteRank site.1) (siteFresh who site.1)) *
          sourcePointValue setup parameter utility excludedPayoff profile who point| +
        |expect untilLaw bad| * |sourcePointValue setup parameter utility excludedPayoff
          profile who point| := by
        rw [← abs_mul]
        refine le_trans (le_of_eq ?_) (abs_sub _ _)
        congr 1
        ring
    _ ≤ (2 * (scale ^ 3 + η) * (2 * horizon + 1) + scale ^ 3 * (2 * horizon + 1)) * bound +
        scale ^ 3 * (2 * horizon + 1) * bound := by
        refine add_le_add near (mul_le_mul ?_ valueBounded (abs_nonneg _) (by positivity))
        rw [abs_of_nonneg (by apply expect_nonneg; intro stop _; exact badNonneg stop)]
        exact badMass
    _ = _ := by ring

end Value

end Vegas
