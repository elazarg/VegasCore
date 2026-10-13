/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCommitmentCompletion
import Vegas.Game.OnePacketCompletionTransport
import Vegas.Game.IntendedCommitGain

/-! # The gain of an intended commitment at a regular history

**The assembled law at a forced first activation.** At a forced agent outside
the late pools, the assembled profile plays the slot-trembled prescribed
component of the source assessment (`Vegas.assembled_strategy_of_unpooled`).

**Canonical decisions at a binding transmit.** Along every history of the
one-packet game, the canonical decision of every successful value at a binding
of the player's turn transmits (`Vegas.canonicalTransmitsAt_of_binding`).

**The gain of an intended commitment.** At a forced first activation outside
the late pools for a binding, at a history whose decoded point has no player
owing a failure, a choice committing a value whose source action is intended at
the projected view gains at most what committing that source action gains in the
intended game at the replay of the history, up to twice the transport error plus
twelve times the scale times the payoff range
(`Vegas.onePacket_commitment_gain_le_of_regular`).
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
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

/-- **The assembled law at a forced first activation.** At a forced agent
outside the late pools, the assembled profile plays the slot-trembled
prescribed component of the source assessment. -/
theorem assembled_strategy_of_unpooled
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence)
    (n : ℕ) {who : Player} (site : (onePacketN).InformationSite who)
    (forced : ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    (unkeyed : ¬ ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
      ((onePacketN).agentAt site)) :
    (targetSequence n).strategy who site.1 =
      slotPrescribedComponent setup leaks bounds (initialLaw setup) horizon scheduler
        (sequence n) (scale n) (scale_pos n).le (scale_le_one n) who site.1 := by
  rw [assembled n]
  have atAgent := (onePacketN).agentBehavior_at (onePacketN).playedInformation
    (onePacketFallback setup leaks bounds horizon scheduler)
    (fun agent => (weights n (onePacketPool setup leaks bounds horizon scheduler agent)).bind
      (freeKeyedComponent
        (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
        (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n)
        (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n) agent)) ((onePacketN).agentAt site)
  refine atAgent.trans ?_
  obtain ⟨identify, components⟩ := freeKeyedComponent_of_not_free
    (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
    (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one n)
    (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one (slots := slots) n) (key := agentLateKey setup leaks bounds (initialLaw setup)
        horizon scheduler) forced
  have constant : ∀ part, freeKeyedComponent
      (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
      (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) ((onePacketN).agentAt site) part =
      onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n ((onePacketN).agentAt site) := fun part => by
    rw [components part]
    exact keyedComponent_of_not_keyed _ _ unkeyed _
  change (weights n _).bind _ = _
  rw [show (freeKeyedComponent
      (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
      (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) ((onePacketN).agentAt site)) =
      fun _ => onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n ((onePacketN).agentAt site) from funext constant, PMF.bind_const]
  rfl

variable {setup leaks bounds horizon scheduler} in
omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **Canonical decisions at a binding transmit.** Along every history of the
one-packet game, at a binding of who, the canonical decision of every encoded
source action transmits. -/
theorem canonicalTransmitsAt_of_binding {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId) {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) :
    CanonicalTransmitsAt setup leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event := by
  intro action graphAction _ _ _
  obtain ⟨serial, selected⟩ := onePacket_canonicalFreshSlot_exists trace who
  obtain ⟨choice, rfl⟩ : ∃ choice : PublicationResult (L.Val payload),
      graphAction = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
    ⟨cast (congrArg EventGraph.EventField.Action outputEq) graphAction, by simp⟩
  rw [(runtime setup).canonicalServiceDecision_binding leaks who _ _ event payload outputEq
    codeEq node serial selected choice]
  exact Option.some_ne_none _

open Classical in
/-- **The gain of an intended commitment at a regular history.** For a
well-formed setup under the asynchronous contract with timely delays and
retention of first covered canonical packets, with bounded utilities, at a
forced first activation outside the late pools of an assembled profile, pending
at a binding, let a choice transmit a commitment of the event to a prepared slot
of who whose meaning after the submission is a value decoding to a source action
in the intended menu at the projected view. Then at every history of the site
whose decoded point has no player owing a failure, the gain of the choice is at
most the gain, in the intended game at the replay of the history, of committing
that source action at the projected site, up to twice the transport error plus
twelve times the scale times the payoff range. -/
theorem onePacket_commitment_gain_le_of_regular (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence)
    (n : ℕ) {who : Player} (site : (onePacketN).InformationSite who)
    (forced : ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    (unkeyed : ¬ ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
      ((onePacketN).agentAt site))
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (choice : (onePacketN).Choice who site.1) {response : (application setup leaks).Action}
    (selected : choice.1 = some response) (material : (application setup leaks).Submission)
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    {value : L.Val payload}
    (after : material.call.candidateAfter who view.application.candidates (.prepared serial) =
      .openable ⟨payload, value⟩)
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1))
    (offered : sourceOfValue setup event outputEq value ∈
      setup.intendedMenu who (projectView setup leaks who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    (regular : ∀ point, nativeDecodedState setup leaks history.1.state = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point) :
    (onePacketN).historyGain ((onePacketN).truncatedRunner (2 * horizon + 1))
        (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
          utility excludedPayoff) (payoffComponent setup) (targetSequence n)
        (site, ((targetSequence n).strategy who).withLaw site.1 (PMF.pure choice)) history ≤
      setup.intendedModel.historyGain
          (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
          (intendedReadoutExclusion setup parameter utility excludedPayoff)
          (payoffComponent setup) (sequence n)
          (projectedSite setup leaks decision, ((sequence n).strategy who).commit
            (projectView setup leaks who site.1)
            ⟨sourceOfValue setup event outputEq value, offered⟩)
          (replayProjection setup leaks bounds horizon scheduler
            (projectedSite setup leaks decision) site atSite rfl history) +
        (2 * (((Fintype.card Player * (2 * horizon + 1) : ℕ) * (1 - slotRetention (scale n))) *
            (max 0 (max (excludedPayoff who) (upperUtility who)) -
              min 0 (min (excludedPayoff who) (lowerUtility who)))) +
          12 * scale n * (max 0 (max (excludedPayoff who) (upperUtility who)) -
            min 0 (min (excludedPayoff who) (lowerUtility who)))) := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let low := min 0 (min (excludedPayoff who) (lowerUtility who))
  let range := max 0 (max (excludedPayoff who) (upperUtility who)) - low
  have zeroWithin : low ≤ 0 ∧ 0 ≤ low + range :=
    ⟨min_le_left _ _, by
      simp only [low, range]
      linarith [le_max_left 0 (max (excludedPayoff who) (upperUtility who))]⟩
  have readoutBounded : ∀ readout, |exclusionReadoutUtility setup parameter utility
      excludedPayoff readout who| ≤ range := fun readout => by
    have within := exclusionReadoutUtility_mem_Icc setup parameter utility excludedPayoff
      lowerUtility upperUtility lower_le le_upper readout who
    exact abs_le.mpr ⟨by simp only [range]; linarith [within.1, zeroWithin.2],
      by simp only [range, low]; linarith [within.2, zeroWithin.1]⟩
  -- The history is at the decision of who.
  obtain ⟨start, observed⟩ := history
  change ∀ point, nativeDecodedState setup leaks start.state = some point → _ at regular
  have observedState : (application setup leaks).observe who start.state = site.1 :=
    (menu.info (initialLaw setup) horizon scheduler who start.trace).symm.trans observed
  rcases startState : start.state with _ | ⟨remaining, actor, execution⟩
  · rw [startState, atSite] at observedState
    cases observedState
  rw [startState] at observedState regular
  have actorEq : actor = some who := by
    by_contra different
    simp only [ReactiveApplication.observe, different, ↓reduceIte] at observedState
    rw [atSite] at observedState
    cases observedState
  subst actorEq
  simp only [ReactiveApplication.observe, ↓reduceIte] at observedState
  rw [atSite] at observedState
  obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj observedState)
  subst pastEq viewEq
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := startState ▸ start.trace
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    menu.toRawTrace (initialLaw setup) horizon scheduler trace
  have pendingAt := pending
  rw [atSite] at pendingAt
  obtain ⟨turn, readyView, owned, _⟩ := pendingEvent_spec pendingAt
  have turnExecution : execution.application.publicView.ownTurn? who = some event := turn
  have ready := (execution.application.publicView_eventReady event).mp readyView
  have never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry :=
    fun entry member activated => unkeyed
      ⟨⟨_, _, event, atSite, pending, entry, member, activated⟩, forced⟩
  -- The decoded point.
  obtain ⟨found, foundOrdered, _⟩ := pendingAt_history rawTrace
  have rankEq : siteRank site.1 = found := by
    rw [atSite]
    change (execution.application.config.history.map EventGraph.Completion.event).length = found
    rw [List.length_map]
    exact history_length_of_isPrefix _ foundOrdered
  have ordered : execution.application.config.cut.IsPrefix (siteRank site.1) :=
    rankEq ▸ foundOrdered
  obtain ⟨decodedRank, ⟨residual⟩, holds⟩ := decodedState_intended_or_owes wellFormed
    (failureProfile setup.program) menu horizon scheduler trace _ rfl
  have sameRank := isPrefix_unique residual.checkpoint.ordered ordered
  subst sameRank
  have decoded := residual.decode
  generalize residual.lift (ProtocolState.entry residual.program residual.source) = point
    at decoded
  have pointDecoded : decodedPoint setup execution.application.config = some point :=
    (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have intendedPoint : ProtocolState.Intended setup.program point := by
    rcases holds point decoded with intendedHere | ⟨player, owed⟩
    · exact intendedHere
    · exact (regular point pointDecoded player owed).elim
  have acts : ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) =
      some who := (decodedPoint_actor who ready pointDecoded).trans owned
  -- The committed source action.
  have projected : projectView setup leaks who site.1 = setup.protocolObserve who (some point) := by
    rw [atSite]
    exact projectView_observe setup leaks who execution _ ordered point decoded
      (execution.recall who)
  have offeredAt := offered
  rw [projected] at offeredAt
  change ProtocolView.intendedMenu who setup.program (ProtocolState.observe who setup.program point)
    (sourceOfValue setup event outputEq value) at offeredAt
  obtain ⟨sourceAction, decodes⟩ : ∃ sourceAction,
      sourceOfValue setup event outputEq value = some sourceAction := by
    cases decodesCase : sourceOfValue setup event outputEq value with
    | none =>
        rw [decodesCase] at offeredAt
        exact (offeredAt acts).elim
    | some sourceAction => exact ⟨sourceAction, rfl⟩
  rw [decodes] at offeredAt
  -- The commitment completes at the source step of its action.
  have commitLaw := firstActivation_commitment_completionPointLaw contract timely
    (targetSequence n).strategy start startState event turnExecution never node site.1 observed
    choice selected material sends packet after ordered decoded intendedPoint decodes offeredAt.2
    (fresh := fun control => ¬ StoreEventFailed control.execution.application.config.store event)
    (fun _ notFailed => notFailed)
  have decisionSome : site.1.isSome := by
    rw [atSite]
    rfl
  have deviationRun := abs_expect_historyRun_sub_le_of_completionPointLaw setup leaks bounds
    horizon scheduler parameter utility excludedPayoff wellFormed contract timely retains
    lowerUtility upperUtility lower_le le_upper sequence scale scale_pos scale_le_one weights
    targetSequence assembled n site.1 decisionSome (PMF.pure choice) start startState ordered _
    _ commitLaw
  -- The prescribed component completes at the step of the intended effective opening.
  have prescribedLaw := firstActivation_prescribed_completionPointLaw contract timely retains
    (sequence n) (scale_pos n).le (scale_le_one n) (targetSequence n).strategy start startState
    event pendingAt never node (canonicalTransmitsAt_of_binding trace who event node) ordered
    decoded intendedPoint
    (fresh := fun control => ¬ StoreEventFailed control.execution.application.config.store event)
    (fun _ notFailed => notFailed) site.1 observed
  have baselineRun := abs_expect_historyRun_sub_le_of_completionPointLaw setup leaks bounds
    horizon scheduler parameter utility excludedPayoff wellFormed contract timely retains
    lowerUtility upperUtility lower_le le_upper sequence scale scale_pos scale_le_one weights
    targetSequence assembled n site.1 decisionSome _ start startState ordered _ _ prescribedLaw
  rw [expect_sourcePointValue_behavioralStateStep setup parameter utility excludedPayoff _ who
    readoutBounded point, ← assembled_strategy_of_unpooled setup leaks bounds horizon scheduler
      sequence scale scale_pos scale_le_one weights targetSequence assembled n site forced unkeyed,
    BehavioralPolicy.withLaw_eq_self] at baselineRun
  -- The intended gain at the replay.
  obtain ⟨replay, replayed⟩ := intendedHistory?_isSome_of_debtFree wellFormed start.trace _
    startState regular
  have projectionEq := replayProjection_eq (setup := setup) (leaks := leaks) (bounds := bounds)
    (horizon := horizon) (scheduler := scheduler) (sourceSite := projectedSite setup leaks decision)
    atSite rfl ⟨start, observed⟩ replayed
  have replayState := intendedHistory?_state start.trace replayed
  rw [startState] at replayState
  have projectionState : (replayProjection setup leaks bounds horizon scheduler
      (projectedSite setup leaks decision) site atSite rfl ⟨start, observed⟩).1.state =
      some point := by
    rw [projectionEq, replayState]
    exact pointDecoded
  have intendedGain := intendedCommit_historyGain setup parameter utility excludedPayoff
    wellFormed (sequence n) (projectedSite setup leaks decision)
    ⟨sourceOfValue setup event outputEq value, offered⟩ _ projectionState acts readoutBounded
  have intendedGainAt : setup.intendedModel.historyGain
      (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
      (intendedReadoutExclusion setup parameter utility excludedPayoff)
      (payoffComponent setup) (sequence n)
      (projectedSite setup leaks decision, ((sequence n).strategy who).commit
        (projectView setup leaks who site.1) ⟨sourceOfValue setup event outputEq value, offered⟩)
      (replayProjection setup leaks bounds horizon scheduler (projectedSite setup leaks decision)
        site atSite rfl ⟨start, observed⟩) =
      expect (ProtocolState.step setup.program point
          (fun _ => (sourceOfValue setup event outputEq value : Option (OwnAction Player L))))
          (sourcePointValue setup parameter utility excludedPayoff
            (setup.intendedOpeningProfile (sequence n).strategy) who) -
        sourcePointValue setup parameter utility excludedPayoff
          (setup.intendedOpeningProfile (sequence n).strategy) who point := intendedGain
  rw [intendedGainAt]
  change (sourceOfValue setup event outputEq value : Option (OwnAction Player L)) = _ at decodes
  simp only [decodes]
  unfold InformationModel.historyGain
  rw [Profile.update_eq_self]
  rw [Profile.update_eq_self] at baselineRun
  change expect (((onePacketN).runBehavioralFrom
      (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
        (((targetSequence n).strategy who).withLaw site.1 (PMF.pure choice))) (2 * horizon + 1)
        start).map (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler
          parameter utility excludedPayoff)) (payoffComponent setup · who) -
    expect (((onePacketN).runBehavioralFrom (targetSequence n).strategy (2 * horizon + 1)
        start).map (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler
          parameter utility excludedPayoff)) (payoffComponent setup · who) ≤ _
  have deviationBound := abs_le.mp deviationRun
  have baselineBound := abs_le.mp baselineRun
  linarith [deviationBound.2, baselineBound.1]

variable {setup leaks bounds horizon scheduler} in
omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **One packet per event.** At every history of the default runtime, a
response of the one-packet menu transmitting for an event is sent before the
recall has submitted for that event. -/
theorem onePacket_unrecorded_of_member {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (event : (graph setup).EventId) (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who))
    (submitted : (runtime setup).submittedEvent? leaks response = some event) :
    (runtime setup).eventRecorded leaks (control.execution.recall who) event = false := by
  let app := application setup leaks
  cases recorded : (runtime setup).eventRecorded leaks (control.execution.recall who) event with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨_, sent⟩ := (bounds.mem_onePacketActions (runtime setup) leaks who _ _ _).mp member
      rcases sent with silent | ⟨material, transmits, permitted⟩
      · unfold EventGraphRuntime.submittedEvent? at submitted
        rw [silent] at submitted
        cases submitted
      · have named : material.call.packet.event? (graph setup) = some event := by
          unfold EventGraphRuntime.submittedEvent? at submitted
          rw [transmits] at submitted
          exact submitted
        have recalled := (runtime setup).countRecall_history leaks trace
        rw [(runtime setup).localEnvelope_eq_of_recall leaks control.execution recalled.1
          recalled.2.1 who material, countPermits_eq_true_iff] at permitted
        obtain ⟨entry, entryMember, entrySubmitted⟩ :=
          ((runtime setup).eventRecorded_iff leaks _ event).mp recorded
        obtain ⟨entryMaterial, entryTransmits⟩ : ∃ entryMaterial,
            entry.action.transmission = some entryMaterial := by
          unfold EventGraphRuntime.submittedEvent? at entrySubmitted
          cases transmission : entry.action.transmission with
          | none => rw [transmission] at entrySubmitted; cases entrySubmitted
          | some entryMaterial => exact ⟨entryMaterial, rfl⟩
        have entryNamed : entryMaterial.call.packet.event? (graph setup) = some event := by
          unfold EventGraphRuntime.submittedEvent? at entrySubmitted
          rw [entryTransmits] at entrySubmitted
          exact entrySubmitted
        obtain ⟨message, emitted, call⟩ :=
          ((transmissionsEmitted_serviceInvariant scheduler).history (initialLaw setup) horizon
            (fun _ _ _ entry member => (List.not_mem_nil member).elim) trace) who entry
            entryMember entryMaterial entryTransmits
        have output : message ∈ app.outputs (control.execution.recall who) :=
          List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩
        have earlier := earlierOwnPacket_of_output trace who
          (app.packet (app.submit control.execution.application who material) who
            (control.execution.network.known who) material) message output
        apply permitted.2.2 message earlier
        change message.payload.call.event? (graph setup) =
          material.call.packet.event? (graph setup)
        rw [call, entryNamed, named]

open Classical in
/-- **The gain of an intended commitment at the player's turn.** Under the
hypotheses of `Vegas.onePacket_commitment_gain_le_of_regular`, at a forced site
outside the late pools, a choice committing an intended value at the player's
own turn has an intended policy at the projected site whose gain at the replay
of every history of the site whose decoded point has no player owing a failure
is, up to twice the transport error plus twelve times the scale times the payoff
range, at least the gain of the choice there. -/
theorem onePacket_intendedCommitment_gain_le (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence)
    (n : ℕ) {who : Player} (site : (onePacketN).InformationSite who)
    (choice : (onePacketN).Choice who site.1)
    (forced : ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    (unkeyed : ¬ ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
      ((onePacketN).agentAt site))
    (atTurn : CommitsAtTurn setup leaks bounds horizon scheduler who site choice)
    (intended : IntendedCommitment setup leaks bounds horizon scheduler site choice)
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1))
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view)) :
    ∃ policy : setup.intendedModel.BehavioralPolicy who,
      ∀ history : (onePacketN).InformationHistory who site.1,
        (∀ point, nativeDecodedState setup leaks history.1.state = some point →
          ∀ player, ¬ ProtocolState.OwesFailure player setup.program point) →
        (onePacketN).historyGain ((onePacketN).truncatedRunner (2 * horizon + 1))
            (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
              utility excludedPayoff) (payoffComponent setup) (targetSequence n)
            (site, ((targetSequence n).strategy who).withLaw site.1 (PMF.pure choice)) history ≤
          setup.intendedModel.historyGain
              (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
              (intendedReadoutExclusion setup parameter utility excludedPayoff)
              (payoffComponent setup) (sequence n) (projectedSite setup leaks decision, policy)
              (replayProjection setup leaks bounds horizon scheduler
                (projectedSite setup leaks decision) site atSite rfl history) +
            (2 * (((Fintype.card Player * (2 * horizon + 1) : ℕ) *
                (1 - slotRetention (scale n))) *
                (max 0 (max (excludedPayoff who) (upperUtility who)) -
                  min 0 (min (excludedPayoff who) (lowerUtility who)))) +
              12 * scale n * (max 0 (max (excludedPayoff who) (upperUtility who)) -
                min 0 (min (excludedPayoff who) (lowerUtility who)))) := by
  obtain ⟨intendedPast, intendedView, response, material, event, serial, payload, outputEq, value,
    intendedSite, selected, sends, packet, after, offered⟩ := intended
  rw [atSite] at intendedSite
  obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj intendedSite)
  subst pastEq viewEq
  obtain ⟨turnPast, turnView, turnResponse, turnEvent, turnSite, chosen, submitted, turn⟩ :=
    atTurn
  rw [atSite] at turnSite
  obtain ⟨turnPastEq, turnViewEq⟩ := Prod.mk.inj (Option.some.inj turnSite)
  subst turnPastEq turnViewEq
  rw [selected] at chosen
  cases Option.some.inj chosen
  have namedEvent : turnEvent = event := by
    unfold EventGraphRuntime.submittedEvent? at submitted
    rw [sends] at submitted
    change material.call.packet.event? (graph setup) = some turnEvent at submitted
    rw [packet] at submitted
    exact (Option.some.inj submitted).symm
  subst namedEvent
  -- The response is in the one-packet menu, so the event is pending.
  have member : response ∈ bounds.onePacketActions (runtime setup) leaks who past view := by
    have legal : choice.1 ∈ (onePacketN).menu who site.1 := choice.2
    generalize choice.1 = picked at legal selected
    subst selected
    generalize site.1 = info at legal atSite
    subst atSite
    obtain ⟨action, offeredAction, actionEq⟩ := legal
    cases Option.some.inj actionEq
    exact offeredAction
  refine ⟨((sequence n).strategy who).commit (projectView setup leaks who site.1)
    ⟨sourceOfValue setup turnEvent outputEq value, offered⟩, fun history regular => ?_⟩
  obtain ⟨_, _, nodePayload, nodeOutputEq, nodeCodeEq, node⟩ :=
    onePacket_commitment_facts bounds member sends packet
  have samePayload : nodePayload = payload := by
    have both := nodeOutputEq.symm.trans outputEq
    injection both
  subst samePayload
  have sameOutput : nodeOutputEq = outputEq := rfl
  subst sameOutput
  -- The event is pending at the site.
  obtain ⟨start, observed⟩ := history
  have observedState : (application setup leaks).observe who start.state = site.1 :=
    ((bounds.onePacketMenu (runtime setup) leaks).info (initialLaw setup) horizon scheduler who
      start.trace).symm.trans observed
  have pending : pendingEvent setup leaks who site.1 = some turnEvent := by
    rw [atSite]
    refine pendingEvent_of_spec turn ?_
    rcases startState : start.state with _ | ⟨remaining, actor, execution⟩
    · rw [startState, atSite] at observedState
      cases observedState
    rw [startState] at observedState
    have actorEq : actor = some who := by
      by_contra different
      simp only [ReactiveApplication.observe, different, ↓reduceIte] at observedState
      rw [atSite] at observedState
      cases observedState
    subst actorEq
    simp only [ReactiveApplication.observe, ↓reduceIte] at observedState
    rw [atSite] at observedState
    obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj observedState)
    subst pastEq viewEq
    have trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
        horizon scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
      startState ▸ start.trace
    exact onePacket_unrecorded_of_member ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace
      (initialLaw setup) horizon scheduler trace) who turnEvent response member submitted
  exact onePacket_commitment_gain_le_of_regular setup leaks bounds horizon scheduler parameter
    utility excludedPayoff wellFormed contract timely retains lowerUtility upperUtility lower_le
    le_upper sequence scale scale_pos scale_le_one weights targetSequence assembled n site forced
    unkeyed atSite pending (outputEq := nodeOutputEq) (codeEq := nodeCodeEq) node choice selected
    material sends packet after decision offered ⟨start, observed⟩ regular

end Vegas
