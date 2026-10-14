/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateCommitFailure
import Vegas.Game.OnePacketLateCommitValue
import Vegas.Game.OnePacketCommitmentGain
import Vegas.Game.OnePacketSureCompletion
import GameTheoryExtensions.Math.Probability.ProductDecorrelation

/-! # Value-blind late commitments at a site

At a debt-free late delivery of a binding, a choice committing an intended value
at a prepared slot has, from every forced history, completion value exactly one
less its failure probability times the value of committing that source choice
(`Vegas.certificate_lateCommit_historyValue`). Its failure is, from every forced
history, near the certificate's lumped failure of the slot, a function of the
history's operational record, and the value of committing is a function of the
decoded point; so when the belief decorrelates the record and the decoded point,
the site's completion value is one less the site's failure probability times the
site's value of committing, up to errors that vanish with the scale, the belief
mass outside the forced region and the decorrelation
(`Vegas.certificate_lateCommit_siteValue`).
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
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- The newest entry of an operational record is the operational state of the
history's state. -/
theorem operationalRecord_headD {state : (application setup leaks).ProtocolState}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state) :
    (operationalRecord setup leaks bounds horizon scheduler trace).headD
        (operationalState setup leaks none) = operationalState setup leaks state :=
  match trace with
  | .start => rfl
  | .extend _ _ _ _ => rfl

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- Every history of a decision site of `who` with a pending event is a prefix of
the site's rank. -/
theorem ordered_of_site {who : Player} {site : (onePacketN).InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (history : (onePacketN).InformationHistory who site.1) :
    ∃ remaining execution, history.1.state = some ⟨remaining, some who, execution⟩ ∧
      execution.recall who = past ∧ execution.observe (application setup leaks) who = view ∧
      execution.application.config.cut.IsPrefix (siteRank site.1) := by
  obtain ⟨remaining, execution, current, recallEq, observeEq⟩ :=
    state_of_site setup leaks bounds horizon scheduler atSite history
  refine ⟨remaining, execution, current, recallEq, observeEq, ?_⟩
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      (current ▸ history.1.trace)
  obtain ⟨found, foundOrdered, _⟩ := pendingAt_history rawTrace
  have rankEq : siteRank site.1 = found := by
    rw [atSite, ← observeEq]
    change (execution.application.config.history.map EventGraph.Completion.event).length = found
    rw [List.length_map]
    exact history_length_of_isPrefix _ foundOrdered
  exact rankEq ▸ foundOrdered

/-- **The completion value of an intended late commitment.** At a debt-free
late delivery of the binding `event` of `who`, from a forced history of the
site, a choice committing, at a prepared slot, a value whose source choice is
intended at the site has completion value exactly one less its failure
probability times the value of committing that source choice. -/
theorem certificate_lateCommit_historyValue
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (wellFormed : setup.WellFormed)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (assessment : (onePacketN).BehavioralAssessment) (profile : BehavioralProfile setup.program)
    {who : Player} (site : (onePacketN).InformationSite who)
    (late : LateDelivery setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (choice : (onePacketN).Choice who site.1) (response : (application setup leaks).Action)
    (selected : choice.1 = some response) {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    {value : L.Val payload}
    (after : material.call.candidateAfter who view.application.candidates (.prepared serial) =
      .openable ⟨payload, value⟩)
    (offered : sourceOfValue setup event outputEq value ∈
      setup.intendedMenu who (projectView setup leaks who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    (forced : ForcedState setup leaks who history.1.state)
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound) :
    historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site (PMF.pure choice) history.1 =
      (1 - siteHistoryFailure setup leaks bounds horizon scheduler assessment site
          (PMF.pure choice) history) *
        decodedCommitValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          profile who (siteRank site.1) (sourceOfValue setup event outputEq value) history.1 := by
  obtain ⟨chosen, chosenEq, member⟩ := choice_response setup leaks bounds horizon scheduler site
    atSite choice
  rw [selected] at chosenEq
  cases Option.some.inj chosenEq
  obtain ⟨remaining, execution, current, recallEq, observeEq, ordered⟩ :=
    ordered_of_site setup leaks bounds horizon scheduler atSite history
  subst recallEq
  subst observeEq
  let menu := bounds.onePacketMenu (runtime setup) leaks
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.1.trace
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    menu.toRawTrace (initialLaw setup) horizon scheduler trace
  have pendingAt := pending
  rw [atSite] at pendingAt
  obtain ⟨turn, readyView, owned, unrecorded⟩ := pendingEvent_spec pendingAt
  have turnExecution : execution.application.publicView.ownTurn? who = some event := turn
  have ready := (execution.application.publicView_eventReady event).mp readyView
  have siteKeyHere := siteKey
  rw [atSite] at siteKeyHere
  obtain ⟨_, _, _, decided⟩ := lateKey_decides_binding setup leaks horizon scheduler rawTrace rfl
    siteKeyHere turn unrecorded node
  -- The decoded point is intended and reached by the intended game.
  obtain ⟨decodedRank, ⟨residual⟩, holds⟩ := decodedState_intended_or_owes wellFormed
    (failureProfile setup.program) menu horizon scheduler trace _ rfl
  have sameRank := isPrefix_unique residual.checkpoint.ordered ordered
  subst sameRank
  have decoded := residual.decode
  generalize residual.lift (ProtocolState.entry residual.program residual.source) = point
    at decoded
  have pointDecoded : decodedPoint setup execution.application.config = some point :=
    (decodedPoint_eq_of_isPrefix ordered).trans decoded
  rw [current] at forced
  obtain ⟨forcedFound, forcedDecoded, forcedHolds⟩ := (forcedState_iff_decodedPoint _).mp forced
  rw [pointDecoded, Option.some.injEq] at forcedDecoded
  subst forcedDecoded
  have free : ∀ found, decodedPoint setup execution.application.config = some found →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program found := by
    intro found foundDecoded player
    rw [pointDecoded, Option.some.injEq] at foundDecoded
    subst foundDecoded
    by_cases same : player = who
    · subst same
      exact debtFree history point (by rw [current]; exact pointDecoded)
    · exact (forcedHolds.2 player same).2
  have intendedPoint : ProtocolState.Intended setup.program point := by
    rcases holds point decoded with intendedHere | ⟨player, owed⟩
    · exact intendedHere
    · exact (free point pointDecoded player owed).elim
  obtain ⟨replay, replayed⟩ := intendedHistory?_isSome_of_debtFree wellFormed trace _ rfl free
  have replayState : replay.state = some point :=
    (intendedHistory?_state trace replayed).trans pointDecoded
  have reachedPoint : IntendedReached setup point := ⟨replay, replayState⟩
  -- Every step of the committed source choice is intended.
  have acts : ∀ player, ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some who := fun player =>
    (decodedPoint_actor player ready pointDecoded).trans owned
  have projected : projectView setup leaks who site.1 =
      setup.protocolObserve who (some point) := by
    rw [atSite]
    exact projectView_observe setup leaks who execution _ ordered point decoded
      (execution.recall who)
  have offeredAt := offered
  rw [projected] at offeredAt
  change ProtocolView.intendedMenu who setup.program
    (ProtocolState.observe who setup.program point)
    (sourceOfValue setup event outputEq value) at offeredAt
  have targetIntended : ∀ target ∈ (ProtocolState.step setup.program point
      (fun _ => sourceOfValue setup event outputEq value)).support,
      ProtocolState.Intended setup.program target := by
    intro target reached
    refine ProtocolState.intended_step_of_actors setup.program point _ target
      intendedPoint (fun player active => ?_) reached
    cases (acts player).symm.trans active
    cases sourceCase : sourceOfValue setup event outputEq value with
    | none =>
        rw [sourceCase] at offeredAt
        exact (offeredAt (acts who)).elim
    | some sourceAction =>
        rw [sourceCase] at offeredAt
        exact ⟨sourceAction, rfl, offeredAt.2⟩
  exact lateCommit_historyNear parameter utility excludedPayoff completes assessment profile site
    late siteKey decided pending choice response selected history current atSite member material
    sends packet turnExecution ordered outputEq codeEq after decoded reachedPoint targetIntended
    readoutBounded

open Classical in
/-- **Value-blind late commitments at a site.** At a debt-free late delivery of
the binding `event` of `who`, let a choice commit the event at a prepared slot
to a value its candidate opens to, whose source choice is intended at the site.
Let `unforced` bound the belief mass outside the forced region, and let the
belief decorrelate the histories' operational records and decoded points up to
`γ`. Then the site's completion value of the choice is one less its failure
probability times the site's value of committing that source choice, up to twice
the payoff bound times the unforced mass, the failure error to the lumped
failure of the slot and the decorrelation. -/
theorem certificate_lateCommit_siteValue
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount) {who : Player}
    (site : (onePacketN).InformationSite who) (late : LateDelivery setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {unforced γ : ℝ}
    (unforcedMass : expect ((targetSequence n).belief who site) (fun history =>
      if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤ unforced)
    (decorrelated : BeliefDecorrelated ((targetSequence n).belief who site)
      (fun history => operationalRecord setup leaks bounds horizon scheduler history.1.trace)
      (fun history => nativeDecodedState setup leaks history.1.state) γ)
    (choice : (onePacketN).Choice who site.1) (response : (application setup leaks).Action)
    (selected : choice.1 = some response) {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    {value : L.Val payload}
    (after : material.call.candidateAfter who view.application.candidates (.prepared serial) =
      .openable ⟨payload, value⟩)
    (offered : sourceOfValue setup event outputEq value ∈
      setup.intendedMenu who (projectView setup leaks who site.1))
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound) :
    |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
        (PMF.pure choice) -
      (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
          (PMF.pure choice)) *
        siteCommitValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
          (sourceOfValue setup event outputEq value)| ≤
      2 * bound * unforced +
        (2 * bound * ((2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3) + unforced) +
          2 * bound * γ) := by
  let belief := (targetSequence n).belief who site
  let profile := setup.intendedOpeningProfile (sequence n).strategy
  let error : ℝ := (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)
  let lumping := certificateLumping setup leaks bounds horizon scheduler sequence scale
    scale_pos scale_le_one covers capacity slotsLe weights targetSequence assembled n who
  let failure := fun history : (onePacketN).InformationHistory who site.1 =>
    siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site
      (PMF.pure choice) history
  let commitValue := fun history : (onePacketN).InformationHistory who site.1 =>
    decodedCommitValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
      profile who (siteRank site.1) (sourceOfValue setup event outputEq value) history.1
  let lumped := fun record : List (Option (OperationalState setup leaks)) =>
    expect ((fun law => law.bind (lumping.kernel key (none : LateOption slots)))^[2 * horizon + 1]
      (PMF.pure (Sum.inr (committedImage event who (who, .prepared serial)
        (record.headD (operationalState setup leaks none))))))
      (lumping.failure key)
  let valueOf : setup.ProtocolState → ℝ := fun found =>
    match found with
    | none => excludedPayoff who
    | some point =>
        if IntendedReached setup point then
          expect (ProtocolState.step setup.program point
              fun _ => sourceOfValue setup event outputEq value)
            (sourcePointValue setup parameter utility excludedPayoff profile who)
        else excludedPayoff who
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans excludedBounded
  have errorNonneg : 0 ≤ error :=
    mul_nonneg (Nat.cast_nonneg _) (by have := pow_nonneg (scale_pos n).le 3; linarith)
  have failureUnit : ∀ history, 0 ≤ failure history ∧ failure history ≤ 1 := by
    intro history
    simp only [failure]
    unfold siteHistoryFailure
    exact ⟨expect_nonneg _ _ fun final _ => by split <;> norm_num,
      expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1 fun final _ => by
        split <;> norm_num⟩
  have lumpedUnit : ∀ record, 0 ≤ lumped record ∧ lumped record ≤ 1 := by
    intro record
    exact ⟨expect_nonneg _ _ fun image _ => (lumping.failure_unit key image).1,
      expect_le_const _ _ (payoffIntegrable_of_bounded _ _ (C := 1) fun image => by
          have := lumping.failure_unit key image
          rw [abs_le]
          constructor <;> linarith) 1
        fun image _ => (lumping.failure_unit key image).2⟩
  have lumpedEq : ∀ history : (onePacketN).InformationHistory who site.1,
      lumped (operationalRecord setup leaks bounds horizon scheduler history.1.trace) =
        certificateCommitFailure setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one covers capacity slotsLe weights targetSequence assembled n who key event
          serial history.1.state := by
    intro history
    simp only [lumped, operationalRecord_headD]
    rfl
  have pointBound : ∀ point, |sourcePointValue setup parameter utility excludedPayoff profile
      who point| ≤ bound := fun point => expect_abs_le_of_bounded boundNonneg readoutBounded
  have valueBounded : ∀ found, |valueOf found| ≤ bound := by
    intro found
    rcases found with _ | point
    · exact excludedBounded
    · simp only [valueOf]
      split
      · exact expect_abs_le_of_bounded boundNonneg pointBound
      · exact excludedBounded
  have valueEq : ∀ history : (onePacketN).InformationHistory who site.1,
      commitValue history = valueOf (nativeDecodedState setup leaks history.1.state) := by
    intro history
    obtain ⟨remaining, execution, current, _, _, ordered⟩ :=
      ordered_of_site setup leaks bounds horizon scheduler atSite history
    simp only [commitValue]
    unfold decodedCommitValue
    rw [current]
    change _ = valueOf (decodedPoint setup execution.application.config)
    rw [decodedPoint_eq_of_isPrefix ordered]
    rfl
  -- From every forced history the failure is near the lumped failure of the record.
  have near : expect belief (fun history => |failure history -
      lumped (operationalRecord setup leaks bounds horizon scheduler history.1.trace)|) ≤
      error + unforced := by
    have pointwise : ∀ history ∈ belief.support,
        |failure history - lumped (operationalRecord setup leaks bounds horizon scheduler
          history.1.trace)| ≤
          error + if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1 := by
      intro history _
      by_cases forced : ForcedState setup leaks who history.1.state
      · simp only [forced, ↓reduceIte, add_zero]
        rw [lumpedEq]
        exact certificate_lateCommit_historyFailure setup leaks bounds horizon scheduler
          sequence scale scale_pos scale_le_one weights targetSequence assembled n completes
          covers capacity slotsLe site late debtFree siteKey pending node atSite choice response
          selected sends packet after history forced
      · simp only [forced, ↓reduceIte]
        have := failureUnit history
        have := lumpedUnit (operationalRecord setup leaks bounds horizon scheduler
          history.1.trace)
        rw [abs_le]
        constructor <;> linarith
    calc _ ≤ expect belief (fun history =>
          error + if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) :=
          expect_mono pointwise (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
      _ = error + expect belief (fun history =>
          if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) := by
          rw [expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
            expect_constant]
      _ ≤ error + unforced := by linarith
  have decorrelation := abs_expect_mul_sub_le_of_decorrelated belief
    (fun history => operationalRecord setup leaks bounds horizon scheduler history.1.trace)
    (fun history => nativeDecodedState setup leaks history.1.state) decorrelated failure
    commitValue lumped valueOf
    (fun history => by
      have := failureUnit history
      rw [abs_le]
      constructor <;> linarith)
    (fun record => by
      have := lumpedUnit record
      rw [abs_le]
      constructor <;> linarith)
    valueBounded valueEq near
  -- From every forced history the completion value is exact.
  have historyNear : ∀ history ∈ belief.support,
      |historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          (targetSequence n) profile site (PMF.pure choice) history.1 -
        (1 - failure history) * commitValue history| ≤
        2 * bound * if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1 := by
    intro history _
    by_cases forced : ForcedState setup leaks who history.1.state
    · simp only [forced, ↓reduceIte, mul_zero]
      rw [certificate_lateCommit_historyValue setup leaks bounds horizon
        scheduler parameter utility excludedPayoff wellFormed completes (targetSequence n)
        profile site late debtFree siteKey pending node atSite choice response selected sends
        packet after offered history forced readoutBounded, sub_self, abs_zero]
    · simp only [forced, ↓reduceIte, mul_one]
      have stopBound := abs_historyStopValue_le setup leaks bounds horizon scheduler parameter
        utility excludedPayoff (targetSequence n) profile site (PMF.pure choice) history.1
        readoutBounded excludedBounded
      have valueAt : |commitValue history| ≤ bound := by
        rw [valueEq]
        exact valueBounded _
      have unit := failureUnit history
      have productBound : |(1 - failure history) * commitValue history| ≤ bound := by
        rw [abs_mul]
        calc _ ≤ 1 * bound := mul_le_mul (by rw [abs_le]; constructor <;> linarith) valueAt
              (abs_nonneg _) zero_le_one
          _ = bound := one_mul _
      calc _ ≤ |historyStopValue setup leaks bounds horizon scheduler parameter utility
            excludedPayoff (targetSequence n) profile site (PMF.pure choice) history.1| +
            |(1 - failure history) * commitValue history| := abs_sub _ _
        _ ≤ 2 * bound := by linarith
  have stopNear := abs_expect_sub_le_expect belief
    (fun history => historyStopValue setup leaks bounds horizon scheduler parameter utility
      excludedPayoff (targetSequence n) profile site (PMF.pure choice) history.1)
    (fun history => (1 - failure history) * commitValue history) _ historyNear
  rw [expect_const_mul] at stopNear
  have failureEq : onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
      site (PMF.pure choice) = expect belief failure := by
    unfold onePacketSiteFailure localFailure
    rw [expect_localRun]
    rfl
  rw [failureEq]
  unfold siteStopValue siteCommitValue
  change |expect belief (fun history => historyStopValue setup leaks bounds horizon scheduler
      parameter utility excludedPayoff (targetSequence n) profile site (PMF.pure choice)
      history.1) - (1 - expect belief failure) * expect belief commitValue| ≤ _
  have unforcedBound : 2 * bound * expect belief (fun history =>
      if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤ 2 * bound * unforced :=
    mul_le_mul_of_nonneg_left unforcedMass (by linarith)
  calc _ ≤ |expect belief (fun history => historyStopValue setup leaks bounds horizon scheduler
          parameter utility excludedPayoff (targetSequence n) profile site (PMF.pure choice)
          history.1) - expect belief (fun history => (1 - failure history) * commitValue history)| +
        |expect belief (fun history => (1 - failure history) * commitValue history) -
          (1 - expect belief failure) * expect belief commitValue| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (stopNear.trans unforcedBound) decorrelation

end Vegas
