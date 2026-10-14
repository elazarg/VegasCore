/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateCommitBlind

/-! # Value-blind completion at late deliveries

From a history of a site, the failure probability of a law installed at the site
is the law's average of the failure probabilities of its choices
(`Vegas.siteHistoryFailure_eq_expect`).

At a site, when from every forced history of the belief the completion value of a
law is one less its failure probability times the continuation value up to `A`,
and its failure probability is near a function of the operational record, and the
belief decorrelates the records and the decoded points, the site's completion
value is one less the site's failure probability times the site's continuation
value, up to `A`, the belief mass outside the forced region and the
decorrelation (`Vegas.abs_siteStopValue_sub_le_of_forced`).

For the certificate, at a debt-free late delivery, from every forced history
the profile installing a late option or silence has completion value near one
less its failure probability times the continuation value: at a late binding by
value-free success, at a late reveal exactly
(`Vegas.certificate_late_historyNear`). Each late option fails near the
certificate's lumped failure of its record, and silence fails within one less
the slot retention of waiting (`Vegas.abs_expect_sub_apply_le`). So with
vanishing scale, unforced mass and decorrelation, the compared choices and the
late options are value-blind at late deliveries with a vanishing error
(`Vegas.lateValueBlind_of_bounds`).
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

/-- **Failure is affine in the installed law.** From a history of a decision
site, the failure probability of a law installed at the site is the law's
average of the failure probabilities of its choices. -/
theorem siteHistoryFailure_eq_expect (assessment : (onePacketN).BehavioralAssessment)
    {who : Player} (site : (onePacketN).InformationSite who)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1) :
    siteHistoryFailure setup leaks bounds horizon scheduler assessment site law history =
      expect law fun choice => siteHistoryFailure setup leaks bounds horizon scheduler
        assessment site (PMF.pure choice) history := by
  classical
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketN
  have actsOnce := (menu.decisionRecall (initialLaw setup) horizon
    scheduler).actsOnceWhereItMatters
  obtain ⟨remaining, execution, current, _, _⟩ :=
    state_of_site setup leaks bounds horizon scheduler atSite history
  have running : ¬ (menu.protocol (initialLaw setup) horizon scheduler).terminal
      history.1.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have active := InformationModel.InformationSite.active (M := model) site history
  have split : ∀ law : PMF ((onePacketN).Choice who site.1),
      model.runBehavioralFrom (Profile.update (sig := model.behavioralSignature)
          (assessment.strategy) who ((assessment.strategy who).withLaw site.1 law))
          (2 * horizon + 1) history.1 =
        law.bind fun choice => model.runBehavioralFrom (Profile.update
          (sig := model.behavioralSignature) (assessment.strategy) who
          ((assessment.strategy who).commit site.1 choice)) (2 * horizon + 1) history.1 :=
    fun law => model.runBehavioralFrom_update_withLaw_eq_bind actsOnce assessment.strategy who
      (assessment.strategy who) site.1 law history.1 history.2 running active (2 * horizon)
  unfold siteHistoryFailure localHistoryRun
  change expect (model.runBehavioralFrom _ (2 * horizon + 1) history.1) _ =
    expect law fun choice => expect (model.runBehavioralFrom _ (2 * horizon + 1) history.1) _
  rw [split law, expect_bind_tower_bounded _ _ _ (C := 1) fun final => by split <;> norm_num]
  refine expect_congr_on_support fun choice _ => ?_
  rw [split (PMF.pure choice), PMF.pure_bind]

open Classical in
/-- **Value-blind completion at a site from its forced histories.** Suppose,
from every forced history of a site's belief, the completion value of a law is
one less its failure probability times the history's continuation value up to
`A`, and its failure probability is within `E` of a function of the history's
operational record bounded by one. Let `unforced` bound the belief mass outside
the forced region and let the belief decorrelate the records and the decoded
points up to `γ`. Then the site's completion value is one less the site's failure
probability times the site's continuation value, up to `A` and twice the payoff
bound times the unforced mass, `E` plus the unforced mass, and `γ`. -/
theorem abs_siteStopValue_sub_le_of_forced
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (assessment : (onePacketN).BehavioralAssessment) (profile : BehavioralProfile setup.program)
    {who : Player} (site : (onePacketN).InformationSite who)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (law : PMF ((onePacketN).Choice who site.1))
    (lumped : List (Option (OperationalState setup leaks)) → ℝ)
    (lumpedUnit : ∀ record, 0 ≤ lumped record ∧ lumped record ≤ 1)
    {A E unforced γ bound : ℝ} (A_nonneg : 0 ≤ A) (E_nonneg : 0 ≤ E)
    (historyNear : ∀ history ∈ (assessment.belief who site).support,
      ForcedState setup leaks who history.1.state →
      |historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment profile site law history.1 -
        (1 - siteHistoryFailure setup leaks bounds horizon scheduler assessment site law
          history) *
          decodedPointValue setup leaks bounds horizon scheduler parameter utility
            excludedPayoff profile who (siteRank site.1) history.1| ≤ A)
    (failureNear : ∀ history ∈ (assessment.belief who site).support,
      ForcedState setup leaks who history.1.state →
      |siteHistoryFailure setup leaks bounds horizon scheduler assessment site law history -
        lumped (operationalRecord setup leaks bounds horizon scheduler history.1.trace)| ≤ E)
    (unforcedMass : expect (assessment.belief who site) (fun history =>
      if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤ unforced)
    (decorrelated : BeliefDecorrelated (assessment.belief who site)
      (fun history => operationalRecord setup leaks bounds horizon scheduler history.1.trace)
      (fun history => nativeDecodedState setup leaks history.1.state) γ)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound) :
    |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site law -
      (1 - onePacketSiteFailure setup leaks bounds horizon scheduler assessment site law) *
        siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment profile site| ≤
      A + 2 * bound * unforced + (2 * bound * (E + unforced) + 2 * bound * γ) := by
  let belief := assessment.belief who site
  let failure := fun history : (onePacketN).InformationHistory who site.1 =>
    siteHistoryFailure setup leaks bounds horizon scheduler assessment site law history
  let pointValue := fun history : (onePacketN).InformationHistory who site.1 =>
    decodedPointValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
      profile who (siteRank site.1) history.1
  let valueOf : setup.ProtocolState → ℝ := fun found =>
    match found with
    | none => excludedPayoff who
    | some point =>
        if IntendedReached setup point then
          sourcePointValue setup parameter utility excludedPayoff profile who point
        else excludedPayoff who
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans excludedBounded
  have failureUnit : ∀ history, 0 ≤ failure history ∧ failure history ≤ 1 := by
    intro history
    simp only [failure]
    unfold siteHistoryFailure
    exact ⟨expect_nonneg _ _ fun final _ => by split <;> norm_num,
      expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1 fun final _ => by
        split <;> norm_num⟩
  have valueBounded : ∀ found, |valueOf found| ≤ bound := by
    intro found
    rcases found with _ | point
    · exact excludedBounded
    · simp only [valueOf]
      split
      · exact expect_abs_le_of_bounded boundNonneg readoutBounded
      · exact excludedBounded
  have valueEq : ∀ history : (onePacketN).InformationHistory who site.1,
      pointValue history = valueOf (nativeDecodedState setup leaks history.1.state) := by
    intro history
    obtain ⟨remaining, execution, current, _, _, ordered⟩ :=
      ordered_of_site setup leaks bounds horizon scheduler atSite history
    simp only [pointValue]
    unfold decodedPointValue
    rw [current]
    change _ = valueOf (decodedPoint setup execution.application.config)
    rw [decodedPoint_eq_of_isPrefix ordered]
    rfl
  have near : expect belief (fun history => |failure history -
      lumped (operationalRecord setup leaks bounds horizon scheduler history.1.trace)|) ≤
      E + unforced := by
    have pointwise : ∀ history ∈ belief.support,
        |failure history - lumped (operationalRecord setup leaks bounds horizon scheduler
          history.1.trace)| ≤
          E + if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1 := by
      intro history member
      by_cases forced : ForcedState setup leaks who history.1.state
      · simp only [forced, ↓reduceIte, add_zero]
        exact failureNear history member forced
      · simp only [forced, ↓reduceIte]
        have := failureUnit history
        have := lumpedUnit (operationalRecord setup leaks bounds horizon scheduler
          history.1.trace)
        rw [abs_le]
        constructor <;> linarith
    calc _ ≤ expect belief (fun history =>
          E + if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) :=
          expect_mono pointwise (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
      _ = E + expect belief (fun history =>
          if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) := by
          rw [expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
            expect_constant]
      _ ≤ E + unforced := by linarith
  have decorrelation := abs_expect_mul_sub_le_of_decorrelated belief
    (fun history => operationalRecord setup leaks bounds horizon scheduler history.1.trace)
    (fun history => nativeDecodedState setup leaks history.1.state) decorrelated failure
    pointValue lumped valueOf
    (fun history => by
      have := failureUnit history
      rw [abs_le]
      constructor <;> linarith)
    (fun record => by
      have := lumpedUnit record
      rw [abs_le]
      constructor <;> linarith)
    valueBounded valueEq near
  have historyBound : ∀ history ∈ belief.support,
      |historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment profile site law history.1 - (1 - failure history) * pointValue history| ≤
        A + 2 * bound * if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1 := by
    intro history member
    by_cases forced : ForcedState setup leaks who history.1.state
    · simp only [forced, ↓reduceIte, mul_zero, add_zero]
      exact historyNear history member forced
    · simp only [forced, ↓reduceIte, mul_one]
      have stopBound := abs_historyStopValue_le setup leaks bounds horizon scheduler parameter
        utility excludedPayoff assessment profile site law history.1 readoutBounded
        excludedBounded
      have valueAt : |pointValue history| ≤ bound := by
        rw [valueEq]
        exact valueBounded _
      have unit := failureUnit history
      have productBound : |(1 - failure history) * pointValue history| ≤ bound := by
        rw [abs_mul]
        calc _ ≤ 1 * bound := mul_le_mul (by rw [abs_le]; constructor <;> linarith) valueAt
              (abs_nonneg _) zero_le_one
          _ = bound := one_mul _
      calc _ ≤ |historyStopValue setup leaks bounds horizon scheduler parameter utility
            excludedPayoff assessment profile site law history.1| +
            |(1 - failure history) * pointValue history| := abs_sub _ _
        _ ≤ A + 2 * bound := by linarith
  have stopNear := abs_expect_sub_le_expect belief
    (fun history => historyStopValue setup leaks bounds horizon scheduler parameter utility
      excludedPayoff assessment profile site law history.1)
    (fun history => (1 - failure history) * pointValue history) _ historyBound
  rw [expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    expect_constant, expect_const_mul] at stopNear
  have failureEq : onePacketSiteFailure setup leaks bounds horizon scheduler assessment site
      law = expect belief failure := by
    unfold onePacketSiteFailure localFailure
    rw [expect_localRun]
    rfl
  rw [failureEq]
  unfold siteStopValue siteValue
  change |expect belief (fun history => historyStopValue setup leaks bounds horizon scheduler
      parameter utility excludedPayoff assessment profile site law history.1) -
    (1 - expect belief failure) * expect belief pointValue| ≤ _
  have unforcedBound : 2 * bound * expect belief (fun history =>
      if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤
      2 * bound * unforced :=
    mul_le_mul_of_nonneg_left unforcedMass (by linarith)
  calc _ ≤ |expect belief (fun history => historyStopValue setup leaks bounds horizon scheduler
          parameter utility excludedPayoff assessment profile site law history.1) -
          expect belief (fun history => (1 - failure history) * pointValue history)| +
        |expect belief (fun history => (1 - failure history) * pointValue history) -
          (1 - expect belief failure) * expect belief pointValue| := abs_sub_le _ _ _
    _ ≤ _ := by linarith

/-- **The certificate's completion value at a late delivery.** At a debt-free
late delivery of `who` for its pending event, from a forced history of the site,
the profile installing a late option or silence at the site has completion value
within a multiple of the cube of the scale, times the payoff bound, of one less
its failure probability times the history's continuation value: a late binding
by the certificate's value-free success, a late reveal exactly. -/
theorem certificate_late_historyNear
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
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (law : PMF ((onePacketN).Choice who site.1))
    (lawShape : (∃ option : LateOption slots, law = onePacketLate setup leaks bounds horizon
        scheduler sequence scale scale_pos scale_le_one n ((onePacketN).agentAt site) option) ∨
      law = PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        site.1))
    (history : (onePacketN).InformationHistory who site.1)
    (forced : ForcedState setup leaks who history.1.state)
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound) :
    |historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site law
        history.1 -
      (1 - siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site law
          history) *
        decodedPointValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          (setup.intendedOpeningProfile (sequence n).strategy) who (siteRank site.1) history.1| ≤
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
          (2 * horizon + 1) + 2 * (scale n ^ 3 * (2 * horizon + 1))) * bound := by
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans excludedBounded
  have errorNonneg : 0 ≤ (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 +
      scale n ^ 3)) * (2 * horizon + 1) + 2 * (scale n ^ 3 * (2 * horizon + 1))) * bound := by
    have := pow_nonneg (scale_pos n).le 3
    positivity
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
  obtain ⟨turn, readyView, owned, _⟩ := pendingEvent_spec pendingAt
  have turnExecution : execution.application.publicView.ownTurn? who = some event := turn
  have ready := (execution.application.publicView_eventReady event).mp readyView
  have siteKeyHere := siteKey
  rw [atSite] at siteKeyHere
  have decided := decidedEvent_eq_of_pending setup leaks horizon scheduler pendingAt rawTrace rfl
    siteKeyHere
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
  have forcedHere := forced
  rw [current] at forcedHere
  obtain ⟨forcedFound, forcedDecoded, forcedHolds⟩ :=
    (forcedState_iff_decodedPoint _).mp forcedHere
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
  have reachedPoint : IntendedReached setup point :=
    ⟨replay, (intendedHistory?_state trace replayed).trans pointDecoded⟩
  -- A late binding, by value-free success; a late reveal, exactly.
  cases view : nodeView (graph setup) event with
  | bind owner payload outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst ownerEq
      exact certificate_lateBinding_historyNear setup leaks bounds horizon scheduler parameter
        utility excludedPayoff sequence scale scale_pos scale_le_one weights targetSequence
        assembled n completes covers capacity slotsLe site late siteKey pending law lawShape
        history current atSite forced view ordered decoded intendedPoint reachedPoint
        readoutBounded
  | resolve owner payload binding checks outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst ownerEq
      rw [lateReveal_historyNear parameter utility excludedPayoff completes (sequence n)
        (targetSequence n) site decided pending law history current turnExecution ordered
        outputEq codeEq decoded intendedPoint reachedPoint readoutBounded, sub_self, abs_zero]
      exact errorNonneg
  | sample payload distribution outputEq codeEq =>
      rw [nodeView_sample_actor outputEq codeEq] at owned
      cases owned

omit [Fintype Player] in
/-- A law's average of a function with values in the unit interval is within
one less the mass of a point of the function's value at the point. -/
theorem abs_expect_sub_apply_le {α : Type*} [Finite α] (law : PMF α) (value : α → ℝ)
    (unit : ∀ point, 0 ≤ value point ∧ value point ≤ 1) (point : α) :
    |expect law value - value point| ≤ 1 - (law point).toReal := by
  classical
  let := Fintype.ofFinite α
  have total : ∑ other, (law other).toReal = 1 := by
    have sum := expect_eq_sum law (fun _ => (1 : ℝ))
    rw [expect_constant] at sum
    simpa using sum.symm
  have split : expect law value - value point =
      ∑ other, (law other).toReal * (value other - value point) := by
    rw [expect_eq_sum]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, total, one_mul]
  rw [split]
  calc _ ≤ ∑ other, |(law other).toReal * (value other - value point)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ other, (if other = point then 0 else (law other).toReal) := by
        refine Finset.sum_le_sum fun other _ => ?_
        by_cases same : other = point
        · subst same
          simp
        · simp only [same, ↓reduceIte]
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          have := unit other
          have := unit point
          have difference : |value other - value point| ≤ 1 := by
            rw [abs_le]
            constructor <;> linarith
          calc _ ≤ (law other).toReal * 1 :=
                mul_le_mul_of_nonneg_left difference ENNReal.toReal_nonneg
            _ = _ := mul_one _
    _ = 1 - (law point).toReal := by
        have pieces : ∀ other, (law other).toReal =
            (if other = point then (law other).toReal else 0) +
              (if other = point then 0 else (law other).toReal) := fun other => by
          split <;> simp
        rw [← total, Finset.sum_congr rfl fun other _ => pieces other, Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        ring

open Classical Filter in
/-- **Value blindness at late deliveries.** Along an assembled sequence of
vanishing scale, let a vanishing drift bound the belief mass outside the forced
region and let the beliefs decorrelate the operational records and the decoded
points up to a vanishing error, at every late delivery of an agent that is
neither free nor owing. With bounded payoffs, the compared choices and every late
option have completion value one less their failure probability times the site's
continuation value, up to a vanishing error. -/
theorem lateValueBlind_of_bounds
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (scale_vanishing : Tendsto scale atTop (nhds 0))
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount)
    (unforcedDrift decorrelation : ℕ → ℝ)
    (unforcedLimit : Tendsto unforcedDrift atTop (nhds 0))
    (decorrelationLimit : Tendsto decorrelation atTop (nhds 0))
    (unforced : ∀ n who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site) →
      expect ((targetSequence n).belief who site) (fun history =>
        if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤ unforcedDrift n)
    (decorrelated : ∀ n who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site) →
      BeliefDecorrelated ((targetSequence n).belief who site)
        (fun history => operationalRecord setup leaks bounds horizon scheduler history.1.trace)
        (fun history => nativeDecodedState setup leaks history.1.state) (decorrelation n))
    {bound : ℝ} (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ bound) :
    ∃ blindError : ℕ → ℝ, Tendsto blindError atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        (∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
          |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
              (PMF.pure choice) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (PMF.pure choice)) *
            siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
            blindError n) ∧
        ∀ option,
          |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
              (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)) *
            siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
            blindError n := by
  let pathError := fun n => ((2 * horizon + 1 : ℕ) : ℝ) * (scale n ^ 3 + scale n ^ 3)
  let valueError := fun n => (2 * (scale n ^ 3 + pathError n) * (2 * horizon + 1) +
    2 * (scale n ^ 3 * (2 * horizon + 1))) * bound
  let silenceError := fun n => 1 - slotRetention (scale n)
  let error := fun n => valueError n + 2 * bound * |unforcedDrift n| +
    (2 * bound * (pathError n + silenceError n + |unforcedDrift n|) +
      2 * bound * |decorrelation n|)
  have cube := scale_vanishing.pow 3
  have pathLimit : Tendsto pathError atTop (nhds 0) := by
    simpa [pathError] using (cube.add cube).const_mul ((2 * horizon + 1 : ℕ) : ℝ)
  have silenceLimit : Tendsto silenceError atTop (nhds 0) := by
    have square := scale_vanishing.pow 2
    have retention : Tendsto (fun n => slotRetention (scale n)) atTop (nhds 1) := by
      unfold slotRetention
      simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub cube).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub square)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub scale_vanishing)
    simpa [silenceError] using (tendsto_const_nhds (x := (1 : ℝ))).sub retention
  refine ⟨error, ?_, ?_⟩
  · have valueLimit : Tendsto valueError atTop (nhds 0) := by
      simpa [valueError] using ((((cube.add pathLimit).const_mul 2).mul_const
        ((2 * horizon + 1 : ℕ) : ℝ)).add ((cube.mul_const ((2 * horizon + 1 : ℕ) : ℝ)).const_mul
          2)).mul_const bound
    simpa [error] using (valueLimit.add (unforcedLimit.abs.const_mul (2 * bound))).add
      ((((pathLimit.add silenceLimit).add unforcedLimit.abs).const_mul (2 * bound)).add
        (decorrelationLimit.abs.const_mul (2 * bound)))
  intro n who site notFree notOwing keyed
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans (excludedBounded who)
  have retentionLe := slotRetention_le_one (scale_pos n).le (scale_le_one n)
  have silenceNonneg : 0 ≤ silenceError n := by
    simp only [silenceError]
    linarith
  have pathNonneg : 0 ≤ pathError n :=
    mul_nonneg (Nat.cast_nonneg _) (by have := pow_nonneg (scale_pos n).le 3; linarith)
  have valueNonneg : 0 ≤ valueError n := by
    have := pow_nonneg (scale_pos n).le 3
    simp only [valueError]
    positivity
  have late : LateDelivery setup leaks who site.1 := keyed.1
  have debtFree : SiteDebtFree setup leaks bounds horizon scheduler site :=
    fun history point decoded owes => notOwing ⟨history, point, decoded, owes⟩
  obtain ⟨past, view, event, atSite, pending, _⟩ := id late
  have : Finite ((onePacketN).Choice who site.1) :=
    (onePacketN).finite_choice_of_played ((onePacketN).site_mem_playedInformation site)
  obtain ⟨key, siteKey⟩ : ∃ key, lateKey setup leaks who site.1 = some key :=
    ⟨_, by rw [atSite]; rfl⟩
  have decidedOf : ∀ history : (onePacketN).InformationHistory who site.1,
      decidedEvent key = some event := by
    intro history
    obtain ⟨remaining, execution, current, recallEq, _⟩ :=
      state_of_site setup leaks bounds horizon scheduler atSite history
    have pendingAt := pending
    rw [atSite] at pendingAt
    have siteKeyAt := siteKey
    rw [atSite] at siteKeyAt
    exact decidedEvent_eq_of_pending setup leaks horizon scheduler pendingAt
      ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
        scheduler (current ▸ history.1.trace)) recallEq siteKeyAt
  let lumping := certificateLumping setup leaks bounds horizon scheduler sequence scale
    scale_pos scale_le_one covers capacity slotsLe weights targetSequence assembled n who
  have lumpedUnit : ∀ option record, 0 ≤ lumpedFailure setup leaks bounds horizon scheduler
      lumping (2 * horizon + 1) key option record ∧ lumpedFailure setup leaks bounds horizon
        scheduler lumping (2 * horizon + 1) key option record ≤ 1 := by
    intro option record
    unfold lumpedFailure
    exact ⟨expect_nonneg _ _ fun image _ => (lumping.failure_unit key image).1,
      expect_le_const _ _ (payoffIntegrable_of_bounded _ _ (C := 1) fun image => by
          have := lumping.failure_unit key image
          rw [abs_le]
          constructor <;> linarith) 1
        fun image _ => (lumping.failure_unit key image).2⟩
  have optionNear : ∀ option : LateOption slots,
      ∀ history ∈ ((targetSequence n).belief who site).support,
      ForcedState setup leaks who history.1.state →
      |siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) history -
        lumpedFailure setup leaks bounds horizon scheduler lumping (2 * horizon + 1) key option
          (operationalRecord setup leaks bounds horizon scheduler history.1.trace)| ≤
        pathError n := by
    intro option history supported forced
    exact lateHistoryFailure_near_lumped setup leaks bounds horizon scheduler sequence scale
      scale_pos scale_le_one n (targetSequence n) who lumping site
        ⟨Or.inl late, debtFree⟩ key siteKey
      option (fun other _ _ final reached =>
        onePacketFailed_iff_decisionFailed_of_pending setup leaks bounds horizon scheduler
          completes site (decidedOf other) pending other _ final reached)
      history supported forced
  have unforcedAbs := (unforced n who site notFree notOwing keyed).trans
    (le_abs_self (unforcedDrift n))
  have decorrelatedAbs : BeliefDecorrelated ((targetSequence n).belief who site)
      (fun history => operationalRecord setup leaks bounds horizon scheduler history.1.trace)
      (fun history => nativeDecodedState setup leaks history.1.state) |decorrelation n| :=
    (decorrelated n who site notFree notOwing keyed).mono (le_abs_self _)
  constructor
  · -- The compared choice is silence; it fails like waiting.
    intro choice compared
    have silent : ∀ info, info = some (past, view) →
        (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who info).1 =
          some ⟨none⟩ := by
      intro info infoEq
      subst infoEq
      simp only [silenceChoice, responseChoice]
      split <;> rfl
    have isSilence : choice = silenceChoice setup leaks bounds (initialLaw setup) horizon
        scheduler who site.1 := by
      apply Subtype.ext
      rw [compared.1 late]
      exact (silent site.1 atSite).symm
    subst isSilence
    have silenceNear : ∀ history ∈ ((targetSequence n).belief who site).support,
        ForcedState setup leaks who history.1.state →
        |siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
              site.1)) history -
          lumpedFailure setup leaks bounds horizon scheduler lumping (2 * horizon + 1) key none
            (operationalRecord setup leaks bounds horizon scheduler history.1.trace)| ≤
          pathError n + silenceError n := by
      intro history supported forced
      have waitNear := optionNear none history supported forced
      rw [siteHistoryFailure_eq_expect setup leaks bounds horizon scheduler (targetSequence n)
        site atSite] at waitNear
      have mass : slotRetention (scale n) ≤ ((onePacketLate setup leaks bounds horizon scheduler
          sequence scale scale_pos scale_le_one (slots := slots) n ((onePacketN).agentAt site)
          none) (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
            site.1)).toReal := by
        have main := slotTrembledChoice_ge_main setup leaks bounds (initialLaw setup) horizon
          scheduler (scale_pos n).le (scale_le_one n) who site.1
          (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
            site.1 (none : LateOption slots))
          (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
            site.1))
          (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
            site.1) (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
              site.1)
        have waiting : ∀ info, info = some (past, view) →
            (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler
              (sequence n) who info (none : LateOption slots)
              (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
                info)).toReal = 1 := by
          intro info infoEq
          subst infoEq
          simp only [lateChoice, lateResponse, PMF.pure_map, silenceChoice, PMF.pure_apply_self,
            ENNReal.toReal_one]
        have mainMass := waiting site.1 atSite
        rw [mainMass, mul_one] at main
        exact main
      have spread := abs_expect_sub_apply_le (onePacketLate setup leaks bounds horizon scheduler
        sequence scale scale_pos scale_le_one (slots := slots) n ((onePacketN).agentAt site)
        none) (fun choice => siteHistoryFailure setup leaks
        bounds horizon scheduler (targetSequence n) site (PMF.pure choice) history)
        (fun choice => by
          unfold siteHistoryFailure
          exact ⟨expect_nonneg _ _ fun final _ => by split <;> norm_num,
            expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1 fun final _ => by
              split <;> norm_num⟩)
        (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who site.1)
      calc _ ≤ |siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site
              (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler
                who site.1)) history -
            expect (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n ((onePacketN).agentAt site) none) (fun choice =>
              siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site
                (PMF.pure choice) history)| +
            |expect (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n ((onePacketN).agentAt site) none) (fun choice =>
              siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site
                (PMF.pure choice) history) -
            lumpedFailure setup leaks bounds horizon scheduler lumping (2 * horizon + 1) key
              none (operationalRecord setup leaks bounds horizon scheduler history.1.trace)| :=
            abs_sub_le _ _ _
        _ ≤ silenceError n + pathError n := by
            refine add_le_add ?_ waitNear
            rw [abs_sub_comm]
            simp only [silenceError]
            linarith
        _ = _ := add_comm _ _
    have site_bound := abs_siteStopValue_sub_le_of_forced setup leaks bounds horizon scheduler
      parameter utility excludedPayoff (targetSequence n)
      (setup.intendedOpeningProfile (sequence n).strategy) site atSite _
      (lumpedFailure setup leaks bounds horizon scheduler lumping (2 * horizon + 1) key none)
      (lumpedUnit none) valueNonneg (add_nonneg pathNonneg silenceNonneg)
      (fun history _ forced => certificate_late_historyNear setup leaks bounds horizon
        scheduler parameter utility excludedPayoff wellFormed sequence scale scale_pos
        scale_le_one weights targetSequence assembled n completes covers capacity slotsLe site
        late debtFree siteKey pending atSite _ (Or.inr rfl) history forced (readoutBounded who)
        (excludedBounded who))
      silenceNear unforcedAbs decorrelatedAbs (readoutBounded who) (excludedBounded who)
    refine site_bound.trans (le_of_eq ?_)
    simp only [error]
  · intro option
    have site_bound := abs_siteStopValue_sub_le_of_forced setup leaks bounds horizon scheduler
      parameter utility excludedPayoff (targetSequence n)
      (setup.intendedOpeningProfile (sequence n).strategy) site atSite _
      (lumpedFailure setup leaks bounds horizon scheduler lumping (2 * horizon + 1) key option)
      (lumpedUnit option) valueNonneg pathNonneg
      (fun history _ forced => certificate_late_historyNear setup leaks bounds horizon
        scheduler parameter utility excludedPayoff wellFormed sequence scale scale_pos
        scale_le_one weights targetSequence assembled n completes covers capacity slotsLe site
        late debtFree siteKey pending atSite _ (Or.inl ⟨option, rfl⟩) history forced
        (readoutBounded who) (excludedBounded who))
      (optionNear option) unforcedAbs decorrelatedAbs (readoutBounded who) (excludedBounded who)
    refine site_bound.trans ?_
    simp only [error]
    have := mul_le_mul_of_nonneg_left silenceNonneg (by linarith : (0 : ℝ) ≤ 2 * bound)
    have expand : 2 * bound * (pathError n + silenceError n + |unforcedDrift n|) =
        2 * bound * (pathError n + |unforcedDrift n|) + 2 * bound * silenceError n := by ring
    linarith

end Vegas
