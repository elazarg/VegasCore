/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateSuccess
import Vegas.Game.OnePacketCertificateDischarge

/-! # The value decomposition at forced sites

**The rank of a site.** A site's information records the public completion
order, so every history of a site has completed the same number of events, the
site's rank (`Vegas.siteRank`).

**Installed laws keep as-if-honest play after the site's event.** Installing a
law at a site of an assembled profile leaves its play at every forced
information state as-if-honest play reaches from a reached boundary beyond the
site's rank: such a state has completed more events than the site, so it is not
the site, and it is not a late delivery
(`Vegas.not_lateDelivery_of_honestReachedFrom`), so its components are the
slot-trembled prescribed component (`Vegas.installed_dominates`).

**The successful part of a site.** So the successful part of every law
installed at a site of an assembled profile is within a vanishing error of its
completion value (`Vegas.abs_siteSuccess_sub_siteStopValue_le`): the belief
average of the value at the first completion of the event of the site's rank,
the source continuation value of the intended effective opening at the decoded
point when that point is intended and the site's pending event, if any, did not
fail (`Vegas.siteStopValue`).

**The decomposition.** The continuation value of an agent is the belief
average, over its site, of the source continuation value at the decoded point
of the site's rank, at points the intended game reaches
(`Vegas.siteContinuation`). It lies between the exclusion payoff and the upper
utility whenever exclusion is a punishment at every terminal readout of the
intended game (`Vegas.excludedPayoff_le_of_reached`,
`Vegas.siteContinuation_mem_Icc`). Given that the completion
value of each law the decomposition compares is its success probability times
this continuation value up to a vanishing error, the value decompositions at
late deliveries and away from them follow
(`Vegas.onePacket_lateDecomposition`, `Vegas.onePacket_nonLateDecomposition`).
That premise is value-blind success: the success probability depends neither
on the committed value nor, under the belief, on the hidden values the
continuation value depends on. It is discharged by value-blind binding
inclusion (opaque commitments) together with the fiber results of the forced
beliefs. It splits into value-free success from each history of the site and
the decorrelation of failure and continuation value under the site's belief
(`Vegas.abs_siteStopValue_sub_le_of_valueFree`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

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

variable {setup leaks} in
/-- **The rank of a site**: the number of events its public completion order
records. -/
def siteRank : (application setup leaks).Info → Nat
  | none => 0
  | some (_, view) => view.application.publicView.observation.completionOrder.length

/-- **Installed laws keep as-if-honest play after the site's event.** Under the
asynchronous contract with timely delays and retention of first covered
canonical packets, installing any law at a site of a profile assembled from
mixtures of the components of the one-packet certificate gives, from every
one-packet history ending between rounds at a reached boundary beyond the
site's rank decoding to a point of the intended game, each choice at every
forced information state as-if-honest play reaches at least the slot retention
of the scale times its as-if-honest mass. -/
theorem installed_dominates {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence)
    (n : ℕ) {owner : Player} (site : (application setup leaks).Info) (decision : site.isSome)
    (law : PMF ((onePacketN).Choice owner site))
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) (anchor : (application setup leaks).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (reached : ReachedBoundary setup leaks horizon scheduler (siteRank site + 1) anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup (siteRank site + 1) anchor.application.config =
      some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (who : Player) (info : (application setup leaks).Info)
    (reachedInfo : HonestReachedFrom setup leaks bounds horizon scheduler (sequence n) start who
      info)
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who info)
    (choice : (onePacketN).Choice who info) :
    slotRetention (scale n) * ((honestProfile setup leaks bounds (initialLaw setup) horizon
        scheduler (sequence n) who info) choice).toReal ≤
      ((Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy owner
        (((targetSequence n).strategy owner).withLaw site law) who info) choice).toReal := by
  let app := application setup leaks
  let menu := bounds.onePacketMenu (runtime setup) leaks
  have notLate := not_lateDelivery_of_honestReachedFrom bounds contract timely (sequence n)
    retains reached point decoded intendedPoint start state reachedInfo
  have occurs : ∃ history : ((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).History,
      (onePacketN).infoOf who history.trace = info := by
    obtain ⟨_, history, _, infoEq⟩ := reachedInfo
    exact ⟨history, infoEq⟩
  have base := onePacketMixture_ge_honest_of_not_late setup leaks bounds horizon scheduler
    sequence scale scale_pos scale_le_one n (weights n) notLate occurs forced choice
  -- Every state play reaches from the boundary has completed more events than the site.
  have beyond : info ≠ site := by
    intro same
    obtain ⟨fuel, history, mem, infoEq⟩ := reachedInfo
    have supported := menu.runRoundsSupported_of_mem_run (initialLaw setup) horizon scheduler
      (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler (sequence n)) fuel
      start history state mem
    have observed : app.observe who history.state = site :=
      ((menu.info (initialLaw setup) horizon scheduler who history.trace).symm.trans infoEq).trans
        same
    rcases current : history.state with _ | control
    · rw [current] at observed
      rw [← observed] at decision
      cases decision
    obtain ⟨later, grows, ordered⟩ := runRoundsSupported_isPrefix reached.ordered supported current
    rw [current] at observed
    rcases control with ⟨remaining, actor, execution⟩
    by_cases active : actor = some who
    · subst active
      simp only [ReactiveApplication.observe, ↓reduceIte] at observed
      have rankEq : siteRank site = later := by
        rw [← observed]
        change (execution.application.config.history.map EventGraph.Completion.event).length =
          later
        rw [List.length_map]
        exact history_length_of_isPrefix _ ordered
      omega
    · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
      rw [← observed] at decision
      cases decision
  have agrees : Profile.update (sig := (onePacketN).behavioralSignature)
      (targetSequence n).strategy owner (((targetSequence n).strategy owner).withLaw site law)
      who info = (targetSequence n).strategy who info := by
    by_cases same : who = owner
    · subst same
      rw [Profile.update_same]
      exact BehavioralPolicy.withLaw_of_ne _ _ _ beyond
    · rw [Profile.update_of_ne _ _ same]
  rw [agrees, assembled n]
  exact base

/-- A source point at which some history of the intended game ends. -/
def IntendedReached (point : ProtocolState setup.program) : Prop :=
  ∃ history : setup.intendedProtocol.History, history.state = some point

section Values

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- **The value at a site history.** The source continuation value of `profile`
at the point the history's configuration decodes to after `rank` events, when
that point is a point of the intended game; the exclusion payoff otherwise. -/
def decodedPointValue (profile : BehavioralProfile setup.program) (who : Player) (rank : Nat)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History) : ℝ :=
  match history.state with
  | none => excludedPayoff who
  | some control =>
      match sourceServicePrefix? setup rank control.execution.application.config with
      | none => excludedPayoff who
      | some point =>
          if IntendedReached setup point then
            sourcePointValue setup parameter utility excludedPayoff profile who point
          else excludedPayoff who

/-- **The continuation value of a site.** The belief average, over the histories
of a site, of the source continuation value of `profile` at their decoded point
of the site's rank. -/
def siteValue (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) : ℝ :=
  expect (assessment.belief who site) fun history =>
    decodedPointValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
      profile who (siteRank site.1) history.1

variable {setup leaks} in
/-- The site's pending event, if any, has not failed. -/
def siteFresh (who : Player) (info : (application setup leaks).Info)
    (control : (application setup leaks).Control) : Prop :=
  match pendingEvent setup leaks who info with
  | some event => ¬ StoreEventFailed control.execution.application.config.store event
  | none => True

open Classical in
/-- **The completion value from a history.** The expected completion value under
play from a history, with `law` installed at the site, until the event of the
site's rank completes: the source continuation value of `profile` at the
decoded point after that event, when the intended game reaches it and the
site's pending event did not fail, and the expected payoff of `who` off the
site's failure set otherwise. -/
def historyStopValue (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1))
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History) : ℝ :=
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let installed := Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy
    who ((assessment.strategy who).withLaw site.1 law)
  let payoff := fun final : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    if final ∈ onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)
    then 0 else exclusionBase setup parameter utility excludedPayoff leaks final.state who
  expect ((onePacketN).runBehavioralUntil certificate installed
      (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) history)
    (fun stop => if LateStopped setup leaks bounds horizon scheduler (siteRank site.1) stop then
      completionValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        profile (siteRank site.1) (siteFresh who site.1) who
        (fun later => expect ((onePacketN).runBehavioralTerminalFrom certificate installed later)
          payoff) stop
      else payoff stop)

/-- **The completion value of a site.** The belief average, over the histories
of a site, of their completion values (`Vegas.historyStopValue`). -/
def siteStopValue (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1)) :
    ℝ :=
  expect (assessment.belief who site) fun history =>
    historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
      assessment profile site law history.1

end Values

section Site

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- A belief average of quantities within `error` of their targets is within
`error` of the average target. -/
private theorem abs_expect_sub_le_of_near {α : Type*} [Finite α] (belief : PMF α)
    (value target : α → ℝ) {error : ℝ} (nonnegative : 0 ≤ error)
    (near : ∀ point ∈ belief.support, |value point - target point| ≤ error) :
    |expect belief value - expect belief target| ≤ error := by
  classical
  rw [← expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
  rw [expect_congr_on_support (g := fun point =>
    if point ∈ belief.support then value point - target point else 0)
    (fun point member => by rw [ite_eq_left member ..])]
  apply expect_abs_le_of_bounded nonnegative
  intro point
  split
  · rename_i member
    exact near point member
  · rw [abs_zero]
    exact nonnegative

/-- **The successful part of a site is its completion value.** For a
well-formed setup under the asynchronous contract with timely delays and
retention of first covered canonical packets, at every site of an assembled
profile, the successful part of every law installed at the site is within
`|Player| * (2 * horizon + 1) * (1 - slotRetention (scale n)) * range` of its
completion value, the source continuation values being those of the intended
effective opening of the source assessment. -/
theorem abs_siteSuccess_sub_siteStopValue_le [Finite ((bounds.onePacketMenu (runtime setup)
      leaks).protocol (initialLaw setup) horizon scheduler).History]
    (wellFormed : setup.WellFormed) {delay bound : (graph setup).EventId → Nat}
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
    (law : PMF ((onePacketN).Choice who site.1)) :
    |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility excludedPayoff
        (targetSequence n) site law -
      siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site law| ≤
      ((Fintype.card Player * (2 * horizon + 1) : ℕ) * (1 - slotRetention (scale n))) *
        (max 0 (max (excludedPayoff who) (upperUtility who)) -
          min 0 (min (excludedPayoff who) (lowerUtility who))) := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
  have bounded := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := bounded.wellFoundedHistories
  let low := min 0 (min (excludedPayoff who) (lowerUtility who))
  let range := max 0 (max (excludedPayoff who) (upperUtility who)) - low
  have boundedReadout : ∀ readout, low ≤ exclusionReadoutUtility setup parameter utility
      excludedPayoff readout who ∧
      exclusionReadoutUtility setup parameter utility excludedPayoff readout who ≤ low + range :=
    fun readout => by
      have within := exclusionReadoutUtility_mem_Icc setup parameter utility excludedPayoff
        lowerUtility upperUtility lower_le le_upper readout who
      exact ⟨within.1, by simp only [low, range]; linarith [within.2]⟩
  have zeroWithin : low ≤ 0 ∧ 0 ≤ low + range :=
    ⟨min_le_left _ _, by
      simp only [low, range]
      linarith [le_max_left 0 (max (excludedPayoff who) (upperUtility who))]⟩
  have retentionNonneg := slotRetention_nonneg (scale_pos n).le (scale_le_one n)
  have retentionLe := slotRetention_le_one (scale_pos n).le (scale_le_one n)
  have rangeNonneg : 0 ≤ range := by linarith [zeroWithin.1, zeroWithin.2]
  unfold onePacketSiteSuccess localSuccessValue siteStopValue
  rw [expect_localRun]
  unfold historyStopValue
  apply abs_expect_sub_le_of_near _ _ _
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) rangeNonneg)
  intro history _
  obtain ⟨start, observed⟩ := history
  have observedState : (application setup leaks).observe who start.state = site.1 :=
    (menu.info (initialLaw setup) horizon scheduler who start.trace).symm.trans observed
  have decision : site.1.isSome := by
    obtain ⟨_, _, action, member⟩ := site.2
    cases info : site.1 with
    | none =>
        rw [info] at member
        change some action = none at member
        cases member
    | some _ => rfl
  rcases startState : start.state with _ | ⟨remaining, actor, execution⟩
  · rw [startState] at observedState
    rw [← observedState] at decision
    cases decision
  rw [startState] at observedState
  have actorEq : actor = some who := by
    by_contra different
    simp only [ReactiveApplication.observe, different, ↓reduceIte] at observedState
    rw [← observedState] at decision
    cases decision
  subst actorEq
  simp only [ReactiveApplication.observe, ↓reduceIte] at observedState
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    startState ▸ menu.toRawTrace (initialLaw setup) horizon scheduler start.trace
  obtain ⟨rank, ordered, seen⟩ := pendingAt_history rawTrace
  have rankEq : siteRank site.1 = rank := by
    rw [← observedState]
    change (execution.application.config.history.map EventGraph.Completion.event).length = rank
    rw [List.length_map]
    exact history_length_of_isPrefix _ ordered
  have avoids : ∀ (stop : (menu.protocol (initialLaw setup) horizon scheduler).History)
      (control : (application setup leaks).Control),
      stop.state = some control →
      control.execution.application.config.cut.IsPrefix (siteRank site.1 + 1) →
      siteFresh who site.1 control →
      ∀ final ∈ (model.runBehavioralTerminalFrom certificate
        (Profile.update (sig := model.behavioralSignature) (targetSequence n).strategy who
          (((targetSequence n).strategy who).withLaw site.1 law)) stop).support,
        final ∉ onePacketFailed setup leaks bounds horizon scheduler (model.agentAt site) := by
    intro stop control stopState completed fresh final finalMember
    change final ∉ (match pendingEvent setup leaks who site.1 with
      | none => ∅
      | some event => EventFailedHistory setup leaks bounds horizon scheduler who event)
    unfold siteFresh at fresh
    cases pending : pendingEvent setup leaks who site.1 with
    | none => exact fun impossible => impossible
    | some event =>
        rw [pending] at fresh
        have eventRank : event.val = rank := by
          have pendingSome := pending
          rw [← observedState] at pendingSome
          obtain ⟨_, eventReady, _, _⟩ := pendingEvent_spec pendingSome
          exact (ready_iff_rank setup _ rank ordered event).mp
            ((execution.application.publicView_eventReady event).mp eventReady)
        have eventCompleted : event ∈ control.execution.application.config.cut.completed :=
          (completed.2 event).mpr (by omega)
        exact not_eventFailedHistory_of_succeeded bounds _ certificate event stop stopState
          eventCompleted fresh who final finalMember
  have transport := abs_expect_offFailed_sub_completionValue_le bounds parameter utility
    excludedPayoff wellFormed contract timely (sequence n) retains retentionNonneg retentionLe
    (Profile.update (sig := model.behavioralSignature) (targetSequence n).strategy who
      (((targetSequence n).strategy who).withLaw site.1 law))
    (siteRank site.1)
    (fun start anchor state reached point decoded intendedPoint =>
      installed_dominates setup leaks bounds horizon scheduler contract timely retains
        sequence scale scale_pos scale_le_one weights targetSequence assembled n site.1 decision
        law start anchor state reached point decoded intendedPoint)
    (onePacketFailed setup leaks bounds horizon scheduler (model.agentAt site))
    (siteFresh who site.1) avoids who low range boundedReadout zeroWithin start startState
    (by rw [rankEq]; exact ⟨ordered, seen⟩)
  change |expect (model.runBehavioralFrom _ (2 * horizon + 1) start) _ - _| ≤ _
  rw [← model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded]
  exact transport

end Site

section ValueBlind

variable [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
    scheduler).History]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- The failure probability of the site's failure set, from one history of the
site, when `law` is installed there. -/
def siteHistoryFailure (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1) : ℝ :=
  expect (localHistoryRun (2 * horizon + 1) assessment site law history) fun final =>
    if final ∈ onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)
    then 1 else 0

/-- **Value-blind success from its two parts.** Suppose, from every history of a
site's belief, the completion value of a law is its success probability from
that history times the history's continuation value up to valueFree
(value-free success: the committed value is the source decision at the decoded
point and its success does not depend on it), and the belief average of these
products is the average success probability times the average continuation
value up to decorrelated (the failure probability and the continuation value
are uncorrelated under the belief). Then the site's completion value is its
success probability times the site's continuation value up to their sum. -/
theorem abs_siteStopValue_sub_le_of_valueFree (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1))
    {valueFree decorrelated : ℝ}
    (historyNear : ∀ history ∈ (assessment.belief who site).support,
      |historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment profile site law history.1 -
        (1 - siteHistoryFailure setup leaks bounds horizon scheduler assessment site law
          history) *
          decodedPointValue setup leaks bounds horizon scheduler parameter utility
            excludedPayoff profile who (siteRank site.1) history.1| ≤ valueFree)
    (uncorrelated : |expect (assessment.belief who site) (fun history =>
        (1 - siteHistoryFailure setup leaks bounds horizon scheduler assessment site law
          history) *
          decodedPointValue setup leaks bounds horizon scheduler parameter utility
            excludedPayoff profile who (siteRank site.1) history.1) -
      (1 - expect (assessment.belief who site)
          (siteHistoryFailure setup leaks bounds horizon scheduler assessment site law)) *
        expect (assessment.belief who site) (fun history =>
          decodedPointValue setup leaks bounds horizon scheduler parameter utility
            excludedPayoff profile who (siteRank site.1) history.1)| ≤ decorrelated) :
    |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site law -
      (1 - onePacketSiteFailure setup leaks bounds horizon scheduler assessment site law) *
        siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment profile site| ≤ valueFree + decorrelated := by
  obtain ⟨witness, witnessed⟩ := (assessment.belief who site).support_nonempty
  have freeNonneg : 0 ≤ valueFree := (abs_nonneg _).trans (historyNear witness witnessed)
  have failureEq : onePacketSiteFailure setup leaks bounds horizon scheduler assessment site law =
      expect (assessment.belief who site)
        (siteHistoryFailure setup leaks bounds horizon scheduler assessment site law) := by
    unfold onePacketSiteFailure localFailure siteHistoryFailure
    exact expect_localRun _ _ _ _ _
  rw [failureEq]
  unfold siteStopValue siteValue
  have first := abs_expect_sub_le_of_near (assessment.belief who site) _ _ freeNonneg
    historyNear
  calc _ ≤ |expect (assessment.belief who site) (fun history =>
          historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
            assessment profile site law history.1) -
        expect (assessment.belief who site) (fun history =>
          (1 - siteHistoryFailure setup leaks bounds horizon scheduler assessment site law
            history) *
            decodedPointValue setup leaks bounds horizon scheduler parameter utility
              excludedPayoff profile who (siteRank site.1) history.1)| + |_ - _| :=
        abs_sub_le _ _ _
    _ ≤ _ := add_le_add first uncorrelated

end ValueBlind

section Bounds

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- An expectation of a payoff within `[low, high]` on the support lies in
`[low, high]`. -/
private theorem expect_mem_Icc {α : Type*} (law : PMF α) (payoff : α → ℝ) {low high : ℝ}
    (within : ∀ point, low ≤ payoff point ∧ payoff point ≤ high) :
    low ≤ expect law payoff ∧ expect law payoff ≤ high := by
  have integrable : PayoffIntegrable law payoff :=
    payoffIntegrable_of_bounded law payoff (C := |low| + |high|) fun point => by
      have := within point
      rw [abs_le]
      constructor <;> cases abs_cases low <;> cases abs_cases high <;> linarith
  refine ⟨?_, expect_le_const law payoff integrable high fun point _ => (within point).2⟩
  have lower := expect_mono (μ := law) (f := fun _ => low) (g := payoff)
    (fun point _ => (within point).1) (payoffIntegrable_constant law low) integrable
  rwa [expect_constant] at lower

omit [Fintype Player] in
/-- **The source continuation value is between the exclusion payoff and the
upper utility.** If the exclusion payoff of `who` is at most its utility at
every terminal state the continuation of `profile` from a point of the intended
game reaches, and the utility is at most `upper`, the source continuation value
of `profile` at every point of the intended game lies in
`[excludedPayoff who, max (excludedPayoff who) upper]`. -/
theorem sourcePointValue_mem_Icc (profile : BehavioralProfile setup.program) (who : Player)
    (upper : ℝ) (le_upper : ∀ outcome, utility outcome who ≤ upper)
    (below : ∀ point, IntendedReached setup point →
      ∀ terminal ∈ (ProtocolState.continuationLaw setup.program profile point).support,
        excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (point : ProtocolState setup.program)
    (reachedPoint : IntendedReached setup point) :
    excludedPayoff who ≤ sourcePointValue setup parameter utility excludedPayoff profile who point ∧
      sourcePointValue setup parameter utility excludedPayoff profile who point ≤
        max (excludedPayoff who) upper := by
  classical
  unfold sourcePointValue
  rw [expect_map]
  have within : ∀ terminal ∈ (ProtocolState.continuationLaw setup.program profile point).support,
      excludedPayoff who ≤ exclusionReadoutUtility setup parameter utility excludedPayoff
        (some terminal) who ∧
      exclusionReadoutUtility setup parameter utility excludedPayoff (some terminal) who ≤
        max (excludedPayoff who) upper := by
    intro terminal member
    change excludedPayoff who ≤ exclusionUtility setup.program excludedPayoff utility
        (setup.parameterOutcome parameter terminal) who ∧
      exclusionUtility setup.program excludedPayoff utility
        (setup.parameterOutcome parameter terminal) who ≤ max (excludedPayoff who) upper
    unfold exclusionUtility
    split
    · exact ⟨below point reachedPoint terminal member,
        (le_upper _).trans (le_max_right _ _)⟩
    · exact ⟨le_rfl, le_max_left _ _⟩
  rw [expect_congr_on_support (g := fun terminal =>
    if terminal ∈ (ProtocolState.continuationLaw setup.program profile point).support then
      exclusionReadoutUtility setup parameter utility excludedPayoff (some terminal) who
    else excludedPayoff who) (fun terminal member => by rw [ite_eq_left member ..]; rfl)]
  apply expect_mem_Icc
  intro terminal
  split
  · rename_i member
    exact within terminal member
  · exact ⟨le_rfl, le_max_left _ _⟩

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The continuation value of a site is between the exclusion payoff and the
upper utility.** Under the hypotheses of `Vegas.sourcePointValue_mem_Icc` for
`profile`, the continuation value of a site lies in
`[excludedPayoff who, max (excludedPayoff who) upper]`. -/
theorem siteValue_mem_Icc (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who)
    (upper : ℝ) (le_upper : ∀ outcome, utility outcome who ≤ upper)
    (below : ∀ point, IntendedReached setup point →
      ∀ terminal ∈ (ProtocolState.continuationLaw setup.program profile point).support,
        excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who) :
    excludedPayoff who ≤ siteValue setup leaks bounds horizon scheduler parameter utility
        excludedPayoff assessment profile site ∧
      siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site ≤ max (excludedPayoff who) upper := by
  apply expect_mem_Icc
  intro history
  unfold decodedPointValue
  split
  · exact ⟨le_rfl, le_max_left _ _⟩
  · split
    · exact ⟨le_rfl, le_max_left _ _⟩
    · split
      · rename_i reachedPoint
        exact sourcePointValue_mem_Icc setup parameter utility excludedPayoff profile who upper
          le_upper below _ reachedPoint
      · exact ⟨le_rfl, le_max_left _ _⟩

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **Exclusion is a punishment on reached continuations.** If the exclusion
payoff of every player is at most its utility at every terminal readout of the
intended game, it is at most its utility at every terminal state the
continuation of the intended effective opening of an intended profile reaches
from a point the intended game reaches. -/
theorem excludedPayoff_le_of_reached [Finite Player] (wellFormed : setup.WellFormed)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (point : ProtocolState setup.program) (reachedPoint : IntendedReached setup point)
    (who : Player) :
    ∀ terminal ∈ (ProtocolState.continuationLaw setup.program
        (setup.intendedOpeningProfile intended) point).support,
      excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who := by
  have := Fintype.ofFinite Player
  obtain ⟨history, state⟩ := reachedPoint
  intro terminal member
  have law := setup.intendedOpeningProfile_runFrom wellFormed intended
    (setup.protocolRemaining history.state) history le_rfl
  have readout : some terminal ∈ ((setup.continuationLaw (setup.intendedOpeningProfile intended)
      history.state).map some).support := by
    rw [state]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨terminal, member, rfl⟩
  rw [← law] at readout
  obtain ⟨final, _, read⟩ := (PMF.mem_support_map_iff _ _ _).mp readout
  exact below final terminal read who

end Bounds

section Decomposition

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- **The continuation value of an agent.** At a decision information state, the
continuation value of its site (`Vegas.siteValue`); the exclusion payoff
elsewhere. -/
def siteContinuation (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) : ℝ :=
  if decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1 then
    siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff assessment
      profile ⟨agent.2.1, decision⟩
  else excludedPayoff agent.1

theorem siteContinuation_agentAt (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) :
    siteContinuation setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile ((onePacketN).agentAt site) =
      siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site := by
  unfold siteContinuation
  rw [dite_eq_left_of_eq_true (eq_true site.2)]
  rfl

/-- Under the hypotheses of `Vegas.siteValue_mem_Icc`, the continuation value of
every agent lies in `[excludedPayoff who, max (excludedPayoff who) upper]`. -/
theorem siteContinuation_mem_Icc (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (upper : ℝ) (le_upper : ∀ outcome, utility outcome agent.1 ≤ upper)
    (below : ∀ point, IntendedReached setup point →
      ∀ terminal ∈ (ProtocolState.continuationLaw setup.program profile point).support,
        excludedPayoff agent.1 ≤ utility (setup.parameterOutcome parameter terminal) agent.1) :
    excludedPayoff agent.1 ≤ siteContinuation setup leaks bounds horizon scheduler parameter
        utility excludedPayoff assessment profile agent ∧
      siteContinuation setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile agent ≤ max (excludedPayoff agent.1) upper := by
  unfold siteContinuation
  split
  · exact siteValue_mem_Icc setup leaks bounds horizon scheduler parameter utility
      excludedPayoff assessment profile _ upper le_upper below
  · exact ⟨le_rfl, le_max_left _ _⟩

end Decomposition

section Field

variable [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
    scheduler).History]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- **The value bounds and the transport error along a sequence.** Under bounded
utilities and vanishing scales, the transport error with the summed payoff
range of all players tends to zero; every agent's continuation value is at
least the exclusion payoff and within the gap bound of it; and, at every site,
a law whose completion value is within blind of its success probability times
the site's continuation value has its successful part within the transport
error plus blind of that product. -/
theorem siteDecomposition_of_completion (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (scale_vanishing : Tendsto scale atTop (nhds 0)) {slots : Nat}
    (gapBound : ℝ) (gap_le : ∀ who, upperUtility who - excludedPayoff who ≤ gapBound)
    (gapBound_nonneg : 0 ≤ gapBound)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) :
    ∃ transportError : ℕ → ℝ, Tendsto transportError atTop (nhds 0) ∧ (∀ n, 0 ≤ transportError n) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        excludedPayoff who ≤ siteContinuation setup leaks bounds horizon scheduler parameter
          utility excludedPayoff (targetSequence n)
          (setup.intendedOpeningProfile (sequence n).strategy) ((onePacketN).agentAt site) ∧
        siteContinuation setup leaks bounds horizon scheduler parameter utility excludedPayoff
            (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy)
            ((onePacketN).agentAt site) - excludedPayoff who ≤ gapBound ∧
        ∀ (law : PMF ((onePacketN).Choice who site.1)) (blind : ℝ),
          |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site law -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
              law) * siteValue setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy)
              site| ≤ blind →
          |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site law -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
              law) * siteContinuation setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy)
              ((onePacketN).agentAt site)| ≤ transportError n + blind := by
  let range := fun who : Player => max 0 (max (excludedPayoff who) (upperUtility who)) -
    min 0 (min (excludedPayoff who) (lowerUtility who))
  have rangeNonneg : ∀ who, 0 ≤ range who := fun who => by
    have := le_max_left 0 (max (excludedPayoff who) (upperUtility who))
    have := min_le_left 0 (min (excludedPayoff who) (lowerUtility who))
    simp only [range]
    linarith
  let total := ∑ who, range who
  have rangeLe : ∀ who, range who ≤ total := fun who =>
    Finset.single_le_sum (fun player _ => rangeNonneg player) (Finset.mem_univ who)
  let transportError := fun n : ℕ =>
    ((Fintype.card Player * (2 * horizon + 1) : ℕ) * (1 - slotRetention (scale n))) * total
  have transportLimit : Tendsto transportError atTop (nhds 0) := by
    have limit := (((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_slotRetention scale_vanishing)).const_mul
        ((Fintype.card Player * (2 * horizon + 1) : ℕ) : ℝ)).mul_const total
    simpa [transportError] using limit
  have transportNonneg : ∀ n, 0 ≤ transportError n := fun n =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (by linarith [slotRetention_le_one (scale_pos n).le (scale_le_one n)]))
      (Finset.sum_nonneg fun player _ => rangeNonneg player)
  refine ⟨transportError, transportLimit, transportNonneg, fun n who site => ?_⟩
  obtain ⟨lower, upper⟩ := siteContinuation_mem_Icc setup leaks bounds horizon scheduler
    parameter utility excludedPayoff (targetSequence n)
    (setup.intendedOpeningProfile (sequence n).strategy) ((onePacketN).agentAt site)
    (upperUtility who) (fun outcome => le_upper outcome who)
    (fun point reachedPoint => excludedPayoff_le_of_reached setup parameter utility excludedPayoff
      wellFormed below (sequence n).strategy point reachedPoint who)
  refine ⟨lower, ?_, fun law blind near => ?_⟩
  · have := gap_le who
    rcases le_total (excludedPayoff who) (upperUtility who) with low | high
    · rw [max_eq_right low] at upper
      linarith
    · rw [max_eq_left high] at upper
      linarith
  rw [siteContinuation_agentAt]
  have transport := abs_siteSuccess_sub_siteStopValue_le setup leaks bounds horizon scheduler
    parameter utility excludedPayoff wellFormed contract timely retains lowerUtility upperUtility
    lower_le le_upper sequence scale scale_pos scale_le_one weights targetSequence assembled n
    site law
  have widen : ((Fintype.card Player * (2 * horizon + 1) : ℕ) * (1 - slotRetention (scale n))) *
      range who ≤ transportError n :=
    mul_le_mul_of_nonneg_left (rangeLe who)
      (mul_nonneg (Nat.cast_nonneg _)
        (by linarith [slotRetention_le_one (scale_pos n).le (scale_le_one n)]))
  calc _ ≤ |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
          excludedPayoff (targetSequence n) site law -
        siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site law| +
        |_ - _| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (transport.trans widen) near

/-- **The value decomposition at late deliveries.** For a well-formed setup
under the asynchronous contract with timely delays and retention of first
covered canonical packets, with bounded utilities and vanishing tremble scales,
suppose exclusion is a punishment on intended continuations (below), the gap
bound covers the upper utility, and success is value-blind at late deliveries
(valueBlind): the completion value of each marked choice and of each late
option is within a vanishing error of its success probability times the
site's continuation value. Then the late value decomposition of
`Vegas.OnePacketOpenInputs` holds. -/
theorem onePacket_lateDecomposition (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (scale_vanishing : Tendsto scale atTop (nhds 0)) {slots : Nat}
    (gapBound : ℝ) (gap_le : ∀ who, upperUtility who - excludedPayoff who ≤ gapBound)
    (gapBound_nonneg : 0 ≤ gapBound)
    (valueBlind : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler
        slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one weights targetSequence →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
        ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
          (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
      ∃ blindError : ℕ → ℝ, Tendsto blindError atTop (nhds 0) ∧
        ∀ n who (site : (onePacketN).InformationSite who),
          ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
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
              blindError n) :
    ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
      (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        excludedPayoff who ≤ continuation n ((onePacketN).agentAt site) + error n ∧
        continuation n ((onePacketN).agentAt site) - excludedPayoff who ≤ gapBound ∧
        (∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
          |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site (PMF.pure choice) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (PMF.pure choice)) * continuation n ((onePacketN).agentAt site)| ≤
            error n) ∧
        ∀ option,
          |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site
              (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)) *
              continuation n ((onePacketN).agentAt site)| ≤ error n := by
  intro weights targetSequence assembled mixed bayes
  obtain ⟨blindError, blindLimit, blind⟩ := valueBlind weights targetSequence assembled mixed bayes
  obtain ⟨transportError, transportLimit, transportNonneg, holds⟩ :=
    siteDecomposition_of_completion setup leaks bounds horizon scheduler parameter utility
      excludedPayoff wellFormed contract timely retains lowerUtility upperUtility lower_le
      le_upper sequence below scale scale_pos scale_le_one scale_vanishing gapBound gap_le
      gapBound_nonneg weights targetSequence assembled
  refine ⟨fun n => siteContinuation setup leaks bounds horizon scheduler parameter utility
      excludedPayoff (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy),
    fun n => transportError n + |blindError n|,
    by simpa using transportLimit.add blindLimit.abs, fun n who site notFree keyed => ?_⟩
  obtain ⟨lower, gap, decompose⟩ := holds n who site
  obtain ⟨choices, options⟩ := blind n who site notFree keyed
  refine ⟨by linarith [transportNonneg n, abs_nonneg (blindError n)], gap,
    fun choice marked => decompose _ _ ((choices choice marked).trans (le_abs_self _)),
    fun option => decompose _ _ ((options option).trans (le_abs_self _))⟩

/-- **The value decomposition away from late deliveries.** Under the hypotheses
of `Vegas.onePacket_lateDecomposition`, with value-blind success away from late
deliveries (valueBlind): the completion value of each marked choice and of
the prescribed component is within a vanishing error of its success
probability times the site's continuation value. Then the non-late value
decomposition of `Vegas.OnePacketOpenInputs` holds. -/
theorem onePacket_nonLateDecomposition (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (scale_vanishing : Tendsto scale atTop (nhds 0))
    (gapBound : ℝ) (gap_le : ∀ who, upperUtility who - excludedPayoff who ≤ gapBound)
    (gapBound_nonneg : 0 ≤ gapBound) {slots : Nat}
    (valueBlind : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler
        slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one weights targetSequence →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
        ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
          (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
      ∃ blindError : ℕ → ℝ, Tendsto blindError atTop (nhds 0) ∧
        ∀ n who (site : (onePacketN).InformationSite who),
          ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ¬ ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
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
          |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
              (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one n ((onePacketN).agentAt site)) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
                scale_pos scale_le_one n ((onePacketN).agentAt site))) *
            siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
            blindError n) :
    ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
      (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        excludedPayoff who ≤ continuation n ((onePacketN).agentAt site) + error n ∧
        continuation n ((onePacketN).agentAt site) - excludedPayoff who ≤ gapBound ∧
        (∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
          |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site (PMF.pure choice) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (PMF.pure choice)) * continuation n ((onePacketN).agentAt site)| ≤
            error n) ∧
        |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
            excludedPayoff (targetSequence n) site
            (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one n ((onePacketN).agentAt site)) -
          (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one n ((onePacketN).agentAt site))) *
            continuation n ((onePacketN).agentAt site)| ≤ error n := by
  intro weights targetSequence assembled mixed bayes
  obtain ⟨blindError, blindLimit, blind⟩ := valueBlind weights targetSequence assembled mixed bayes
  obtain ⟨transportError, transportLimit, transportNonneg, holds⟩ :=
    siteDecomposition_of_completion setup leaks bounds horizon scheduler parameter utility
      excludedPayoff wellFormed contract timely retains lowerUtility upperUtility lower_le
      le_upper sequence below scale scale_pos scale_le_one scale_vanishing gapBound gap_le
      gapBound_nonneg weights targetSequence assembled
  refine ⟨fun n => siteContinuation setup leaks bounds horizon scheduler parameter utility
      excludedPayoff (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy),
    fun n => transportError n + |blindError n|,
    by simpa using transportLimit.add blindLimit.abs, fun n who site notFree notKeyed => ?_⟩
  obtain ⟨lower, gap, decompose⟩ := holds n who site
  obtain ⟨choices, prescribed⟩ := blind n who site notFree notKeyed
  refine ⟨by linarith [transportNonneg n, abs_nonneg (blindError n)], gap,
    fun choice marked => decompose _ _ ((choices choice marked).trans (le_abs_self _)),
    decompose _ _ (prescribed.trans (le_abs_self _))⟩

end Field

end Vegas
