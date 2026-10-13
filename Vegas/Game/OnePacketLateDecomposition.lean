/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateSuccess
import Vegas.Game.OnePacketCertificateDischarge

/-! # The value decomposition of late deliveries

**Installed laws keep as-if-honest play from reached boundaries.** Installing a
law at a late delivery of an assembled profile leaves its play at every forced
information state as-if-honest play reaches from a reached boundary: such a
state is not a late delivery (`Vegas.not_lateDelivery_of_honestReachedFrom`), so
it is not the late delivery, and its components are the slot-trembled prescribed
component (`Vegas.installedLate_dominates`).

**The successful part of a late delivery.** So, at a late delivery of an
assembled profile, the successful part of every law installed at the site is
within a vanishing error of its completion value
(`Vegas.abs_lateSiteSuccess_sub_lateStopValue_le`): the belief average of the
value at the first completion of the pending event, which is the source
continuation value of the intended effective opening at the decoded point when
that point is intended and the event did not fail
(`Vegas.lateStopValue`, `Vegas.lateSiteValue`).

**The decomposition.** The continuation value of an agent is the belief
average, over its site, of the source continuation value at the decoded point
before the pending event (`Vegas.lateContinuation`). It lies between the
exclusion payoff and the upper utility whenever exclusion is a punishment on
intended continuations (`Vegas.lateContinuation_mem_Icc`). Given that the
completion value of each late option and marked choice is its success
probability times this continuation value up to a vanishing error (value-blind
success: the success probability depends neither on the committed value nor,
under the belief, on the hidden values), the late value decomposition follows
(`Vegas.onePacket_lateValueDecomposition`, `Vegas.onePacket_lateDecomposition`).
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

/-- **Installed laws keep as-if-honest play from reached boundaries.** Under the
asynchronous contract with timely delays and retention of first covered
canonical packets, installing any law at a late delivery of a profile assembled
from mixtures of the components of the one-packet certificate gives, from every
one-packet history ending between rounds at a reached boundary decoding to a
point of the intended game, each choice at every forced information state
as-if-honest play reaches at least the slot retention of the scale times its
as-if-honest mass. -/
theorem installedLate_dominates {delay bound : (graph setup).EventId → Nat}
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
    (n : ℕ) {owner : Player} {late : (application setup leaks).Info}
    (lateDelivery : LateDelivery setup leaks owner late)
    (law : PMF ((onePacketN).Choice owner late))
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) (anchor : (application setup leaks).Execution) (rank : Nat)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (reached : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
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
        (((targetSequence n).strategy owner).withLaw late law) who info) choice).toReal := by
  have notLate := not_lateDelivery_of_honestReachedFrom bounds contract timely (sequence n)
    retains reached point decoded intendedPoint start state reachedInfo
  have occurs : ∃ history : ((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).History,
      (onePacketN).infoOf who history.trace = info := by
    obtain ⟨_, history, _, infoEq⟩ := reachedInfo
    exact ⟨history, infoEq⟩
  have base := onePacketMixture_ge_honest_of_not_late setup leaks bounds horizon scheduler
    sequence scale scale_pos scale_le_one n (weights n) notLate occurs forced choice
  have agrees : Profile.update (sig := (onePacketN).behavioralSignature)
      (targetSequence n).strategy owner (((targetSequence n).strategy owner).withLaw late law)
      who info = (targetSequence n).strategy who info := by
    by_cases same : who = owner
    · subst same
      have different : info ≠ late := fun equal => notLate (equal ▸ lateDelivery)
      rw [Profile.update_same, BehavioralPolicy.withLaw_of_ne _ _ _ different]
    · rw [Profile.update_of_ne _ _ same]
  rw [agrees, assembled n]
  exact base

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
          if ProtocolState.Intended setup.program point then
            sourcePointValue setup parameter utility excludedPayoff profile who point
          else excludedPayoff who

/-- **The continuation value of a late delivery.** The belief average, over the
histories of a site, of the source continuation value of `profile` at their
decoded point before the site's event. -/
def lateSiteValue (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (event : (graph setup).EventId) : ℝ :=
  expect (assessment.belief who site) fun history =>
    decodedPointValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
      profile who event.val history.1

open Classical in
/-- **The completion value of a late delivery.** The belief average, over the
histories of a site, of the expected completion value under play, with `law`
installed at the site, until the site's event completes: the source
continuation value of `profile` at the decoded point after the event, when it
is intended and the event did not fail, and the expected payoff of `who` off
the site's failure set otherwise. -/
def lateStopValue (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (event : (graph setup).EventId)
    (law : PMF ((onePacketN).Choice who site.1)) : ℝ :=
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let installed := Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy
    who ((assessment.strategy who).withLaw site.1 law)
  let payoff := fun final : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    if final ∈ EventFailedHistory setup leaks bounds horizon scheduler who event then 0
    else exclusionBase setup parameter utility excludedPayoff leaks final.state who
  expect (assessment.belief who site) fun history =>
    expect ((onePacketN).runBehavioralUntil certificate installed
        (LateStopped setup leaks bounds horizon scheduler event.val) history.1)
      (fun stop => if LateStopped setup leaks bounds horizon scheduler event.val stop then
        completionValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          profile event.val event who
          (fun later => expect ((onePacketN).runBehavioralTerminalFrom certificate installed later)
            payoff) stop
        else payoff stop)

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

/-- **The successful part of a late delivery is its completion value.** For a
well-formed setup under the asynchronous contract with timely delays and
retention of first covered canonical packets, at a late delivery of an
assembled profile with pending event `event`, the successful part of every law
installed at the site is within
`|Player| * (2 * horizon + 1) * (1 - slotRetention (scale n)) * range` of its
completion value, the source continuation values being those of the intended
effective opening of the source assessment. -/
theorem abs_lateSiteSuccess_sub_lateStopValue_le [Finite ((bounds.onePacketMenu (runtime setup)
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
    (lateDelivery : LateDelivery setup leaks who site.1) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    (law : PMF ((onePacketN).Choice who site.1)) :
    |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility excludedPayoff
        (targetSequence n) site law -
      lateStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site event law| ≤
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
  have failedEq : onePacketFailed setup leaks bounds horizon scheduler (model.agentAt site) =
      EventFailedHistory setup leaks bounds horizon scheduler who event := by
    change (match pendingEvent setup leaks who site.1 with
      | none => ∅
      | some event => EventFailedHistory setup leaks bounds horizon scheduler who event) = _
    rw [pending]
  obtain ⟨past, view, lateEvent, infoEq, latePending, activated⟩ := lateDelivery
  rw [pending, Option.some.injEq] at latePending
  subst latePending
  unfold onePacketSiteSuccess localSuccessValue lateStopValue
  rw [failedEq, expect_localRun]
  apply abs_expect_sub_le_of_near _ _ _
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) rangeNonneg)
  intro history _
  obtain ⟨start, observed⟩ := history
  have observedState : (application setup leaks).observe who start.state = some (past, view) :=
    ((menu.info (initialLaw setup) horizon scheduler who start.trace).symm.trans observed).trans
      infoEq
  rcases startState : start.state with _ | ⟨remaining, actor, execution⟩
  · rw [startState] at observedState
    cases observedState
  rw [startState] at observedState
  have actorEq : actor = some who := by
    by_contra different
    simp [ReactiveApplication.observe, different] at observedState
  subst actorEq
  simp only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
    at observedState
  obtain ⟨_, viewEq⟩ := observedState
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    startState ▸ menu.toRawTrace (initialLaw setup) horizon scheduler start.trace
  obtain ⟨rank, ordered, seen⟩ := pendingAt_history rawTrace
  have rankEq : event.val = rank := by
    have pendingSome := pending
    rw [infoEq] at pendingSome
    obtain ⟨_, eventReady, _, _⟩ := pendingEvent_spec pendingSome
    rw [← viewEq] at eventReady
    exact (ready_iff_rank setup _ rank ordered event).mp
      ((execution.application.publicView_eventReady event).mp eventReady)
  subst rankEq
  have transport := abs_expect_offFailed_sub_completionValue_le bounds parameter utility
    excludedPayoff wellFormed contract timely (sequence n) retains retentionNonneg retentionLe
    (Profile.update (sig := model.behavioralSignature) (targetSequence n).strategy who
      (((targetSequence n).strategy who).withLaw site.1 law))
    (fun start anchor rank state reached point decoded intendedPoint =>
      installedLate_dominates setup leaks bounds horizon scheduler contract timely retains
        sequence scale scale_pos scale_le_one weights targetSequence assembled n
        ⟨past, view, event, infoEq, pending, activated⟩ law start anchor rank state
        reached point decoded intendedPoint)
    (EventFailedHistory setup leaks bounds horizon scheduler who event) event.val
    event rfl
    (fun stop control stopState completed succeeded =>
      not_eventFailedHistory_of_succeeded bounds _ certificate event stop stopState
        completed succeeded who)
    who low range boundedReadout zeroWithin start startState ⟨ordered, seen⟩
  change |expect (model.runBehavioralFrom _ (2 * horizon + 1) start) _ - _| ≤ _
  rw [← model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded]
  exact transport

end Site

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
    (below : ∀ point, ProtocolState.Intended setup.program point →
      ∀ terminal ∈ (ProtocolState.continuationLaw setup.program profile point).support,
        excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (point : ProtocolState setup.program)
    (intendedPoint : ProtocolState.Intended setup.program point) :
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
    · exact ⟨below point intendedPoint terminal member,
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
/-- **The continuation value of a late delivery is between the exclusion payoff
and the upper utility.** Under the hypotheses of
`Vegas.sourcePointValue_mem_Icc` for `profile`, the continuation value of a late
delivery lies in `[excludedPayoff who, max (excludedPayoff who) upper]`. -/
theorem lateSiteValue_mem_Icc (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (event : (graph setup).EventId)
    (upper : ℝ) (le_upper : ∀ outcome, utility outcome who ≤ upper)
    (below : ∀ point, ProtocolState.Intended setup.program point →
      ∀ terminal ∈ (ProtocolState.continuationLaw setup.program profile point).support,
        excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who) :
    excludedPayoff who ≤ lateSiteValue setup leaks bounds horizon scheduler parameter utility
        excludedPayoff assessment profile site event ∧
      lateSiteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site event ≤ max (excludedPayoff who) upper := by
  apply expect_mem_Icc
  intro history
  unfold decodedPointValue
  split
  · exact ⟨le_rfl, le_max_left _ _⟩
  · split
    · exact ⟨le_rfl, le_max_left _ _⟩
    · split
      · rename_i intendedPoint
        exact sourcePointValue_mem_Icc setup parameter utility excludedPayoff profile who upper
          le_upper below _ intendedPoint
      · exact ⟨le_rfl, le_max_left _ _⟩

end Bounds

section Decomposition

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- **The continuation value of an agent.** At a decision information state with
a pending event, the continuation value of the late delivery there
(`Vegas.lateSiteValue`); the exclusion payoff elsewhere. -/
def lateContinuation (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) : ℝ :=
  if decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1 then
    match pendingEvent setup leaks agent.1 agent.2.1 with
    | some event => lateSiteValue setup leaks bounds horizon scheduler parameter utility
        excludedPayoff assessment profile ⟨agent.2.1, decision⟩ event
    | none => excludedPayoff agent.1
  else excludedPayoff agent.1

theorem lateContinuation_agentAt (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event) :
    lateContinuation setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile ((onePacketN).agentAt site) =
      lateSiteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site event := by
  unfold lateContinuation
  rw [dite_eq_left_of_eq_true (eq_true site.2)]
  change (match pendingEvent setup leaks who site.1 with
    | some event => lateSiteValue setup leaks bounds horizon scheduler parameter utility
        excludedPayoff assessment profile ⟨site.1, site.2⟩ event
    | none => excludedPayoff who) = _
  rw [pending]
  rfl

/-- Under the hypotheses of `Vegas.lateSiteValue_mem_Icc`, the continuation value
of every agent lies in `[excludedPayoff who, max (excludedPayoff who) upper]`. -/
theorem lateContinuation_mem_Icc (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (upper : ℝ) (le_upper : ∀ outcome, utility outcome agent.1 ≤ upper)
    (below : ∀ point, ProtocolState.Intended setup.program point →
      ∀ terminal ∈ (ProtocolState.continuationLaw setup.program profile point).support,
        excludedPayoff agent.1 ≤ utility (setup.parameterOutcome parameter terminal) agent.1) :
    excludedPayoff agent.1 ≤ lateContinuation setup leaks bounds horizon scheduler parameter
        utility excludedPayoff assessment profile agent ∧
      lateContinuation setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile agent ≤ max (excludedPayoff agent.1) upper := by
  unfold lateContinuation
  split
  · split
    · exact lateSiteValue_mem_Icc setup leaks bounds horizon scheduler parameter utility
        excludedPayoff assessment profile _ _ upper le_upper below
    · exact ⟨le_rfl, le_max_left _ _⟩
  · exact ⟨le_rfl, le_max_left _ _⟩

end Decomposition

section Field

variable [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
    scheduler).History]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- **The value decomposition of late deliveries.** For a well-formed setup
under the asynchronous contract with timely delays and retention of first
covered canonical packets, with bounded utilities, along vanishing tremble
scales, suppose:

* *exclusion is a punishment on intended continuations*: the exclusion payoff
  of each player is at most its utility at every terminal state the
  continuation of the intended effective opening of the source assessment
  reaches from a point of the intended game (which the source hypothesis
  `below` of `Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_extends_to_exclusion`
  gives for points the intended game reaches);
* *the gap bound covers the upper utility*;
* *value-blind success* (`valueBlind`): at every forced late delivery of every
  assembled fully mixed Bayes profile sequence, the completion value
  (`Vegas.lateStopValue`) of each late option and of each marked choice is
  within a vanishing error of its success probability times the continuation
  value of the site (`Vegas.lateSiteValue`). This is where value-blind binding
  inclusion (opaque commitments) and the forced-belief fiber results enter:
  the success probability does not depend on the committed value nor, under
  the belief, on the hidden values the continuation value depends on.

Then every such sequence has continuation values of its agents, the exclusion
payoff at most each one and within the gap bound of it, such that at every
forced late delivery the successful part of each late option and of each
marked choice is its success probability times the continuation value, up to a
vanishing error. -/
theorem onePacket_lateValueDecomposition (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (below : ∀ n who point, ProtocolState.Intended setup.program point →
      ∀ terminal ∈ (ProtocolState.continuationLaw setup.program
          (setup.intendedOpeningProfile (sequence n).strategy) point).support,
        excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (scale_vanishing : Tendsto scale atTop (nhds 0)) {slots : Nat}
    (gapBound : ℝ) (gap_le : ∀ who, upperUtility who - excludedPayoff who ≤ gapBound)
    (gapBound_nonneg : 0 ≤ gapBound)
    (compared : ∀ who (site : (onePacketN).InformationSite who),
      (onePacketN).Choice who site.1 → Prop)
    (valueBlind : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler
        slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one weights targetSequence →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
        ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
          (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
      ∃ blindError : ℕ → ℝ, Tendsto blindError atTop (nhds 0) ∧
        ∀ n who (site : (onePacketN).InformationSite who) (event : (graph setup).EventId),
          ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
            (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
            ((onePacketN).agentAt site) →
          pendingEvent setup leaks who site.1 = some event →
          (∀ choice, compared who site choice →
            |lateStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site event
                (PMF.pure choice) -
              (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
                site (PMF.pure choice)) *
              lateSiteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
                event| ≤ blindError n) ∧
          ∀ option,
            |lateStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site event
                (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) -
              (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
                site (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)) *
              lateSiteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
                event| ≤ blindError n)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) :
    ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        excludedPayoff who ≤ continuation n ((onePacketN).agentAt site) + error n ∧
        continuation n ((onePacketN).agentAt site) - excludedPayoff who ≤ gapBound ∧
        (ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
            (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
            ((onePacketN).agentAt site) →
          (∀ choice, compared who site choice →
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
                continuation n ((onePacketN).agentAt site)| ≤ error n) := by
  obtain ⟨blindError, blindLimit, blind⟩ := valueBlind weights targetSequence assembled mixed bayes
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
  refine ⟨fun n => lateContinuation setup leaks bounds horizon scheduler parameter utility
      excludedPayoff (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy),
    fun n => transportError n + |blindError n|, by simpa using transportLimit.add blindLimit.abs,
    ?_⟩
  intro n who site notFree
  have retentionLe := slotRetention_le_one (scale_pos n).le (scale_le_one n)
  have transportNonneg : 0 ≤ transportError n :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith))
      (Finset.sum_nonneg fun player _ => rangeNonneg player)
  obtain ⟨lower, upper⟩ := lateContinuation_mem_Icc setup leaks bounds horizon scheduler
    parameter utility excludedPayoff (targetSequence n)
    (setup.intendedOpeningProfile (sequence n).strategy) ((onePacketN).agentAt site)
    (upperUtility who) (fun outcome => le_upper outcome who) (below n who)
  refine ⟨by linarith [abs_nonneg (blindError n)], ?_, fun keyed => ?_⟩
  · have := gap_le who
    rcases le_total (excludedPayoff who) (upperUtility who) with low | high
    · rw [max_eq_right low] at upper
      linarith
    · rw [max_eq_left high] at upper
      linarith
  obtain ⟨past, view, event, infoEq, pending, activated⟩ := keyed.1
  have lateDelivery : LateDelivery setup leaks who site.1 :=
    ⟨past, view, event, infoEq, pending, activated⟩
  beta_reduce
  rw [lateContinuation_agentAt setup leaks bounds horizon scheduler parameter utility
    excludedPayoff (targetSequence n) _ site pending]
  have near := fun law => abs_lateSiteSuccess_sub_lateStopValue_le setup leaks bounds horizon
    scheduler parameter utility excludedPayoff wellFormed contract timely retains lowerUtility
    upperUtility lower_le le_upper sequence scale scale_pos scale_le_one weights targetSequence
    assembled n site lateDelivery pending law
  have widen : ((Fintype.card Player * (2 * horizon + 1) : ℕ) * (1 - slotRetention (scale n))) *
      range who ≤ transportError n :=
    mul_le_mul_of_nonneg_left (rangeLe who)
      (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  obtain ⟨blindChoices, blindOptions⟩ := blind n who site event notFree keyed pending
  refine ⟨fun choice marked => ?_, fun option => ?_⟩
  · have first := near (PMF.pure choice)
    have second := blindChoices choice marked
    calc _ ≤ |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
            excludedPayoff (targetSequence n) site (PMF.pure choice) -
          lateStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
            (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site event
            (PMF.pure choice)| + |_ - _| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (first.trans widen) (second.trans (le_abs_self _))
  · have first := near (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)
    have second := blindOptions option
    calc _ ≤ |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
            excludedPayoff (targetSequence n) site
            (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) -
          lateStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
            (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site event
            (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)| + |_ - _| :=
          abs_sub_le _ _ _
      _ ≤ _ := add_le_add (first.trans widen) (second.trans (le_abs_self _))

end Field

section Field

variable [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
    scheduler).History]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- **The late value decomposition of the open inputs.** Under the hypotheses of
`Vegas.onePacket_lateValueDecomposition` for the marked choices of the
one-packet certificate, the late value decomposition of
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
    (below : ∀ n who point, ProtocolState.Intended setup.program point →
      ∀ terminal ∈ (ProtocolState.continuationLaw setup.program
          (setup.intendedOpeningProfile (sequence n).strategy) point).support,
        excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
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
        ∀ n who (site : (onePacketN).InformationSite who) (event : (graph setup).EventId),
          ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
            (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
            ((onePacketN).agentAt site) →
          pendingEvent setup leaks who site.1 = some event →
          (∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
            |lateStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site event
                (PMF.pure choice) -
              (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
                site (PMF.pure choice)) *
              lateSiteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
                event| ≤ blindError n) ∧
          ∀ option,
            |lateStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site event
                (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) -
              (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
                site (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)) *
              lateSiteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
                event| ≤ blindError n) :
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
  obtain ⟨continuation, error, limit, holds⟩ := onePacket_lateValueDecomposition setup leaks
    bounds horizon scheduler parameter utility excludedPayoff wellFormed contract timely retains
    lowerUtility upperUtility lower_le le_upper sequence below scale scale_pos scale_le_one
    scale_vanishing gapBound gap_le gapBound_nonneg
    (onePacketCompared setup leaks bounds horizon scheduler) valueBlind weights targetSequence
    assembled mixed bayes
  refine ⟨continuation, error, limit, fun n who site notFree keyed => ?_⟩
  obtain ⟨lower, gap, late⟩ := holds n who site notFree
  exact ⟨lower, gap, (late keyed).1, (late keyed).2⟩

end Field

end Vegas
