/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateDecomposition
import Vegas.Game.OnePacketNextEvent

/-! # Sites whose pending event fails surely

**No success where failure is sure.** A law whose event-level failure at a site
is one has no successful part: the local run is supported on failed histories,
on which the successful part is zero (`Vegas.onePacketSiteSuccess_eq_zero`).

**Transmit or fail surely.** Under the asynchronous contract, at a forced
first activation of `who` with a pending event, either the canonical decisions
transmit, or every choice under every assessment fails the event surely and has
no successful part (`Vegas.firstActivation_transmits_or_doomed`). The second
branch is a disclosure whose resolution of an opening already publishes a
failure; there the site's failure set is the event-level failure of the pending
event (`Vegas.onePacketFailed_of_pending`); without a pending event it is
empty (`Vegas.onePacketFailed_of_unpending`).

**No completion value where a disclosure is doomed.** At a site whose pending
disclosure resolves to a failure at every belief history, play until the event
completes stops at a failed output, where the completion value falls back to
the payoff off the failure set, and every terminal continuation is failed; so
the completion value of every law is zero
(`Vegas.doomedDisclosure_siteStopValue_eq_zero`).
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

/-- At an information state with `event` pending, the failure set of the agent
is the event-level failure of `event`. -/
theorem onePacketFailed_of_pending {who : Player}
    {info : (onePacketN).InfoState who} (played : info ∈ (onePacketN).playedInformation who)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who info = some event) :
    onePacketFailed setup leaks bounds horizon scheduler ⟨who, info, played⟩ =
      EventFailedHistory setup leaks bounds horizon scheduler who event := by
  unfold onePacketFailed
  change (match pendingEvent setup leaks who info with
    | none => ∅
    | some event => EventFailedHistory setup leaks bounds horizon scheduler who event) = _
  rw [pending]

/-- At an information state without a pending event, the failure set of the
agent is empty. -/
theorem onePacketFailed_of_unpending {who : Player}
    {info : (onePacketN).InfoState who} (played : info ∈ (onePacketN).playedInformation who)
    (pending : pendingEvent setup leaks who info = none) :
    onePacketFailed setup leaks bounds horizon scheduler ⟨who, info, played⟩ = ∅ := by
  unfold onePacketFailed
  change (match pendingEvent setup leaks who info with
    | none => ∅
    | some event => EventFailedHistory setup leaks bounds horizon scheduler who event) = _
  rw [pending]

/-- **No success where failure is sure.** A law whose event-level failure at a
site is one has successful part zero. -/
theorem onePacketSiteSuccess_eq_zero (assessment : (onePacketN).BehavioralAssessment)
    {who : Player} (site : (onePacketN).InformationSite who)
    (law : PMF ((onePacketN).Choice who site.1))
    (sure : onePacketSiteFailure setup leaks bounds horizon scheduler assessment site law = 1) :
    onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility excludedPayoff
      assessment site law = 0 := by
  classical
  unfold onePacketSiteFailure localFailure at sure
  rw [expect_indicator, ENNReal.toReal_eq_one_iff, PMF.toOuterMeasure_apply_eq_one_iff] at sure
  unfold onePacketSiteSuccess localSuccessValue
  rw [expect_congr_on_support (g := fun _ => 0) fun history member => by
    simp only [sure member, ↓reduceIte]]
  exact expect_constant _ 0

/-- **Transmit or fail surely.** Under the asynchronous contract, at a forced
first activation of `who` with `event` pending, either the canonical decisions
transmit, or every choice under every assessment fails `event` surely and has
no successful part. -/
theorem firstActivation_transmits_or_doomed
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {event : (graph setup).EventId}
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup)
      horizon scheduler who (some (past, view)))
    (pending : pendingEvent setup leaks who (some (past, view)) = some event)
    (first : ∀ entry ∈ past, ¬ ActivatedAt setup leaks who event entry) :
    CanonicalTransmitsAt setup leaks who past view event ∨
      ∀ (assessment : (onePacketN).BehavioralAssessment)
        (decision : (onePacketN).IsDecisionInfo who (some (past, view)))
        (choice : (onePacketN).Choice who (some (past, view))),
        onePacketSiteFailure setup leaks bounds horizon scheduler assessment
            ⟨some (past, view), decision⟩ (PMF.pure choice) = 1 ∧
          onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
            excludedPayoff assessment ⟨some (past, view), decision⟩ (PMF.pure choice) = 0 := by
  rcases firstActivationTransmits_of_contract setup leaks bounds horizon scheduler contract who
    past view event forced pending first with transmits | doomed
  · exact Or.inl transmits
  · refine Or.inr fun assessment decision choice => ?_
    have failure : onePacketSiteFailure setup leaks bounds horizon scheduler assessment
        ⟨some (past, view), decision⟩ (PMF.pure choice) = 1 := by
      unfold onePacketSiteFailure
      erw [onePacketFailed_of_pending setup leaks bounds horizon scheduler _ pending]
      exact doomed assessment decision choice
    exact ⟨failure, onePacketSiteSuccess_eq_zero setup leaks bounds horizon scheduler parameter
      utility excludedPayoff assessment _ _ failure⟩

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- Terminal histories whose configuration is reached from one at which a
disclosure of `who` is ready with the resolution of an opening publishing a
failure are event-level failed histories of `who` for it. -/
private theorem doomed_failed_of_reaches
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    {control : (application setup leaks).Control} {event : (graph setup).EventId}
    (ready : control.execution.application.config.cut.Ready event) {who : Player}
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks)
    (doomed : EventGraph.EventCode.resolveOutput? binding checks true
      control.execution.application.config.store = some .failure)
    (final : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    {finalControl : (application setup leaks).Control} (state : final.state = some finalControl)
    (reach : ConfigReaches setup control.execution.application.config
      finalControl.execution.application.config)
    (stopped : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).terminal final.state) :
    final ∈ EventFailedHistory setup leaks bounds horizon scheduler who event := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  rw [state] at stopped
  have trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some finalControl) :=
    state ▸ menu.toRawTrace (initialLaw setup) horizon scheduler final.trace
  have terminal := completes finalControl trace stopped
  have done : event ∈ finalControl.execution.application.config.cut.completed := by
    rw [terminal]
    exact Finset.mem_univ _
  have failed := doomedDisclosure_output_failure reach ready (outputEq := outputEq)
    (codeEq := codeEq) doomed done
  change sourceReadout setup leaks final.state ∈ EventFailedReadout setup who event
  rw [state]
  exact eventFailedReadout_of_publicationFailure setup leaks finalControl terminal
    (nodeView_resolve_actor outputEq codeEq) outputEq failed

open Classical in
/-- **A doomed disclosure has no completion value.** Under a scheduler that
completes play, at a site whose pending event is a disclosure of its player
with the resolution of an opening publishing a failure at every history of the
belief, the completion value of every law is zero: play until the event
completes stops at a failed output, where the value falls back to the payoff
off the failure set, and every terminal continuation is failed. -/
theorem doomedDisclosure_siteStopValue_eq_zero
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (assessment : (onePacketN).BehavioralAssessment) (profile : BehavioralProfile setup.program)
    {who : Player} (site : (onePacketN).InformationSite who)
    (law : PMF ((onePacketN).Choice who site.1)) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks)
    (doomedAt : ∀ history ∈ (assessment.belief who site).support,
      ∃ control, history.1.state = some control ∧
        EventGraph.EventCode.resolveOutput? binding checks true
          control.execution.application.config.store = some .failure) :
    siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
      assessment profile site law = 0 := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketN
  have freshIff : ∀ control, siteFresh who site.1 control ↔
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [siteFresh, pending]
  have failedEq : onePacketFailed setup leaks bounds horizon scheduler
      ((onePacketN).agentAt site) = EventFailedHistory setup leaks bounds horizon scheduler who
        event :=
    onePacketFailed_of_pending setup leaks bounds horizon scheduler _ pending
  obtain ⟨past, view, atSite⟩ : ∃ past view, site.1 = some (past, view) := by
    cases info : site.1 with
    | none =>
        rw [info] at pending
        cases pending
    | some input => exact ⟨input.1, input.2, rfl⟩
  have pendingAt := pending
  rw [atSite] at pendingAt
  unfold siteStopValue
  refine (expect_congr_on_support (g := fun _ => 0) fun history member => ?_).trans
    (expect_constant _ 0)
  obtain ⟨control, current, doomed⟩ := doomedAt history member
  obtain ⟨control', current', ready, _, viewEq⟩ := pendingEvent_ready_unique bounds horizon
    scheduler pendingAt history.1 (history.2.trans atSite)
  rw [current, Option.some.injEq] at current'
  subst current'
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control) :=
    menu.toRawTrace (initialLaw setup) horizon scheduler (current ▸ history.1.trace)
  obtain ⟨found, foundOrdered, _⟩ := pendingAt_history rawTrace
  have rankEq : event.val = siteRank site.1 := by
    rw [atSite, viewEq]
    change event.val =
      (control.execution.application.config.history.map EventGraph.Completion.event).length
    rw [List.length_map, history_length_of_isPrefix _ foundOrdered]
    exact (ready_iff_rank setup _ _ foundOrdered event).mp ready
  let reaches : (menu.protocol (initialLaw setup) horizon scheduler).State → Prop :=
    fun state => ∃ next, state = some next ∧ ConfigReaches setup
      control.execution.application.config next.execution.application.config
  have closed : ∀ state joint target, reaches state →
      target ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler state
        joint).support → reaches target := by
    intro state joint target holds reached
    obtain ⟨before, rfl, reach⟩ := holds
    obtain ⟨next, rfl, step⟩ := transition_some_configStep (initialLaw setup) horizon
      scheduler before target joint reached
    exact ⟨next, rfl, reach.tail step⟩
  have failedOf : ∀ final : (menu.protocol (initialLaw setup) horizon scheduler).History,
      reaches final.state → (menu.protocol (initialLaw setup) horizon scheduler).terminal
        final.state →
      final ∈ onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site) :=
    by
    intro final ⟨finalControl, state, reach⟩ stopped
    rw [failedEq]
    exact doomed_failed_of_reaches setup leaks bounds horizon scheduler completes ready
      outputEq codeEq doomed final state reach stopped
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let installed := Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy
    who ((assessment.strategy who).withLaw site.1 law)
  have terminalZero : ∀ later, reaches later.state →
      expect (model.runBehavioralTerminalFrom certificate installed later) (fun final =>
        if final ∈ onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)
        then 0 else exclusionBase setup parameter utility excludedPayoff leaks final.state who) =
        0 := by
    intro later holds
    refine (expect_congr_on_support (g := fun _ => 0) fun final supported => ?_).trans
      (expect_constant _ 0)
    have reached := model.runBehavioralTerminalFrom_support_closed certificate installed reaches
      (fun state joint _ target holds reached => closed state joint target holds reached) later
      holds final supported
    have stopped := model.runBehavioralTerminalFrom_support_terminal certificate installed later
      final supported
    simp only [failedOf final reached stopped, ↓reduceIte]
  unfold historyStopValue
  refine (expect_congr_on_support (g := fun _ => 0) fun stop stopMember => ?_).trans
    (expect_constant _ 0)
  have stopReaches := model.runBehavioralUntil_support_closed certificate installed _ reaches
    (fun state joint _ target holds reached => closed state joint target holds reached)
    history.1 ⟨control, current, Relation.ReflTransGen.refl⟩ stop stopMember
  by_cases stopped : LateStopped setup leaks bounds horizon scheduler (siteRank site.1) stop
  · simp only [stopped, ↓reduceIte]
    obtain ⟨stopControl, stopState, stopReach⟩ := stopReaches
    obtain ⟨prefixControl, prefixState, prefixed⟩ := stopped
    rw [stopState, Option.some.injEq] at prefixState
    subst prefixState
    have done : event ∈ stopControl.execution.application.config.cut.completed :=
      (prefixed.2 event).mpr (by omega)
    have output := doomedDisclosure_output_failure stopReach ready (outputEq := outputEq)
      (codeEq := codeEq) doomed done
    have stale : ¬ siteFresh who site.1 stopControl := fun fresh =>
      (freshIff stopControl).mp fresh
        (storeEventFailed_of_ref _ event _ rfl output rfl)
    have fallback := terminalZero stop ⟨stopControl, stopState, stopReach⟩
    unfold completionValue
    rw [stopState]
    dsimp only
    split
    · exact fallback
    · simp only [stale, and_false, ↓reduceIte]
      exact fallback
  · simp only [stopped, ↓reduceIte]
    have ended := (model.mem_support_runBehavioralUntil certificate installed _ history.1 stop
      stopMember).resolve_left stopped
    simp only [failedOf stop stopReaches ended, ↓reduceIte]

end Vegas
