/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateDecomposition
import Vegas.Game.OnePacketNextEvent
import Vegas.Game.OnePacketCompletionLaw
import Vegas.Game.OnePacketLateCompletion

/-! # Completion values from completion-point laws with success one

**The rank of a pending site.** At every history of an information state with
a pending event, the configuration is a completed prefix of the site's rank,
and the pending event is the ready event of that rank
(`Vegas.pendingEvent_siteRank`).

**Failure from a completion-point law.** A stop with a completion point has
completed the pending event without a failure, so terminal play from it never
fails the event. So, when the completion-point law from a history has success
one up to an error, the failure probability from the history is at most that
error (`Vegas.siteHistoryFailure_le_of_completionPointLaw`), and the completion
value from the history is one less its failure probability times its
continuation value, up to three times the error times the payoff bound, when
the step law keeps the continuation value
(`Vegas.abs_historyStopValue_sub_le_of_sureCompletion`).

**At a site.** When this holds at every history of a site's belief, the site's
completion value is one less its failure probability times its continuation
value up to five times the error times the payoff bound: the failure
probability is at most the error at every history, so it is uncorrelated with
the continuation value up to twice the error times the bound
(`Vegas.abs_siteStopValue_sub_le_of_sureCompletion`).
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

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The rank of a pending site.** At every history of an information state of
`who` with `event` pending, the configuration is a completed prefix of the
site's rank, at which `event` is ready and has that rank. -/
theorem pendingEvent_siteRank {who : Player} {info : (onePacketN).InfoState who}
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who info = some event)
    (history : (onePacketN).InformationHistory who info) :
    ∃ control, history.1.state = some control ∧
      control.execution.application.config.cut.IsPrefix (siteRank info) ∧
      control.execution.application.config.cut.Ready event ∧ event.val = siteRank info := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨past, view, atInfo⟩ : ∃ past view, info = some (past, view) := by
    cases info with
    | none => cases pending
    | some input => exact ⟨input.1, input.2, rfl⟩
  subst atInfo
  obtain ⟨control, current, ready, _, viewEq⟩ := pendingEvent_ready_unique bounds horizon
    scheduler pending history.1 history.2
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control) :=
    menu.toRawTrace (initialLaw setup) horizon scheduler (current ▸ history.1.trace)
  obtain ⟨found, foundOrdered, _⟩ := pendingAt_history rawTrace
  have rankEq : siteRank (some (past, view)) = found := by
    rw [viewEq]
    change (control.execution.application.config.history.map EventGraph.Completion.event).length
      = found
    rw [List.length_map]
    exact history_length_of_isPrefix _ foundOrdered
  rw [rankEq]
  exact ⟨control, current, foundOrdered, ready,
    (ready_iff_rank setup _ _ foundOrdered event).mp ready⟩

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- A history with a completion point has completed the events of the next
rank, at a control satisfying the freshness property. -/
theorem completionPoint_isSome_spec {rank : Nat}
    {fresh : (application setup leaks).Control → Prop}
    {stop : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History}
    (isSome : (completionPoint setup leaks bounds horizon scheduler rank fresh stop).isSome) :
    ∃ control, stop.state = some control ∧
      control.execution.application.config.cut.IsPrefix (rank + 1) ∧ fresh control := by
  classical
  unfold completionPoint at isSome
  cases state : stop.state with
  | none =>
      rw [state] at isSome
      cases isSome
  | some control =>
      rw [state] at isSome
      dsimp only at isSome
      split at isSome
      · rename_i prefixed
        split at isSome
        · split at isSome
          · rename_i good
            exact ⟨control, rfl, prefixed, good.2⟩
          · cases isSome
        · cases isSome
      · cases isSome

section Values

variable [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
    scheduler).History]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- From a history of a site with a pending event, the completion indicator of
a stop bounds terminal success from it: terminal play from a stop with a
completion point never fails the event. -/
private theorem terminalFailure_le_of_stop (assessment : (onePacketN).BehavioralAssessment)
    {who : Player} (site : (onePacketN).InformationSite who)
    (law : PMF ((onePacketN).Choice who site.1)) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    (stop : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) (rankEq : event.val = siteRank site.1) :
    expect ((onePacketN).runBehavioralTerminalFrom
        ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories
        (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
          ((assessment.strategy who).withLaw site.1 law)) stop)
      (fun final => if final ∈ onePacketFailed setup leaks bounds horizon scheduler
        ((onePacketN).agentAt site) then (1 : ℝ) else 0) ≤
      1 - completionIndicator setup leaks bounds horizon scheduler (siteRank site.1)
        (siteFresh who site.1) stop := by
  cases point : completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
      (siteFresh who site.1) stop with
  | none =>
      simp only [completionIndicator, point, Option.elim_none, sub_zero]
      exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1 fun _ _ => by
        split <;> norm_num
  | some target =>
      simp only [completionIndicator, point, Option.elim_some, sub_self]
      obtain ⟨control, state, prefixed, fresh⟩ := completionPoint_isSome_spec setup leaks bounds
        horizon scheduler (by rw [point]; rfl)
      have stale : ¬ StoreEventFailed control.execution.application.config.store event := by
        simpa only [siteFresh, pending] using fresh
      have done : event ∈ control.execution.application.config.cut.completed :=
        (prefixed.2 event).mpr (by omega)
      have failedEq : onePacketFailed setup leaks bounds horizon scheduler
          ((onePacketN).agentAt site) = EventFailedHistory setup leaks bounds horizon scheduler
            who event := by
        unfold onePacketFailed
        change (match pendingEvent setup leaks who site.1 with
          | none => ∅
          | some event => EventFailedHistory setup leaks bounds horizon scheduler who event) = _
        rw [pending]
      refine le_of_eq (expect_congr_on_support (g := fun _ => 0) (fun final member => ?_) |>.trans
        (expect_constant _ 0))
      rw [failedEq]
      exact ite_eq_right_iff.mpr fun inFailed => (not_eventFailedHistory_of_succeeded bounds _ _
        event stop state done stale who final member inFailed).elim

open Classical in
/-- **Failure from a completion-point law.** From a history of a site with a
pending event, if the completion-point law of the installed profile has success
one up to `error`, the failure probability from the history is at most
`error`. -/
theorem siteHistoryFailure_le_of_completionPointLaw
    (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1))
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    (history : (onePacketN).InformationHistory who site.1)
    {stepLaw : PMF (ProtocolState setup.program)} {error : ℝ}
    (pointLaw : CompletionPointLaw setup leaks bounds horizon scheduler
      (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
        ((assessment.strategy who).withLaw site.1 law))
      (siteRank site.1) (siteFresh who site.1) history.1 1 stepLaw error) :
    siteHistoryFailure setup leaks bounds horizon scheduler assessment site law history ≤
      error := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketN
  have horizonBound := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := horizonBound.wellFoundedHistories
  let installed := Profile.update (sig := (onePacketN).behavioralSignature)
    assessment.strategy who ((assessment.strategy who).withLaw site.1 law)
  let stopped := LateStopped setup leaks bounds horizon scheduler (siteRank site.1)
  obtain ⟨_, _, _, _, rankEq⟩ := pendingEvent_siteRank setup leaks bounds horizon scheduler
    pending history
  have mass := pointLaw (fun _ => 1) 1 fun _ => by norm_num
  simp only [expect_constant, mul_one] at mass
  unfold siteHistoryFailure localHistoryRun
  change expect (model.runBehavioralFrom installed (2 * horizon + 1) history.1) _ ≤ _
  rw [← model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate horizonBound,
    model.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate installed stopped,
    expect_bind_tower_bounded _ _ _ (C := 1) fun _ => by split <;> norm_num]
  have pointwise := expect_mono (μ := model.runBehavioralUntil certificate installed stopped
      history.1)
    (fun stop _ => terminalFailure_le_of_stop setup leaks bounds horizon scheduler assessment
      site law pending stop rankEq)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    expect_constant] at pointwise
  have indicatorEq : expect (model.runBehavioralUntil certificate installed stopped history.1)
      (completionIndicator setup leaks bounds horizon scheduler (siteRank site.1)
        (siteFresh who site.1)) =
      expect (model.runBehavioralUntil certificate installed stopped history.1)
        (fun stop => (completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
          (siteFresh who site.1) stop).elim 0 fun _ => 1) := rfl
  rw [indicatorEq] at pointwise
  have := (abs_le.mp mass).1
  linarith

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler] in
open Classical in
/-- Stops without a completion point have mass at most `error` under a
completion-point law with success one up to `error`. -/
private theorem noPoint_mass_le (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    {stepLaw : PMF (ProtocolState setup.program)} {error : ℝ}
    (pointLaw : CompletionPointLaw setup leaks bounds horizon scheduler
      (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
        ((assessment.strategy who).withLaw site.1 law))
      (siteRank site.1) (siteFresh who site.1) history.1 1 stepLaw error) :
    expect ((onePacketN).runBehavioralUntil
        ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories
        (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
          ((assessment.strategy who).withLaw site.1 law))
        (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) history.1)
      (fun stop => 1 - completionIndicator setup leaks bounds horizon scheduler (siteRank site.1)
        (siteFresh who site.1) stop) ≤ error := by
  have mass := pointLaw (fun _ => 1) 1 fun _ => by norm_num
  simp only [expect_constant, mul_one] at mass
  rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    expect_constant]
  have := (abs_le.mp mass).1
  unfold completionIndicator
  linarith

open Classical in
/-- **The completion value from a history with sure completion.** From a
history of a site with a pending event, if the completion-point law of the
installed profile has success one up to `error` with a step law keeping the
history's continuation value, the completion value from the history is one less
its failure probability times its continuation value, up to three times `error`
times the payoff bound. -/
theorem abs_historyStopValue_sub_le_of_sureCompletion
    (assessment : (onePacketN).BehavioralAssessment) (profile : BehavioralProfile setup.program)
    {who : Player} (site : (onePacketN).InformationSite who)
    (law : PMF ((onePacketN).Choice who site.1)) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    (history : (onePacketN).InformationHistory who site.1)
    {stepLaw : PMF (ProtocolState setup.program)} {error bound : ℝ}
    (readoutBounded : ∀ readout, |exclusionReadoutUtility setup parameter utility excludedPayoff
      readout who| ≤ bound)
    (pointLaw : CompletionPointLaw setup leaks bounds horizon scheduler
      (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
        ((assessment.strategy who).withLaw site.1 law))
      (siteRank site.1) (siteFresh who site.1) history.1 1 stepLaw error)
    (stepValue : expect stepLaw (sourcePointValue setup parameter utility excludedPayoff profile
      who) = decodedPointValue setup leaks bounds horizon scheduler parameter utility
        excludedPayoff profile who (siteRank site.1) history.1) :
    |historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site law history.1 -
      (1 - siteHistoryFailure setup leaks bounds horizon scheduler assessment site law history) *
        decodedPointValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          profile who (siteRank site.1) history.1| ≤ 3 * error * bound := by
  obtain ⟨_, _, _, _, rankEq⟩ := pendingEvent_siteRank setup leaks bounds horizon scheduler
    pending history
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans (readoutBounded none)
  have noPoint := noPoint_mass_le setup leaks bounds horizon scheduler assessment site law
    history pointLaw
  have badLaw : expect ((onePacketN).runBehavioralUntil
        ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories
        (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
          ((assessment.strategy who).withLaw site.1 law))
        (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) history.1)
      (fun stop => if completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
          (siteFresh who site.1) stop = none ∧
        ¬ ∀ final ∈ ((onePacketN).runBehavioralTerminalFrom
          ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
            scheduler).wellFoundedHistories
          (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1 law)) stop).support,
          final ∈ onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)
        then 1 else 0) ≤ error := by
    refine (expect_mono (fun stop _ => ?_) (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)).trans noPoint
    cases point : completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
        (siteFresh who site.1) stop with
    | none =>
        simp only [completionIndicator, point, Option.elim_none, sub_zero]
        split <;> norm_num
    | some target =>
        simp only [completionIndicator, point, Option.elim_some, sub_self, reduceCtorEq,
          false_and, ↓reduceIte, le_refl]
  have near := abs_historyStopValue_sub_le_of_completionPointLaw setup leaks bounds horizon
    scheduler parameter utility excludedPayoff assessment profile site law history.1 1 stepLaw
    readoutBounded pointLaw badLaw
  rw [one_mul, stepValue] at near
  have failure := siteHistoryFailure_le_of_completionPointLaw setup leaks bounds horizon
    scheduler assessment site law pending history pointLaw
  have failureNonneg : 0 ≤ siteHistoryFailure setup leaks bounds horizon scheduler assessment
      site law history :=
    expect_nonneg _ _ fun _ _ => by split <;> norm_num
  have valueBounded : |decodedPointValue setup leaks bounds horizon scheduler parameter utility
      excludedPayoff profile who (siteRank site.1) history.1| ≤ bound := by
    rw [← stepValue]
    exact expect_abs_le_of_bounded boundNonneg fun point =>
      expect_abs_le_of_bounded boundNonneg fun readout => readoutBounded readout
  have product : |siteHistoryFailure setup leaks bounds horizon scheduler assessment site law
      history * decodedPointValue setup leaks bounds horizon scheduler parameter utility
        excludedPayoff profile who (siteRank site.1) history.1| ≤ error * bound := by
    rw [abs_mul, abs_of_nonneg failureNonneg]
    exact mul_le_mul failure valueBounded (abs_nonneg _) (failureNonneg.trans failure)
  calc _ = |(historyStopValue setup leaks bounds horizon scheduler parameter utility
          excludedPayoff assessment profile site law history.1 -
          decodedPointValue setup leaks bounds horizon scheduler parameter utility
            excludedPayoff profile who (siteRank site.1) history.1) +
        siteHistoryFailure setup leaks bounds horizon scheduler assessment site law history *
          decodedPointValue setup leaks bounds horizon scheduler parameter utility
            excludedPayoff profile who (siteRank site.1) history.1| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

open Classical in
/-- **The completion value at a site with sure completion.** At a site with a
pending event, if from every history of the belief the completion-point law of
the installed profile has success one up to `error` with a step law keeping the
history's continuation value, the site's completion value is one less its
failure probability times its continuation value up to five times `error` times
the payoff bound. -/
theorem abs_siteStopValue_sub_le_of_sureCompletion
    (assessment : (onePacketN).BehavioralAssessment) (profile : BehavioralProfile setup.program)
    {who : Player} (site : (onePacketN).InformationSite who)
    (law : PMF ((onePacketN).Choice who site.1)) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event) {error bound : ℝ}
    (readoutBounded : ∀ readout, |exclusionReadoutUtility setup parameter utility excludedPayoff
      readout who| ≤ bound)
    (laws : ∀ history ∈ (assessment.belief who site).support,
      ∃ stepLaw : PMF (ProtocolState setup.program),
        CompletionPointLaw setup leaks bounds horizon scheduler
          (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1 law))
          (siteRank site.1) (siteFresh who site.1) history.1 1 stepLaw error ∧
        expect stepLaw (sourcePointValue setup parameter utility excludedPayoff profile who) =
          decodedPointValue setup leaks bounds horizon scheduler parameter utility
            excludedPayoff profile who (siteRank site.1) history.1) :
    |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site law -
      (1 - onePacketSiteFailure setup leaks bounds horizon scheduler assessment site law) *
        siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment profile site| ≤ 5 * error * bound := by
  let belief := assessment.belief who site
  let failure := siteHistoryFailure setup leaks bounds horizon scheduler assessment site law
  let value := fun history : (onePacketN).InformationHistory who site.1 =>
    decodedPointValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
      profile who (siteRank site.1) history.1
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans (readoutBounded none)
  have failureLe : ∀ history ∈ belief.support, failure history ≤ error := fun history member => by
    obtain ⟨_, pointLaw, _⟩ := laws history member
    exact siteHistoryFailure_le_of_completionPointLaw setup leaks bounds horizon scheduler
      assessment site law pending history pointLaw
  have failureNonneg : ∀ history, 0 ≤ failure history := fun history =>
    expect_nonneg _ _ fun _ _ => by split <;> norm_num
  have valueBounded : ∀ history ∈ belief.support, |value history| ≤ bound :=
    fun history member => by
      obtain ⟨stepLaw, _, stepValue⟩ := laws history member
      change |decodedPointValue setup leaks bounds horizon scheduler parameter utility
        excludedPayoff profile who (siteRank site.1) history.1| ≤ bound
      rw [← stepValue]
      exact expect_abs_le_of_bounded boundNonneg fun point =>
        expect_abs_le_of_bounded boundNonneg fun readout => readoutBounded readout
  obtain ⟨witness, witnessed⟩ := belief.support_nonempty
  have errorNonneg : 0 ≤ error := (failureNonneg witness).trans (failureLe witness witnessed)
  have historyNear : ∀ history ∈ belief.support,
      |historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment profile site law history.1 - (1 - failure history) * value history| ≤
        3 * error * bound := fun history member => by
    obtain ⟨stepLaw, pointLaw, stepValue⟩ := laws history member
    exact abs_historyStopValue_sub_le_of_sureCompletion setup leaks bounds horizon scheduler
      parameter utility excludedPayoff assessment profile site law pending history
      readoutBounded pointLaw stepValue
  -- The failure probability is at most the error, so it is uncorrelated with the value.
  have productLe : |expect belief (fun history => failure history * value history)| ≤
      error * bound := by
    have upper := expect_mono (μ := belief)
      (f := fun history => failure history * value history) (g := fun _ => error * bound)
      (fun history member => (le_abs_self _).trans (by
        rw [abs_mul, abs_of_nonneg (failureNonneg history)]
        exact mul_le_mul (failureLe history member) (valueBounded history member)
          (abs_nonneg _) errorNonneg))
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_constant _ _)
    have lower := expect_mono (μ := belief) (f := fun _ => -(error * bound))
      (g := fun history => failure history * value history)
      (fun history member => neg_le_of_abs_le (by
        rw [abs_mul, abs_of_nonneg (failureNonneg history)]
        exact mul_le_mul (failureLe history member) (valueBounded history member)
          (abs_nonneg _) errorNonneg))
      (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
    rw [expect_constant] at upper lower
    exact abs_le.mpr ⟨lower, upper⟩
  have meanFailure : 0 ≤ expect belief failure ∧ expect belief failure ≤ error :=
    ⟨expect_nonneg _ _ fun history _ => failureNonneg history,
      expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ failureLe⟩
  have meanValue : |expect belief value| ≤ bound := by
    have upper := expect_le_const belief value (payoffIntegrable_of_finite _ _) bound
      fun history member => (le_abs_self _).trans (valueBounded history member)
    have lower := expect_mono (μ := belief) (f := fun _ => -bound) (g := value)
      (fun history member => neg_le_of_abs_le (valueBounded history member))
      (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
    rw [expect_constant] at lower
    exact abs_le.mpr ⟨lower, upper⟩
  have uncorrelated : |expect belief (fun history => (1 - failure history) * value history) -
      (1 - expect belief failure) * expect belief value| ≤ 2 * error * bound := by
    have split : expect belief (fun history => (1 - failure history) * value history) =
        expect belief value - expect belief (fun history => failure history * value history) := by
      rw [← expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
      exact congrArg _ (funext fun history => by ring)
    rw [split]
    have meanProduct : |expect belief failure * expect belief value| ≤ error * bound := by
      rw [abs_mul, abs_of_nonneg meanFailure.1]
      exact mul_le_mul meanFailure.2 meanValue (abs_nonneg _) errorNonneg
    calc _ = |expect belief failure * expect belief value -
          expect belief (fun history => failure history * value history)| := by ring_nf
      _ ≤ _ := (abs_sub _ _).trans (by linarith)
  have total := abs_siteStopValue_sub_le_of_valueFree setup leaks bounds horizon scheduler
    parameter utility excludedPayoff assessment profile site law historyNear uncorrelated
  linarith

end Values

end Vegas
