/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateReveal
import Vegas.Game.OnePacketLateLumping

/-! # Source potentials at completed native events -/

noncomputable section
namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)

local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (MessageBounds.onePacketMenu timeouts leaks bounds)
  (initialLaw setup) horizon scheduler

open Classical in
/-- Any law supported on completed native configurations has an affine source
potential when its successful outcomes share one source continuation point. -/
theorem completionValue_expect_affine_of_completed [Finite (E).History]
    (law : PMF (E).History) (rank : Nat)
    (key : LateKey setup timeouts leaks) (event : (graph setup).EventId)
    (decided : decidedEvent (timeouts := timeouts) key = some event)
    (fresh : (application setup timeouts leaks).Control → Prop)
    (freshIff : ∀ next, fresh next ↔
      ¬ StoreEventFailed next.execution.application.config.store event)
    (target : ProtocolState setup.program)
    (completed : ∀ stop ∈ law.support,
      ∃ control : (application setup timeouts leaks).Control, stop.state = some control ∧
        event ∈ control.execution.application.config.cut.completed)
    (stops : ∀ stop ∈ law.support,
      ∃ final, stop.state = some final ∧
        (completionPoint setup timeouts leaks bounds horizon scheduler rank fresh stop = some
          target ∨
          (completionPoint setup timeouts leaks bounds horizon scheduler rank fresh stop = none ∧
            StoreEventFailed final.execution.application.config.store event)))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (profile : BehavioralProfile setup.program) (who : Player) :
    expect law (completionValue setup timeouts leaks bounds horizon scheduler parameter utility
      excludedPayoff profile rank fresh who (fun _ => excludedPayoff who)) =
      (1 - expect law (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1
        : ℝ) else 0)) *
        sourcePointValue setup parameter utility excludedPayoff profile who target +
      expect law (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ)
        else 0) *
        excludedPayoff who := by
  let targetValue := sourcePointValue setup parameter utility excludedPayoff profile who target
  let failure := fun final : (E).History =>
    if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else 0
  have pointwise : ∀ final ∈ law.support,
      completionValue setup timeouts leaks bounds horizon scheduler parameter utility
        excludedPayoff profile
          rank fresh who (fun _ => excludedPayoff who) final =
        (1 - failure final) * targetValue + failure final * excludedPayoff who := by
    intro final supported
    obtain ⟨anchor, state, eventCompleted⟩ := completed final supported
    rw [completionValue_eq_elim setup timeouts leaks bounds horizon scheduler parameter utility
      excludedPayoff profile rank fresh who (fun _ => excludedPayoff who) final]
    obtain ⟨other, otherState, cases⟩ := stops final supported
    have same : other = anchor := Option.some.inj (otherState.symm.trans state)
    subst other
    rcases cases with pointEq | ⟨pointEq, failed⟩
    · have good : ¬ DecisionFailed (timeouts := timeouts) key final.state := by
        intro failed
        have stored : StoreEventFailed anchor.execution.application.config.store event := by
          simpa only [DecisionFailed, state, decided, eventCompleted, true_and] using failed
        have absent := completionPoint_eq_none_of_not_fresh (timeouts := timeouts) (rank := rank)
          (fresh := fresh) state (fun fresh => (freshIff _).mp fresh stored)
        rw [pointEq] at absent
        cases absent
      simp only [pointEq, Option.elim_some, failure, good, ↓reduceIte, sub_zero, one_mul,
        zero_mul, add_zero, targetValue]
    · have failedHere : DecisionFailed (timeouts := timeouts) key final.state := by
        simpa only [DecisionFailed, state, decided, eventCompleted, true_and] using failed
      simp only [pointEq, Option.elim_none, failure, failedHere, ↓reduceIte, sub_self, zero_mul,
        one_mul, zero_add]
  rw [expect_congr_on_support pointwise,
    expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    expect_mul_const, expect_mul_const,
    expect_sub (payoffIntegrable_constant _ 1) (payoffIntegrable_of_finite _ _), expect_constant]


local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler

open Classical in
/-- Successful disclosure completions preserve their current source continuation
value under counted clear terminal completeness. -/
theorem disclosure_sourceValue
    [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)]
    [Finite ((bounds.onePacketMenu timeouts leaks).protocol
      (initialLaw setup) horizon scheduler).History]
    (terminalCompletes : ∀ (final : (application setup timeouts leaks).Control),
      ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      final.execution.application.config.defaulted = ∅ →
      (application setup timeouts leaks).terminal (some final) →
      final.execution.application.config.cut.Terminal)
    (source : setup.intendedModel.BehavioralAssessment)
    (assessment : (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralAssessment) {who : Player}
    (site : (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).InformationSite who)
    {event : (graph setup).EventId}
    (pending : pendingEvent setup timeouts leaks who site.1 = some event)
    (law : PMF ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).Choice who site.1))
    (history : (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup timeouts leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (ordered : execution.application.config.cut.IsPrefix (siteRank (timeouts := timeouts) site.1))
    {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank (timeouts := timeouts) site.1)
      execution.application.config =
      some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    {key : LateKey setup timeouts leaks} (decided : decidedEvent (timeouts := timeouts) key = some
      event)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound) :
    let profile := setup.intendedOpeningProfile source.strategy
    let installed := Profile.update (sig := (N).behavioralSignature) assessment.strategy who
      ((assessment.strategy who).withLaw site.1 law)
    let phase := (N).runBehavioralUntil ((bounds.onePacketMenu timeouts leaks).bounded
      (initialLaw setup) horizon scheduler).wellFoundedHistories installed
      (LateStopped setup timeouts leaks bounds horizon scheduler (siteRank (timeouts := timeouts)
        site.1)) history.1
    expect phase (completionValue setup timeouts leaks bounds horizon scheduler parameter utility
      excludedPayoff profile (siteRank (timeouts := timeouts) site.1) (siteFresh (timeouts :=
        timeouts) who site.1) who
      (fun _ => excludedPayoff who)) =
      (1 - expect phase (fun final => if DecisionFailed (timeouts := timeouts) key final.state then
        (1 : ℝ) else 0)) *
        sourcePointValue setup parameter utility excludedPayoff profile who point +
      expect phase (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 :
        ℝ) else 0) *
        excludedPayoff who := by
  intro profile installed phase
  let menu := bounds.onePacketMenu timeouts leaks
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  obtain ⟨target, stepPure, _intended, stops⟩ := disclosure_sourceKernel (timeouts := timeouts)
    source
    assessment site pending law history current turn ordered outputEq codeEq decoded intendedPoint
    (fun final trace ended same => by
      have finalDecoded : decodedPoint setup final.execution.application.config = some point := by
        rw [decodedPoint_eq_of_isPrefix (show
          final.execution.application.config.cut.IsPrefix (siteRank (timeouts := timeouts)
            site.1) by
            rw [same]; exact ordered), same]
        exact decoded
      have clear := defaulted_eq_empty_of_decodedIntended finalDecoded intendedPoint
      rw [terminalCompletes final trace clear ended]
      exact Finset.mem_univ _)
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  have freshIff : ∀ control, siteFresh (timeouts := timeouts) who site.1 control ↔
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [siteFresh, pending]
  have affine := completionValue_expect_affine_of_completed setup timeouts leaks bounds horizon
    scheduler
    phase (siteRank (timeouts := timeouts) site.1) key event decided (siteFresh (timeouts :=
      timeouts)
      who site.1) freshIff target
    (fun final supported => by
      obtain ⟨anchor, state, action, primary, sampled, drained⟩ :=
        lateStop_primary_drain (timeouts := timeouts) certificate installed ordered ready
          (fun last trace ended same => by
            have lastDecoded : decodedPoint setup last.execution.application.config =
                some point := by
              rw [same]
              exact (decodedPoint_eq_of_isPrefix ordered).trans decoded
            have clear := defaulted_eq_empty_of_decodedIntended lastDecoded intendedPoint
            rw [terminalCompletes last trace clear ended]
            exact Finset.mem_univ _) history.1 current rfl final supported
      refine ⟨anchor, state, ?_⟩
      rw [drained]
      apply EventGraph.Config.Step.path_completed_mono primary.drain_graph_steps
      rw [execution.application.config.step_cut event ready action primary.config sampled]
      exact (EventOrder.Cut.mem_complete _ event ready event).mpr (Or.inl rfl))
    stops parameter utility excludedPayoff profile who
  have targetValue : sourcePointValue setup parameter utility excludedPayoff profile who target =
      sourcePointValue setup parameter utility excludedPayoff profile who point := by
    rw [← expect_pure target (sourcePointValue setup parameter utility excludedPayoff profile who),
      ← stepPure, expect_sourcePointValue_behavioralStateStep setup parameter utility
        excludedPayoff profile who readoutBounded point]
  rw [targetValue] at affine
  exact affine


end Vegas
