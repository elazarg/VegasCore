/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryLateSourcePhase
import Vegas.Game.OnePacketLateReveal

/-! # Source potentials at completed recovery phases -/

noncomputable section
namespace Vegas
open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {recoveryScheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)
local notation "scheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks)
  (initialLaw setup) horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
include initialized nativeLaw completes

open Classical in
/-- The completed-phase source potential is affine in the primitive failure
probability when all successful completions reach one source successor. -/
theorem recovery_pending_completionValue_of_stops [Finite (E).History]
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    (key : LateKey setup leaks) (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (decided : decidedEvent key = some event)
    (fresh : (application setup leaks).Control → Prop)
    (freshIff : ∀ next, fresh next ↔
      ¬ StoreEventFailed next.execution.application.config.store event)
    (target : ProtocolState setup.program)
    (stops : ∀ stop ∈ ((N).runBehavioralUntil certificate players
        (LateStopped setup leaks bounds horizon scheduler rank) start).support,
      ∃ final, stop.state = some final ∧
        (completionPoint setup leaks bounds horizon scheduler rank fresh stop = some target ∨
          (completionPoint setup leaks bounds horizon scheduler rank fresh stop = none ∧
            StoreEventFailed final.execution.application.config.store event)))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (profile : BehavioralProfile setup.program) (who : Player) :
    let phase := (N).runBehavioralUntil certificate players
      (LateStopped setup leaks bounds horizon scheduler rank) start
    expect phase (completionValue setup leaks bounds horizon scheduler parameter utility
      excludedPayoff profile rank fresh who (fun _ => excludedPayoff who)) =
      (1 - expect phase (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0)) *
        sourcePointValue setup parameter utility excludedPayoff profile who target +
      expect phase (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) *
        excludedPayoff who := by
  intro phase
  let targetValue := sourcePointValue setup parameter utility excludedPayoff profile who target
  let failure := fun final : (E).History =>
    if DecisionFailed key final.state then (1 : ℝ) else 0
  have pointwise : ∀ final ∈ phase.support,
      completionValue setup leaks bounds horizon scheduler parameter utility excludedPayoff profile
          rank fresh who (fun _ => excludedPayoff who) final =
        (1 - failure final) * targetValue + failure final * excludedPayoff who := by
    intro final supported
    obtain ⟨anchor, state, completed, prefixed, _seen⟩ :=
      recovery_pending_stop_completed initialized nativeLaw completes false
        certificate players start current ordered clear event ready final supported
    rw [completionValue_eq_elim setup leaks bounds horizon scheduler parameter utility
      excludedPayoff
      profile rank fresh who (fun _ => excludedPayoff who)
      ⟨_, state, prefixed⟩]
    obtain ⟨other, otherState, cases⟩ := stops final supported
    have same : other = ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ :=
      Option.some.inj (otherState.symm.trans state)
    subst other
    rcases cases with pointEq | ⟨pointEq, failed⟩
    · have good : ¬ DecisionFailed key final.state := by
        intro failed
        have stored : StoreEventFailed anchor.application.config.store event := by
          simpa only [DecisionFailed, state, decided, completed, true_and] using failed
        have absent := completionPoint_eq_none_of_not_fresh (rank := rank)
          (fresh := fresh) state
          (fun fresh => (freshIff _).mp fresh stored)
        rw [pointEq] at absent
        cases absent
      simp only [pointEq, Option.elim_some, failure, good, ↓reduceIte, sub_zero, one_mul,
        zero_mul, add_zero, targetValue]
    · have failedHere : DecisionFailed key final.state := by
        simpa only [DecisionFailed, state, decided, completed, true_and] using failed
      simp only [pointEq, Option.elim_none, failure, failedHere, ↓reduceIte, sub_self, zero_mul,
        one_mul, zero_add]
  rw [expect_congr_on_support pointwise,
    expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    expect_mul_const, expect_mul_const,
    expect_sub (payoffIntegrable_constant _ 1) (payoffIntegrable_of_finite _ _), expect_constant]

open Classical in
/-- A disclosure phase has the current source continuation value whenever its
publication succeeds, and the exclusion payoff otherwise. -/
theorem recovery_disclosure_sourceValue
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)]
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).History]
    (source : setup.intendedModel.BehavioralAssessment)
    (assessment : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralAssessment) {who : Player}
    (site : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InformationSite who)
    {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    (law : PMF ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).Choice who site.1))
    (history : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (ordered : execution.application.config.cut.IsPrefix (siteRank site.1))
    {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank site.1) execution.application.config =
      some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    {key : LateKey setup leaks} (decided : decidedEvent key = some event)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound) :
    let profile := setup.intendedOpeningProfile source.strategy
    let installed := Profile.update (sig := (N).behavioralSignature) assessment.strategy who
      ((assessment.strategy who).withLaw site.1 law)
    let phase := (N).runBehavioralUntil ((bounds.onePacketMenu (runtime setup) leaks).bounded
      (initialLaw setup) horizon scheduler).wellFoundedHistories installed
      (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) history.1
    expect phase (completionValue setup leaks bounds horizon scheduler parameter utility
      excludedPayoff profile (siteRank site.1) (siteFresh who site.1) who
      (fun _ => excludedPayoff who)) =
      (1 - expect phase (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0)) *
        sourcePointValue setup parameter utility excludedPayoff profile who point +
      expect phase (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) *
        excludedPayoff who := by
  intro profile installed phase
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  obtain ⟨target, stepPure, _intended, stops⟩ := disclosure_sourceKernel source
    assessment site pending law history current turn ordered outputEq codeEq decoded intendedPoint
    (recovery_terminal_completed_of_decodedIntended initialized nativeLaw completes ordered
      decoded intendedPoint event)
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  have trace := menu.toRawTrace (initialLaw setup) horizon scheduler (current ▸ history.1.trace)
  have clear := exclusionEvidence_of_decodedIntended trace
    ((decodedPoint_eq_of_isPrefix ordered).trans decoded) intendedPoint
  have freshIff : ∀ control, siteFresh who site.1 control ↔
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [siteFresh, pending]
  have affine := recovery_pending_completionValue_of_stops initialized nativeLaw completes
    certificate installed history.1 current ordered clear key event ready decided
    (siteFresh who site.1) freshIff target stops parameter utility excludedPayoff profile who
  have targetValue : sourcePointValue setup parameter utility excludedPayoff profile who target =
      sourcePointValue setup parameter utility excludedPayoff profile who point := by
    rw [← expect_pure target (sourcePointValue setup parameter utility excludedPayoff profile who),
      ← stepPure, expect_sourcePointValue_behavioralStateStep setup parameter utility
        excludedPayoff profile who readoutBounded point]
  rw [targetValue] at affine
  exact affine

end Vegas
