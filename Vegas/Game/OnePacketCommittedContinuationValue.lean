module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketSourcePhase
public import Vegas.Game.OnePacketLocalPhaseValue
public import Vegas.Game.OnePacketPendingFailure
public import Vegas.Game.OnePacketDecodedActor
public import Vegas.Game.OnePacketCompletionPotential

@[expose] public section

/-! # Actual stopped values of intended prepared-slot commitments -/

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

local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) (initialLaw setup) horizon scheduler
local notation "Menu" => bounds.onePacketMenu timeouts leaks
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup timeouts leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

open Classical in
/-- An intended prepared-slot commitment retains its physical success factor
and its source continuation value under counted clear service. -/
theorem assembled_commitment_value_affine
    [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup timeouts leaks).Control,
      (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some
        control) →
      control.execution.application.config.defaulted = ∅ →
      OpportunityAt timeouts leaks control.execution delay)
    (inclusion : ∀ control : (application setup timeouts leaks).Control,
      (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some
        control) →
      control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt timeouts leaks control.execution bound)
    (timely : (AsyncTimely timeouts) delay bound)
    (completes : ∀ control : (application setup timeouts leaks).Control,
      (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some
        control) →
      control.execution.application.config.defaulted = ∅ →
      (application setup timeouts leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    {who : Player} (site : (N).InformationSite who)
    (choice : (N).Choice who site.1) (response : (application setup timeouts leaks).Action)
    (selected : choice.1 = some response)
    (history : (N).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup timeouts leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.logs who,
      execution.observe (application setup timeouts leaks) who))
    (member : response ∈ bounds.onePacketActions timeouts leaks who
      (execution.logs who) (execution.observe (application setup timeouts leaks) who))
    (material : (application setup timeouts leaks).Submission)
    (sends : response.transmission = some material)
    (event : (graph setup).EventId) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (pending : pendingEvent setup timeouts leaks who site.1 = some event)
    (key : LateKey setup timeouts leaks) (decided : decidedEvent (timeouts := timeouts) key = some
      event)
    {payload : L.Ty} (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {value : L.Val payload}
    (after : material.call.candidateAfter who
      (execution.observe (application setup timeouts leaks) who).application.candidates
      (.prepared serial) = .openable ⟨payload, value⟩)
    (ordered : execution.application.config.cut.IsPrefix (siteRank (timeouts := timeouts) site.1))
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank (timeouts := timeouts) site.1)
      execution.application.config =
      some point)
    (intended : ProtocolState.Intended setup.program point)
    (offered : sourceOfValue setup event outputEq value ∈
      setup.intendedMenu who (projectView setup timeouts leaks who site.1))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let certificate := (Menu).bounded (initialLaw setup) horizon scheduler
    let common := (targetSequence n).strategy
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup timeouts leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state who
    let failure := expect ((N).runBehavioralFrom
      (Profile.update (sig := (N).behavioralSignature) common who
        ((common who).withLaw site.1 (PMF.pure choice))) (2 * horizon + 1) history.1)
      (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else 0)
    |expect ((N).runBehavioralUntil certificate.wellFoundedHistories
        (Profile.update (sig := (N).behavioralSignature) common who
          ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
      (excludedPayoff who + (1 - failure) *
        (expect (ProtocolState.step setup.program point
            (fun _ => sourceOfValue setup event outputEq value))
          (sourcePointValue setup parameter utility excludedPayoff
            (setup.intendedOpeningProfile (sequence n).strategy) who) - excludedPayoff who))| ≤
      (2 * payoffBound *
        (1 - slotRetention (scale n))) *
        (2 * horizon + 1) := by
  intro bounded common stopped payoff failure
  let certificate := bounded.wellFoundedHistories
  let installed := Profile.update (sig := (N).behavioralSignature) common who
    ((common who).withLaw site.1 (PMF.pure choice))
  let phase := (N).runBehavioralUntil certificate installed
    (fun final => LateStopped setup timeouts leaks bounds horizon scheduler (siteRank
      (timeouts := timeouts) site.1)
      final ∨ ¬ Clear final.state) history.1
  let oldPhase := (N).runBehavioralUntil certificate installed
    (LateStopped setup timeouts leaks bounds horizon scheduler (siteRank (timeouts :=
      timeouts) site.1)) history.1
  let profile := setup.intendedOpeningProfile (sequence n).strategy
  let fresh := siteFresh (timeouts := timeouts) who site.1
  have pendingHere := pending
  rw [atSite] at pendingHere
  obtain ⟨turn, readyPublic, _owned, _unrecorded⟩ := pendingEvent_spec (timeouts := timeouts)
    pendingHere
  have ready := (execution.application.publicView_eventReady event).mp readyPublic
  have owned := nodeView_bind_actor outputEq codeEq
  have pointDecoded := (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have clear := defaulted_eq_empty_of_decodedIntended pointDecoded intended
  have actors : ∀ player, ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some who := fun player =>
    (decodedPoint_actor player ready pointDecoded).trans (by simp [owned, clear])
  have projected : projectView setup timeouts leaks who site.1 =
      setup.protocolObserve who (some point) := by
    rw [atSite]
    exact projectView_observe setup timeouts leaks who execution _ ordered point decoded
      (execution.logs who)
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
      intended (fun player active => ?_) reached
    cases (actors player).symm.trans active
    cases sourceCase : sourceOfValue setup event outputEq value with
    | none =>
        rw [sourceCase] at offeredAt
        exact (offeredAt (actors who)).elim
    | some sourceAction =>
        rw [sourceCase] at offeredAt
        exact ⟨sourceAction, rfl, offeredAt.2⟩
  have phaseEq : oldPhase = phase := pending_until_eq_clearUntil (timeouts := timeouts)
    certificate installed
    history.1 current ordered clear event ready
  have kernel := committed_sourceKernel (timeouts := timeouts) completes
    (targetSequence n) site decided pending choice response selected history current atSite member
    material sends packet turn ordered outputEq codeEq after decoded intended targetIntended
  obtain ⟨target, stepEq, _targetIntended, supports⟩ := kernel
  have noBad : (phase.toOuterMeasure {final |
      completionPoint setup timeouts leaks bounds horizon scheduler (siteRank (timeouts :=
        timeouts) site.1)
          fresh final = none ∧ ¬ DecisionFailed (timeouts := timeouts) key final.state}) = 0 := by
    apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
    apply Set.disjoint_left.mpr
    intro final member bad
    change completionPoint setup timeouts leaks bounds horizon scheduler (siteRank (timeouts
      := timeouts) site.1)
        (siteFresh (timeouts := timeouts) who site.1) final = none ∧ ¬ DecisionFailed (timeouts :=
          timeouts) key final.state at bad
    have oldMember : final ∈ oldPhase.support := phaseEq.symm ▸ member
    obtain ⟨other, otherState, cases⟩ := supports final oldMember
    rcases cases with completedPoint | ⟨_missing, failed⟩
    · rw [completedPoint] at bad
      cases bad.1
    · have completed : event ∈ other.execution.application.config.cut.completed := by
        apply (other.execution.application.config.output_available event).mp
        obtain ⟨value, stored, _⟩ := failed
        change (other.execution.application.config.store (.inr event)).isSome = true
        rw [stored]
        rfl
      exact bad.2 (by
        simpa only [otherState, DecisionFailed, decided, completed, true_and] using failed)
  have freshEq : fresh = fun control : (application setup timeouts leaks).Control =>
      ¬ StoreEventFailed control.execution.application.config.store event := by
    funext control
    simp only [fresh, siteFresh, pending]
  have continuation := OnePacketComparison.assembled_local_phase_value_sub_le setup timeouts leaks
    bounds horizon scheduler wellFormed covers capacity sequence scale positive le_one weights
    targetSequence assembled n opportunity
    inclusion timely completes certificate who site.1 (PMF.pure choice) history.1 current history.2
    event ready owned key decided ordered point decoded intended parameter utility excludedPayoff
    boundNonneg readoutBounded excludedBounded
  dsimp only at continuation
  rw [← freshEq, noBad, ENNReal.toReal_zero, mul_zero, add_zero] at continuation
  have potential := congrArg (expect phase) (funext (completionValue_eq_elim setup timeouts leaks
    bounds horizon scheduler parameter utility excludedPayoff profile
    (siteRank (timeouts := timeouts) site.1) fresh who (fun _ => excludedPayoff who)))
  have physical := committed_sourceValue (timeouts := timeouts) completes
    (targetSequence n) site decided pending choice response selected history current atSite member
    material sends packet turn ordered outputEq codeEq after decoded intended targetIntended
    parameter utility excludedPayoff profile
  dsimp only at physical potential
  change expect oldPhase
      (completionValue setup timeouts leaks bounds horizon scheduler parameter utility
        excludedPayoff profile (siteRank (timeouts := timeouts) site.1) fresh who (fun _ =>
          excludedPayoff who)) =
    (1 - expect oldPhase (fun final => if DecisionFailed (timeouts := timeouts) key final.state then
      (1 : ℝ) else 0)) *
      expect (ProtocolState.step setup.program point
        (fun _ => sourceOfValue setup event outputEq value))
        (sourcePointValue setup parameter utility excludedPayoff profile who) +
      expect oldPhase (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1
        : ℝ) else 0) *
        excludedPayoff who at physical
  rw [phaseEq] at physical
  rw [potential] at physical
  have failureEq := pending_failure_run_eq_phase (timeouts := timeouts) completes certificate
    installed history.1 current
    ordered clear key
    event ready decided
  change failure = expect oldPhase
      (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else 0)
        at failureEq
  rw [phaseEq] at failureEq
  have failureHere : failure = expect phase
      (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else 0) :=
        failureEq
  rw [← failureHere] at physical
  rw [physical] at continuation
  have algebra (after excluded probability : ℝ) :
      excluded + (1 - probability) * (after - excluded) =
        (1 - probability) * after + probability * excluded := by ring
  rw [algebra]
  exact continuation

end Vegas
