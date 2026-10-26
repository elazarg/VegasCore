/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryCountedValues
import Vegas.Game.RecoveryNonLateSourceValue
import Vegas.Game.RecoveryPhaseValueBlind
import Vegas.Game.RecoveryCompletionPotential

/-! # Actual stopped values of intended prepared-slot commitments -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler runtime leaks scheduler
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "Menu" => bounds.onePacketMenu runtime leaks
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))

open Classical in
/-- An intended prepared-slot commitment retains its physical success factor
and its source continuation value under counted clear service. -/
theorem nativeComparison_commitment_value_affine_of_counted_service [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
      (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).Trace (some
        control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      OpportunityAt runtime leaks control.execution delay)
    (inclusion : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).Trace (some
        control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      ProtectedInclusionAt runtime leaks control.execution bound)
    (timely : runtime.AsyncTimely delay bound)
    (completes : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).Trace (some
        control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      (application setup runtime leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    {who : Player} (site : (N).InformationSite who)
    (choice : (N).Choice who site.1) (response : (application setup runtime leaks).Action)
    (selected : choice.1 = some response)
    (history : (N).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup runtime leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.recall who,
      execution.observe (application setup runtime leaks) who))
    (member : response ∈ bounds.onePacketActions runtime leaks who
      (execution.recall who) (execution.observe (application setup runtime leaks) who))
    (material : (application setup runtime leaks).Submission)
    (sends : response.transmission = some material)
    (event : (graph setup).EventId) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (pending : pendingEvent setup runtime leaks who site.1 = some event)
    (key : LateKey setup runtime leaks) (decided : decidedEvent (runtime := runtime) key = some
      event)
    {payload : L.Ty} (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {value : L.Val payload}
    (after : material.call.candidateAfter who
      (execution.observe (application setup runtime leaks) who).application.candidates
      (.prepared serial) = .openable ⟨payload, value⟩)
    (ordered : execution.application.config.cut.IsPrefix (siteRank (runtime := runtime) site.1))
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank (runtime := runtime) site.1)
      execution.application.config =
      some point)
    (intended : ProtocolState.Intended setup.program point)
    (offered : sourceOfValue setup event outputEq value ∈
      setup.intendedMenu who (projectView setup runtime leaks who site.1))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let certificate := (Menu).bounded (initialLaw setup) horizon (NativeScheduler)
    let common := nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence
      scale
      positive le_one weights n
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
    let failure := expect ((N).runBehavioralFrom
      (Profile.update (sig := (N).behavioralSignature) common who
        ((common who).withLaw site.1 (PMF.pure choice))) (2 * horizon + 1) history.1)
      (fun final => if DecisionFailed (runtime := runtime) key final.state then (1 : ℝ) else 0)
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
    (fun final => LateStopped setup runtime leaks bounds horizon (NativeScheduler) (siteRank
      (runtime := runtime) site.1)
      final ∨ ¬ Clear final.state) history.1
  let oldPhase := (N).runBehavioralUntil certificate installed
    (LateStopped setup runtime leaks bounds horizon (NativeScheduler) (siteRank (runtime :=
      runtime) site.1)) history.1
  let profile := setup.intendedOpeningProfile (sequence n).strategy
  let fresh := siteFresh (runtime := runtime) who site.1
  have pendingHere := pending
  rw [atSite] at pendingHere
  obtain ⟨turn, readyPublic, _owned, _unrecorded⟩ := pendingEvent_spec (runtime := runtime)
    pendingHere
  have ready := (execution.application.publicView_eventReady event).mp readyPublic
  have owned := nodeView_bind_actor outputEq codeEq
  have pointDecoded := (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have actors : ∀ player, ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some who := fun player =>
    (decodedPoint_actor player ready pointDecoded).trans owned
  have projected : projectView setup runtime leaks who site.1 =
      setup.protocolObserve who (some point) := by
    rw [atSite]
    exact projectView_observe setup runtime leaks who execution _ ordered point decoded
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
      intended (fun player active => ?_) reached
    cases (actors player).symm.trans active
    cases sourceCase : sourceOfValue setup event outputEq value with
    | none =>
        rw [sourceCase] at offeredAt
        exact (offeredAt (actors who)).elim
    | some sourceAction =>
        rw [sourceCase] at offeredAt
        exact ⟨sourceAction, rfl, offeredAt.2⟩
  have clear := exclusionEvidence_of_decodedIntended (runtime := runtime)
    ((Menu).toRawTrace (initialLaw setup) horizon (NativeScheduler) (current ▸ history.1.trace))
    pointDecoded intended
  have phaseEq : oldPhase = phase := pending_until_eq_clearUntil (runtime := runtime) completes
    certificate installed
    history.1 current ordered clear event ready
  have kernel := committed_sourceKernel (runtime := runtime) completes
    (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale positive
      le_one
      weights n) site decided pending choice response selected history current atSite member
    material sends packet turn ordered outputEq codeEq after decoded intended targetIntended
  obtain ⟨target, stepEq, _targetIntended, supports⟩ := kernel
  have noBad : (phase.toOuterMeasure {final |
      completionPoint setup runtime leaks bounds horizon (NativeScheduler) (siteRank (runtime :=
        runtime) site.1)
          fresh final = none ∧ ¬ DecisionFailed (runtime := runtime) key final.state}) = 0 := by
    apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
    apply Set.disjoint_left.mpr
    intro final member bad
    change completionPoint setup runtime leaks bounds horizon (NativeScheduler) (siteRank (runtime
      := runtime) site.1)
        (siteFresh (runtime := runtime) who site.1) final = none ∧ ¬ DecisionFailed (runtime :=
          runtime) key final.state at bad
    have oldMember : final ∈ oldPhase.support := phaseEq.symm ▸ member
    obtain ⟨other, otherState, cases⟩ := supports final oldMember
    rcases cases with completedPoint | ⟨_missing, failed⟩
    · rw [completedPoint] at bad
      cases bad.1
    · obtain ⟨anchor, state, completed, _prefixed, _seen⟩ := pending_stop_completed (runtime :=
        runtime) completes true
        certificate installed history.1 current ordered clear event ready final member
      rw [state, Option.some.injEq] at otherState
      cases otherState
      exact bad.2 (by simpa only [state, DecisionFailed, decided, completed, true_and] using failed)
  have freshEq : fresh = fun control : (application setup runtime leaks).Control =>
      ¬ StoreEventFailed control.execution.application.config.store event := by
    funext control
    simp only [fresh, siteFresh, pending]
  have continuation := nativeComparison_local_phase_value_sub_le_of_counted_service setup runtime
    leaks
    bounds horizon
    scheduler wellFormed covers capacity sequence scale positive le_one weights n opportunity
    inclusion timely completes certificate who site.1 (PMF.pure choice) history.1 current history.2
    event ready owned key decided ordered point decoded intended parameter utility excludedPayoff
    boundNonneg readoutBounded excludedBounded
  dsimp only at continuation
  rw [← freshEq, noBad, ENNReal.toReal_zero, mul_zero, add_zero] at continuation
  have potential := pending_completionValue_eq_potential (runtime := runtime) completes
    certificate installed history.1
    current ordered clear event
    ready profile parameter utility excludedPayoff who fresh (fun _ => excludedPayoff who)
  have physical := committed_sourceValue (runtime := runtime) completes
    (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale positive
      le_one
      weights n) site decided pending choice response selected history current atSite member
    material sends packet turn ordered outputEq codeEq after decoded intended targetIntended
    parameter utility excludedPayoff profile
  dsimp only at physical potential
  change expect oldPhase
      (completionValue setup runtime leaks bounds horizon (NativeScheduler) parameter utility
        excludedPayoff profile (siteRank (runtime := runtime) site.1) fresh who (fun _ =>
          excludedPayoff who)) =
    (1 - expect oldPhase (fun final => if DecisionFailed (runtime := runtime) key final.state then
      (1 : ℝ) else 0)) *
      expect (ProtocolState.step setup.program point
        (fun _ => sourceOfValue setup event outputEq value))
        (sourcePointValue setup parameter utility excludedPayoff profile who) +
      expect oldPhase (fun final => if DecisionFailed (runtime := runtime) key final.state then (1
        : ℝ) else 0) *
        excludedPayoff who at physical
  rw [phaseEq] at physical
  rw [potential] at physical
  have failureEq := pending_failure_run_eq_phase (runtime := runtime) completes certificate
    installed history.1 current
    ordered clear key
    event ready decided
  change failure = expect oldPhase
      (fun final => if DecisionFailed (runtime := runtime) key final.state then (1 : ℝ) else 0)
        at failureEq
  rw [phaseEq] at failureEq
  have failureHere : failure = expect phase
      (fun final => if DecisionFailed (runtime := runtime) key final.state then (1 : ℝ) else 0) :=
        failureEq
  rw [← failureHere] at physical
  rw [physical] at continuation
  have algebra (after excluded probability : ℝ) :
      excluded + (1 - probability) * (after - excluded) =
        (1 - probability) * after + probability * excluded := by ring
  rw [algebra]
  exact continuation

open Classical in
theorem nativeComparison_commitment_value_affine [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
      (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion runtime leaks Initial horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay runtime leaks Initial horizon scheduler)
    {who : Player} (site : (N).InformationSite who)
    (choice : (N).Choice who site.1) (response : (application setup runtime leaks).Action)
    (selected : choice.1 = some response)
    (history : (N).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup runtime leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.recall who,
      execution.observe (application setup runtime leaks) who))
    (member : response ∈ bounds.onePacketActions runtime leaks who
      (execution.recall who) (execution.observe (application setup runtime leaks) who))
    (material : (application setup runtime leaks).Submission)
    (sends : response.transmission = some material)
    (event : (graph setup).EventId) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (pending : pendingEvent setup runtime leaks who site.1 = some event)
    (key : LateKey setup runtime leaks) (decided : decidedEvent (runtime := runtime) key = some
      event)
    {payload : L.Ty} (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {value : L.Val payload}
    (after : material.call.candidateAfter who
      (execution.observe (application setup runtime leaks) who).application.candidates
      (.prepared serial) = .openable ⟨payload, value⟩)
    (ordered : execution.application.config.cut.IsPrefix (siteRank (runtime := runtime) site.1))
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank (runtime := runtime) site.1)
      execution.application.config =
      some point)
    (intended : ProtocolState.Intended setup.program point)
    (offered : sourceOfValue setup event outputEq value ∈
      setup.intendedMenu who (projectView setup runtime leaks who site.1))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let certificate := (Menu).bounded (initialLaw setup) horizon (NativeScheduler)
    let common := nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence
      scale
      positive le_one weights n
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
    let failure := expect ((N).runBehavioralFrom
      (Profile.update (sig := (N).behavioralSignature) common who
        ((common who).withLaw site.1 (PMF.pure choice))) (2 * horizon + 1) history.1)
      (fun final => if DecisionFailed (runtime := runtime) key final.state then (1 : ℝ) else 0)
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
  exact nativeComparison_commitment_value_affine_of_counted_service setup runtime leaks bounds
    horizon
    scheduler wellFormed covers capacity sequence scale positive le_one weights n
    (Recovery.Opportunity.clear_counted_native (runtime := runtime) bounds (initialLaw_initialized
      setup)
      (initialLaw_native setup) opportunity)
    (Recovery.ProtectedInclusion.clear_counted_native (runtime := runtime) bounds
      (initialLaw_initialized setup)
      (initialLaw_native setup) inclusion) timely
    (Recovery.CompletesPlay.clear_counted_native (runtime := runtime) bounds
      (initialLaw_initialized setup)
      (initialLaw_native setup) completes) site choice response selected history current atSite
    member material sends event packet pending key decided outputEq codeEq after ordered
    decoded intended offered parameter utility excludedPayoff boundNonneg readoutBounded
    excludedBounded

end Vegas.RecoveryOnePacket
