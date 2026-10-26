/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryKeyedValueBounds
import Vegas.Game.RecoveryCountedValues

/-! # Keyed native value factors from counted service -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

variable {Public : Type*} {signal : State L setup.context → Public}

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "RApp" => recoveryApplication (runtime setup) leaks
local notation "RawNative" => ReactiveApplication.protocol (application setup leaks)
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks

local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)

open Classical in
theorem nativeComparison_keyed_value_sub_le_of_counted_service [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p)) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      OpportunityAt (runtime setup) leaks control.execution delay)
    (inclusion : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      ProtectedInclusionAt (runtime setup) leaks control.execution bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      (application setup leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    {who : Player} (site : (N).InformationSite who)
    (late : LateDelivery setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon (NativeScheduler) site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {unforced gamma : ℝ}
    (unforcedMass : expect ((nativeComparisonSequence setup leaks bounds horizon scheduler
      sequence scale positive le_one weights n).belief who site) (fun history =>
        if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤ unforced)
    (decorrelated : BeliefDecorrelated ((nativeComparisonSequence setup leaks bounds horizon
      scheduler sequence scale positive le_one weights n).belief who site)
      (fun history => operationalRecord setup leaks bounds horizon (NativeScheduler)
        history.1.trace)
      (fun history => nativeDecodedState setup leaks history.1.state) gamma)
    (option : LateOption bounds.candidateCount)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let target := nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n
    let common := target.strategy
    let certificate := ((NMenu).bounded (initialLaw setup) horizon
      (NativeScheduler)).wellFoundedHistories
    let law := onePacketLate setup leaks bounds horizon (NativeScheduler) sequence scale positive
      le_one n ((N).agentAt site) option
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw site.1 law)
    let stopped := fun final : (NP).History => ¬ ClearState final.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup parameter utility excludedPayoff leaks final.state who
    let error := (2 * payoffBound * (1 - slotRetention (scale n))) *
      (2 * horizon + 1) +
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound) +
      2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1))
    |expect (target.belief who site) (fun history =>
        expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff) -
      (excludedPayoff who +
        (1 - localFailure (2 * horizon + 1) target site
          {final | DecisionFailed key final.state} law) *
          (siteValue setup leaks bounds horizon (NativeScheduler) parameter utility excludedPayoff
            target (setup.intendedOpeningProfile (sequence n).strategy) site - excludedPayoff
              who))| ≤
      error + 2 * payoffBound * unforced +
      4 * payoffBound * ((2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3) + unforced) +
      4 * payoffBound * gamma := by
  apply nativeComparison_keyed_value_sub_le_of_pending setup leaks bounds horizon scheduler covers
    capacity sequence scale positive le_one weights n site late debtFree siteKey atSite
    unforcedMass decorrelated option parameter utility excludedPayoff boundNonneg readoutBounded
    excludedBounded
    (2 * payoffBound * (1 - slotRetention (scale n))) (by
      have retention := slotRetention_le_one (positive n).le (le_one n)
      positivity)
  intro history forced
  exact nativeComparison_pending_value_affine_of_counted_service setup leaks bounds horizon
    scheduler wellFormed
    covers capacity sequence scale positive le_one weights n opportunity inclusion timely completes
    site (Or.inl late) debtFree siteKey pending atSite _ history forced (Or.inl ⟨option, rfl⟩)
    parameter utility excludedPayoff boundNonneg readoutBounded excludedBounded

end Vegas.RecoveryOnePacket
