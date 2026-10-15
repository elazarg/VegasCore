/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryPrescribedSourceKernel
import Vegas.Game.RecoveryNativeComparison
import Vegas.Game.OnePacketCommitmentGain

/-! # Source continuation values of the common comparison strategy -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (MessageBounds.onePacketMenu (runtime setup) leaks bounds) (initialLaw setup) horizon
    (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))

/-- At an actual clear first callback decoding to an intended source point, the
common comparison strategy preserves source continuation value until the next
completion, with the prescribed tremble error. The same recovery pool weights
are used; no native completion or service contract is assumed. -/
theorem nativeComparison_firstActivation_sourceValue [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p))
    (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (certificate : (NP).WellFoundedHistories)
    (history : (NP).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (clear : PublicExclusionRecord (RecoveryState.mk execution.application ∅))
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (beneficiary : Player) {payoffBound : ℝ}
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout beneficiary| ≤
        payoffBound) :
    |expect ((N).runBehavioralUntil certificate
        (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive
          le_one weights n)
        (fun stop => LateStopped setup leaks bounds horizon (NativeScheduler) rank stop ∨
          ¬ Clear stop.state) history)
        (fun stop => (nativeDecodedState setup leaks stop.state).elim 0
          (sourcePointValue setup parameter utility excludedPayoff
            (setup.intendedOpeningProfile (sequence n).strategy) beneficiary)) -
      sourcePointValue setup parameter utility excludedPayoff
        (setup.intendedOpeningProfile (sequence n).strategy) beneficiary point| ≤
      6 * scale n * payoffBound := by
  classical
  have infoEq : (N).infoOf who history.trace =
      some (execution.recall who, execution.observe (application setup leaks) who) := by
    change ((bounds.onePacketMenu (runtime setup) leaks).signals (initialLaw setup) horizon
      (NativeScheduler)).infoOf who history.trace = _
    rw [ReactiveApplication.ResponseMenu.info, current]
    simp [ReactiveApplication.observe]
  have running : ¬ (NP).terminal history.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have active : (NP).active history.state who := by
    rw [current]
    rfl
  obtain ⟨site, seen⟩ := (N).exists_informationSite_of_active who history running active
  have siteEq := seen.trans infoEq
  have forced : Vegas.forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup)
      horizon (NativeScheduler) who site.1 := by
    rw [seen]
    apply forcedAgent_of_history history
    rw [current]
    exact ⟨rank, point, ordered, decoded, forcedPoint_of_intended who intendedPoint⟩
  have notFree : ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler)
      ((N).agentAt site) := fun outside => outside forced
  have first : FirstActivation setup leaks who site.1 := by
    refine ⟨execution.recall who, execution.observe (application setup leaks) who, event,
      siteEq, ?_, never⟩
    rw [siteEq]
    exact pending
  have nonlate := not_lateDelivery_of_firstActivation first
  have unkeyed : ¬ ownedKeyed (Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler))
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon (NativeScheduler))
      ((N).agentAt site) := fun keyed => nonlate keyed.1
  have prescribed := assembled_strategy_of_unpooled setup leaks bounds horizon (NativeScheduler)
    sequence scale positive le_one
    (fun index => nativeComparisonWeights setup leaks bounds horizon scheduler (weights index))
    (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive le_one
      weights)
    (nativeComparisonSequence_assembled setup leaks bounds horizon scheduler sequence scale
      positive le_one weights) n site notFree unkeyed
  change nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive
    le_one weights n who site.1 = _ at prescribed
  rw [seen] at prescribed
  have estimate := recovery_firstActivation_prescribed_sourceValue
    (initialLaw_initialized setup) (initialLaw_native setup) opportunity inclusion timely completes
    wellFormed covers capacity (sequence n) certificate
    (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive le_one
      weights n)
    history current clear event pending never ordered decoded intendedPoint _ rfl (positive n).le
    (le_one n) parameter utility excludedPayoff beneficiary readoutBounded
  rw [← prescribed, BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self] at estimate
  exact estimate

end Vegas.RecoveryOnePacket
