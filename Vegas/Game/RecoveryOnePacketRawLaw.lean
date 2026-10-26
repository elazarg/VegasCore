/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryOnePacketExtension
import Vegas.Game.RecoveryExclusionPayoff
import Vegas.Pending.ExclusionPrefix
import Vegas.Game.OnePacketLawApproximation

/-! # Intended joint laws through the audited raw recovery extension -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {initial : PMF (RecoveryState (graph setup))}
  {scheduler : (recoveryApplication runtime leaks).Scheduler}
  [(recoveryApplication runtime leaks).FiniteNature initial scheduler]

local notation "menu" => Recovery.onePacketMenu runtime leaks bounds
local notation "raw" => Recovery.rawMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (Recovery.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "R" => ReactiveApplication.ResponseMenu.information
  (Recovery.rawMenu runtime leaks bounds) initial horizon scheduler

/-- The checked audited raw extension preserves an intended joint law of a
recovery one-packet equilibrium, with zero charges, its complete normalized
state law, and actual settled payoffs. -/
theorem recovery_intended_raw_sequentialEquilibrium_of_onePacket {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (source : setup.intendedModel.BehavioralAssessment)
    (native : (N).BehavioralAssessment)
    (equilibrium : native.IsSequentialEquilibriumFor
      ((menu).decisionInformationAntichain initial horizon scheduler)
      (fun who site => native.truncatedContinuationContext site
        (fun final => recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff
          final.state who)
        (2 * horizon + 1)))
    (law : ((N).runBehavioral native.strategy (2 * horizon + 1)).map (fun final =>
        (sourceReadout setup runtime leaks (RecoveryProjection.protocolState runtime leaks
          final.state), recoveryExclusionBase (runtime := runtime) parameter utility
            excludedPayoff final.state)) =
      (setup.intendedModel.runBehavioral source.strategy
        (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff))
    (service : EvidenceReportService (CountEvidence (graph setup)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (deposit : Player → ℝ) (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      max 0 (max (excludedPayoff who) (upperUtility who)) -
          min 0 (min (excludedPayoff who) (lowerUtility who)) ≤
        observationRate who * deliveryRate who * deposit who) :
    let observe := (recoveryApplication runtime leaks).stateTraffic
    let audit := Recovery.countAudit runtime leaks service.sample
    let base := recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∃ target : (R).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((raw).decisionInformationAntichain initial horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => payoff history.state who) (2 * horizon + 1)) ∧
      (∀ final ∈ ((R).runBehavioral target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((R).runBehavioral target.strategy (2 * horizon + 1)).map (fun final =>
        (Recovery.normalization runtime leaks).state final.state) =
          ((N).runBehavioral native.strategy (2 * horizon + 1)).map History.state ∧
      ((R).runBehavioral target.strategy (2 * horizon + 1)).bind
        (fun final => (settle final.state).map fun payoffs =>
          (sourceReadout setup runtime leaks (RecoveryProjection.protocolState runtime leaks
            final.state), payoffs)) =
        (setup.intendedModel.runBehavioral source.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  intro observe audit base payoff settle
  have nativeSE := (native.isSequentialEquilibrium_iff_truncated_of_bounded (N)
    ((menu).decisionInformationAntichain initial horizon scheduler)
    ((menu).bounded initial horizon scheduler).wellFoundedHistories
    ((menu).bounded initial horizon scheduler)
    (fun who final => base final.state who)).mpr equilibrium
  obtain ⟨target, targetSE, clean, states, joint⟩ :=
    Recovery.onePacket_raw_sequentialEquilibrium runtime leaks bounds initial horizon
      scheduler service observationRate deliveryRate delivery_nonnegative coverage base
      (recoveryExclusionBase_normalization (runtime := runtime) parameter utility excludedPayoff)
      (fun who => min 0 (min (excludedPayoff who) (lowerUtility who)))
      (fun who => max 0 (max (excludedPayoff who) (upperUtility who))) deposit
      (fun state who => (recoveryExclusionBase_mem_Icc (runtime := runtime) parameter utility
        excludedPayoff
        lowerUtility upperUtility lower_le le_upper state who).1)
      (fun state who => (recoveryExclusionBase_mem_Icc (runtime := runtime) parameter utility
        excludedPayoff
        lowerUtility upperUtility lower_le le_upper state who).2)
      deposit_nonnegative sufficient native nativeSE
  refine ⟨target, targetSE, clean, states, ?_⟩
  let read := fun state : (recoveryApplication runtime leaks).ProtocolState =>
    sourceReadout setup runtime leaks (RecoveryProjection.protocolState runtime leaks state)
  have normalized (state : (recoveryApplication runtime leaks).ProtocolState) :
      read ((Recovery.normalization runtime leaks).state state) = read state := by
    cases state <;> rfl
  have pairs := congrArg (PMF.map (Prod.map read id)) joint
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Prod.map_apply, id_eq,
    normalized] at pairs
  rw [pairs, ← law]

end Vegas
