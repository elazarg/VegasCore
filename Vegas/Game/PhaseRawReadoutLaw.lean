/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseExclusionPayoff
import Vegas.Game.PhaseOnePacketExtension

/-! # Exact typed readout and realized audited payoff laws of phased raw extensions -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

local notation "app" => phaseApplication runtime leaks

open Classical in
/-- The actual count-audit extension preserves the full typed terminal-store
readout jointly with the realized payoff vector. The scheduler is arbitrary;
only evidence coverage and the deposit spread bound enter enforcement. -/
theorem phase_counted_raw_sequentialEquilibrium
    (bounds : MessageBounds (serviceGraph setup mode)) (initial : PMF (app).State)
    (horizon : Nat) (scheduler : (app).Scheduler) [(app).FiniteNature initial scheduler]
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ terminal who, lowerUtility who ≤ utility terminal who)
    (le_upper : ∀ terminal who, utility terminal who ≤ upperUtility who)
    (service : EvidenceReportService (PhaseCount.Evidence (serviceGraph setup mode)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : PhaseCount.EvidenceCoverage service observationRate deliveryRate)
    (deposit : Player → ℝ) (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      max 0 (max (excludedPayoff who) (upperUtility who)) -
          min 0 (min (excludedPayoff who) (lowerUtility who)) ≤
        observationRate who * deliveryRate who * deposit who) :
    let counted := PhaseCount.onePacketMenu runtime leaks bounds
    let raw := PhaseCount.rawMenu runtime leaks bounds
    let restriction :=
      PhaseCount.onePacketRestriction runtime leaks bounds initial horizon scheduler
    let sourceCertificate := (counted.bounded initial horizon scheduler).wellFoundedHistories
    let targetCertificate := (raw.bounded initial horizon scheduler).wellFoundedHistories
    let observe := (app).stateTraffic
    let audit := PhaseCount.audit runtime leaks service.sample
    let base := phaseExclusionBase setup mode runtime leaks utility excludedPayoff
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∀ source : (counted.information initial horizon scheduler).BehavioralAssessment,
      source.IsSequentialEquilibrium
        (counted.decisionInformationAntichain initial horizon scheduler) sourceCertificate
        (fun who final => base final.state who) →
      ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
        target.IsSequentialEquilibrium
          (raw.decisionInformationAntichain initial horizon scheduler) targetCertificate
          (fun who final => payoff final.state who) ∧
        restriction.ExtendsProfile source.strategy target.strategy ∧
        (∀ who site, target.belief who (restriction.site who site) =
          (source.belief who site).map (restriction.informationHistory who site)) ∧
        ((counted.information initial horizon scheduler).runBehavioralTerminalFrom
          sourceCertificate source.strategy
            (counted.protocol initial horizon scheduler).initHistory).map
            (fun final => (phaseSourceReadout setup mode runtime leaks final.state,
              base final.state)) =
          ((raw.information initial horizon scheduler).runBehavioralTerminalFrom
            targetCertificate target.strategy
              (raw.protocol initial horizon scheduler).initHistory).bind
              (fun final => (settle final.state).map fun payoffs =>
                (phaseSourceReadout setup mode runtime leaks final.state, payoffs)) ∧
        ∀ final ∈ ((raw.information initial horizon scheduler).runBehavioralTerminalFrom
          targetCertificate target.strategy
            (raw.protocol initial horizon scheduler).initHistory).support,
          ∀ who, TerminalAudit.charge observe audit final.state who = 0 := by
  intro counted raw restriction sourceCertificate targetCertificate observe audit base payoff
    settle source equilibrium
  have lowerBound (state : (app).ProtocolState) (who : Player) :
      min 0 (min (excludedPayoff who) (lowerUtility who)) ≤ base state who :=
    (phaseExclusionBase_mem_Icc setup mode runtime leaks utility excludedPayoff
      lowerUtility upperUtility lower_le le_upper state who).1
  have upperBound (state : (app).ProtocolState) (who : Player) :
      base state who ≤ max 0 (max (excludedPayoff who) (upperUtility who)) :=
    (phaseExclusionBase_mem_Icc setup mode runtime leaks utility excludedPayoff
      lowerUtility upperUtility lower_le le_upper state who).2
  obtain ⟨target, sequential, agrees, beliefs, _historyLaw, jointLaw, clean⟩ :=
    PhaseCount.onePacket_raw_sequentialEquilibrium runtime leaks bounds initial horizon scheduler
      service observationRate deliveryRate delivery_nonnegative coverage base
      (fun who => min 0 (min (excludedPayoff who) (lowerUtility who)))
      (fun who => max 0 (max (excludedPayoff who) (upperUtility who))) deposit
      lowerBound upperBound deposit_nonnegative sufficient source equilibrium
  refine ⟨target, sequential, agrees, beliefs, ?_, clean⟩
  have projected := congrArg (PMF.map fun pair :
      (raw.protocol initial horizon scheduler).History × (Player → ℝ) =>
        (phaseSourceReadout setup mode runtime leaks pair.1.state, pair.2)) jointLaw
  have sameState (history : (counted.protocol initial horizon scheduler).History) :
      ((PhaseCount.onePacketRestriction runtime leaks bounds initial horizon scheduler).history
        history).state = history.state := rfl
  simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, sameState] using projected

end Vegas
