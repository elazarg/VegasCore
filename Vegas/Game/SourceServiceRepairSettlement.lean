/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAudit
import Vegas.Game.BindingRepairReadout
import Vegas.Game.ServicePayoffBounds
import GameTheoryExtensions.Analysis.Protocol.TerminalAuditCoupling

/-! # Actual settlement comparison from full-source continuation repair

The operational coupling may preserve the initial types and public result,
exhibit forbidden signed traffic, or certify a public binding omission. Its
repaired marginal must consist of actual permitted traces. Authentic partial
sampling then gives zero repaired charge and the stated incremental collection
bound. A sufficient deposit compares the realized settlements without assuming
any independence between payoffs, evidence, and detection.

Constructing this coupling for every native continuation remains a separate
operational obligation. Private binding values changed by repair are not part
of the utility readout.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem sourceService_repair_settlement_le {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ∀ event owner payload,
      (graph setup).outputLayout event = .binding owner payload → owner ∈ rosters event)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (sample : List (EnvelopeEvidence setup leaks) →
      FinDist (List (EnvelopeEvidence setup leaks)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (who : Player) (rate gap : ℝ) (deposit : Player → ℝ)
    (coverage : ∀ actual record, record ∈ actual → record.2.2.sender = who →
      (runtime setup).permittedServiceEnvelope record.1 record.2.1 record.2.2 = false →
      rate ≤ (sample actual).probOf {observed | record ∈ observed})
    (nonnegative : 0 ≤ deposit who) (sufficient : gap ≤ min rate 1 * deposit who)
    (coupled : FinDist ((application setup leaks).Control ×
      (application setup leaks).Control × BindingMemory (runtime setup) leaks))
    (permitted : ∀ pair ∈ coupled.support,
      Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
          (some pair.2.1)))
    (onlyBindings : ∀ pair ∈ coupled.support, pair.2.2.shadow.OwnBindings who)
    (related : ∀ pair ∈ coupled.support,
      (∃ record ∈ (application setup leaks).executionTraffic pair.1.execution,
        record.input.envelope.sender = who ∧
        (runtime setup).permittedServiceEnvelope record.observation record.ledger
          record.input.envelope = false) ∨
      pair.1.execution.application.publicView.missedBindingBy who = true ∨
      pair.2.2.Frame (runtime setup) leaks who pair.1.execution pair.2.1.execution)
    (bounded : ∀ pair ∈ coupled.support,
      baseUtility setup leaks (fun state => utility (setup.parameterOutcome parameter state))
          (some pair.1) who ≤
        baseUtility setup leaks (fun state => utility (setup.parameterOutcome parameter state))
          (some pair.2.1) who + gap) :
    let settle := TerminalAudit.settlement
      (baseUtility setup leaks (fun state => utility (setup.parameterOutcome parameter state)))
      ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
      deposit
    ((coupled.map (fun pair => some pair.1)).bind settle).expect (fun payoffs => payoffs who) ≤
      ((coupled.map (fun pair => some pair.2.1)).bind settle).expect
        (fun payoffs => payoffs who) := by
  classical
  intro settle
  let observe := (runtime setup).serviceAuditObservation leaks
  let audit := sourceServiceAudit setup leaks sample
  let departed : Set ((application setup leaks).Control ×
      (application setup leaks).Control × BindingMemory (runtime setup) leaks) :=
    {pair | ¬ BindingMemory.Frame (runtime setup) leaks pair.2.2 who
      pair.1.execution pair.2.1.execution}
  have clean (pair) (supported : pair ∈ coupled.support) :
      TerminalAudit.charge observe audit (some pair.2.1) who = 0 := by
    obtain ⟨trace⟩ := permitted pair supported
    exact sourceService_history_audit_clear setup leaks bounds values capacity rosters
      opportunities network profile sample authentic ⟨some pair.2.1, trace⟩ who
  have collected (pair) (supported : pair ∈ coupled.support) (bad : pair ∈ departed) :
      min rate 1 ≤ TerminalAudit.charge observe audit (some pair.1) who := by
    rcases related pair supported with traffic | missing | framed
    · obtain ⟨record, present, author, forbidden⟩ := traffic
      have lower := (runtime setup).serviceAudit_collection_from_record leaks
        (envelopeEvidence setup leaks) (fun evidence => evidence.2.2.sender)
        (fun evidence => (runtime setup).permittedServiceEnvelope
          evidence.1 evidence.2.1 evidence.2.2) sample
        (FinDist.pure (some pair.1)) who rate coverage record
        (by
          intro state supported
          cases FinDist.mem_support_pure.mp supported
          exact present) author forbidden
      have lowerCharge : rate ≤ TerminalAudit.charge observe audit (some pair.1) who := by
        simpa only [FinDist.map_pure, FinDist.pure_bind, TerminalAudit.charge, observe, audit,
          sourceServiceAudit] using lower
      exact (min_le_left _ _).trans lowerCharge
    · change min rate 1 ≤ TerminalAudit.charge
        ((runtime setup).serviceAuditObservation leaks)
        ((runtime setup).serviceAudit leaks _) (some pair.1) who
      rw [(runtime setup).serviceAudit_charge]
      simpa only [Option.elim_some, missing, ↓reduceIte] using min_le_right rate (1 : ℝ)
    · exact (bad framed).elim
  have incremental : coupled.probOf departed * min rate 1 ≤
      (coupled.map (fun pair => some pair.1)).expect
          (fun state => TerminalAudit.charge observe audit state who) -
        (coupled.map (fun pair => some pair.2.1)).expect
          (fun state => TerminalAudit.charge observe audit state who) := by
    have zero : (coupled.map (fun pair => some pair.2.1)).expect
        (fun state => TerminalAudit.charge observe audit state who) = 0 := by
      rw [FinDist.expect_map]
      calc
        _ = coupled.expect (fun _ => (0 : ℝ)) := FinDist.expect_congr clean
        _ = 0 := FinDist.expect_const _ _
    rw [zero, sub_zero, FinDist.expect_map]
    calc
      _ = coupled.expect (fun pair => (if pair ∈ departed then 1 else 0) * min rate 1) := by
        rw [FinDist.expect_mul_const, FinDist.expect_indicator_eq_probOf]
      _ ≤ _ := by
        apply FinDist.expect_mono
        intro pair supported
        by_cases bad : pair ∈ departed
        · simpa only [bad, ite_true, one_mul] using collected pair supported bad
        · simp only [bad, ite_false, zero_mul]
          exact FinDist.prob_nonneg _ _
  apply TerminalAudit.settlement_le_of_departure_coupling coupled
    (fun pair => some pair.1) (fun pair => some pair.2.1) _ observe audit deposit who departed
      gap (min rate 1) _ _ incremental nonnegative sufficient
  · intro pair supported notDeparted
    have framed := Classical.not_not.mp notDeparted
    exact le_of_eq (congrFun (bindingFrame_baseUtility setup leaks parameter utility who
      pair.2.2 pair.1 pair.2.1 framed (onlyBindings pair supported)) who)
  · intro pair supported _bad
    exact bounded pair supported

/-- The native game's finite payoff range supplies the deposit before any
equilibrium or deviating policy is chosen. Both sides must be actual histories;
no arbitrary payoff-gap premise remains. The coupling is still an operational
obligation, and the positive rate is still a collection-service assumption. -/
theorem sourceService_repair_range_settlement_le {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ∀ event owner payload,
      (graph setup).outputLayout event = .binding owner payload → owner ∈ rosters event)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (sample : List (EnvelopeEvidence setup leaks) →
      FinDist (List (EnvelopeEvidence setup leaks)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (who : Player) (probability : Player → ℝ) (positive : 0 < probability who)
    (coverage : ∀ actual record, record ∈ actual → record.2.2.sender = who →
      (runtime setup).permittedServiceEnvelope record.1 record.2.1 record.2.2 = false →
      probability who ≤ (sample actual).probOf {observed | record ∈ observed})
    (coupled : FinDist ((application setup leaks).Control ×
      (application setup leaks).Control × BindingMemory (runtime setup) leaks))
    (realized : ∀ pair ∈ coupled.support,
      Nonempty (((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
          (some pair.1)))
    (permitted : ∀ pair ∈ coupled.support,
      Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
          (some pair.2.1)))
    (onlyBindings : ∀ pair ∈ coupled.support, pair.2.2.shadow.OwnBindings who)
    (related : ∀ pair ∈ coupled.support,
      (∃ record ∈ (application setup leaks).executionTraffic pair.1.execution,
        record.input.envelope.sender = who ∧
        (runtime setup).permittedServiceEnvelope record.observation record.ledger
          record.input.envelope = false) ∨
      pair.1.execution.application.publicView.missedBindingBy who = true ∨
      pair.2.2.Frame (runtime setup) leaks who pair.1.execution pair.2.1.execution) :
    let base := baseUtility setup leaks
      (fun state => utility (setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit setup leaks bounds rosters network base
      (fun owner => min (probability owner) 1)
    let settle := TerminalAudit.settlement base ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit
    ((coupled.map (fun pair => some pair.1)).bind settle).expect (fun payoffs => payoffs who) ≤
      ((coupled.map (fun pair => some pair.2.1)).bind settle).expect
        (fun payoffs => payoffs who) := by
  intro base deposit settle
  have ratePositive : 0 < min (probability who) 1 := lt_min positive zero_lt_one
  apply sourceService_repair_settlement_le setup leaks bounds values capacity rosters
    opportunities network profile parameter utility sample authentic who (probability who)
    (min (probability who) 1 * deposit who) deposit coverage
    (rosterAuditDeposit_nonnegative setup leaks bounds rosters network base _ who ratePositive)
    (le_refl _) coupled permitted onlyBindings related
  intro pair supported
  obtain ⟨originalTrace⟩ := realized pair supported
  obtain ⟨repairedTrace⟩ := permitted pair supported
  let originalHistory : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History :=
    ⟨some pair.1, originalTrace⟩
  let repairedHistory := (sourceServiceMenu_in_effective setup leaks bounds rosters).history
    (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) ⟨some pair.2.1, repairedTrace⟩
  exact rosterAuditDeposit_covers_gain setup leaks bounds rosters network base
    (fun owner => min (probability owner) 1) who ratePositive originalHistory repairedHistory

end Vegas.SourceProgram.RevealService
