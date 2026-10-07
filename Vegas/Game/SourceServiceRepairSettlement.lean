/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAudit
import Vegas.Game.ServiceSettledEvidence
import Vegas.Game.BindingRepairReadout
import Vegas.Game.ServicePayoffBounds
import GameTheoryExtensions.Analysis.Protocol.TerminalAuditCoupling

/-! # Actual settlement comparison from full-source continuation repair

The operational coupling may preserve the initial types and public result,
exhibit a transmission that breaks the send-time conformance rule, or certify
a public binding omission. A send-time breach at a complete settlement leaves
its author with a packet the settled record forbids
(`Vegas.settled_breach_of_sendTime_breach`). The repaired marginal must
consist of actual retained traces. Authentic partial sampling then gives zero repaired
charge and the stated incremental collection bound. A sufficient deposit
compares the realized settlements without assuming any independence between
payoffs, evidence, and detection.

Constructing this coupling for every native continuation remains a separate
operational obligation. Private binding values changed by repair are not part
of the utility readout.
-/

noncomputable section

namespace Vegas

open SourceProgram

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
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (who : Player) (rate gap : ℝ) (deposit : Player → ℝ)
    (coverage : ∀ actual record, record ∈ actual → record.2.sender = who →
      record.1.permits record.2 = false →
      rate ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (nonnegative : 0 ≤ deposit who) (sufficient : gap ≤ min rate 1 * deposit who)
    (coupled : PMF ((application setup leaks).Control ×
      (application setup leaks).Control × BindingMemory (runtime setup) leaks))
    (permitted : ∀ pair ∈ coupled.support,
      Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
          (some pair.2.1)))
    (realized : ∀ pair ∈ coupled.support,
      Nonempty (((application setup leaks).protocol (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
          (some pair.1)))
    (finished : ∀ pair ∈ coupled.support, pair.1.execution.application.config.cut.Terminal)
    (onlyBindings : ∀ pair ∈ coupled.support, pair.2.2.shadow.OwnBindings who)
    (related : ∀ pair ∈ coupled.support,
      (∃ record ∈ (application setup leaks).executionTraffic pair.1.execution,
        record.envelope.sender = who ∧
        (runtime setup).permittedServiceEnvelope record.observation record.ledger
          record.envelope = false) ∨
      pair.1.execution.application.publicView.missedBindingBy who = true ∨
      pair.2.2.Frame (runtime setup) leaks who pair.1.execution pair.2.1.execution)
    (bounded : ∀ pair ∈ coupled.support,
      baseUtility setup leaks (fun state => utility (setup.parameterOutcome parameter state))
          (some pair.1) who ≤
        baseUtility setup leaks (fun state => utility (setup.parameterOutcome parameter state))
          (some pair.2.1) who + gap)
    (originalIntegrable : PayoffIntegrable coupled fun pair =>
      baseUtility setup leaks (fun state => utility (setup.parameterOutcome parameter state))
        (some pair.1) who)
    (repairedIntegrable : PayoffIntegrable coupled fun pair =>
      baseUtility setup leaks (fun state => utility (setup.parameterOutcome parameter state))
        (some pair.2.1) who) :
    let settle := TerminalAudit.settlement
      (baseUtility setup leaks (fun state => utility (setup.parameterOutcome parameter state)))
      ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
      deposit
    expect ((coupled.map (fun pair => some pair.1)).bind settle) (fun payoffs => payoffs who) ≤
      expect ((coupled.map (fun pair => some pair.2.1)).bind settle)
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
      opportunities network sample authentic ⟨some pair.2.1, trace⟩ who
  have collected (pair) (supported : pair ∈ coupled.support) (bad : pair ∈ departed) :
      min rate 1 ≤ TerminalAudit.charge observe audit (some pair.1) who := by
    rcases related pair supported with traffic | missing | framed
    · obtain ⟨record, present, author, breach⟩ := traffic
      obtain ⟨trace⟩ := realized pair supported
      obtain ⟨other, otherPresent, sameAuthor, forbidden⟩ :=
        settled_breach_of_sendTime_breach (initialLaw setup) _ _
          (fun state member => by
            obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
            exact activationKept_initial _) trace
          (finished pair supported) record present breach
      have lowerCharge : rate ≤ TerminalAudit.charge observe audit (some pair.1) who :=
        (runtime setup).serviceAudit_charge_from_record leaks
          (fun settled traffic => (settled, traffic.envelope))
          (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
          sample who rate coverage pair.1 other otherPresent (sameAuthor.trans author) forbidden
      exact (min_le_left _ _).trans lowerCharge
    · change min rate 1 ≤ TerminalAudit.charge
        ((runtime setup).serviceAuditObservation leaks)
        ((runtime setup).serviceAudit leaks _) (some pair.1) who
      rw [(runtime setup).serviceAudit_charge]
      simpa only [Option.elim_some, missing, ↓reduceIte] using min_le_right rate (1 : ℝ)
    · exact (bad framed).elim
  have incremental : (coupled.toOuterMeasure departed).toReal * min rate 1 ≤
      expect (coupled.map (fun pair => some pair.1))
          (fun state => TerminalAudit.charge observe audit state who) -
        expect (coupled.map (fun pair => some pair.2.1))
          (fun state => TerminalAudit.charge observe audit state who) := by
    have zero : expect (coupled.map (fun pair => some pair.2.1))
        (fun state => TerminalAudit.charge observe audit state who) = 0 := by
      rw [expect_map]
      calc
        _ = expect coupled (fun _ => (0 : ℝ)) := expect_congr_on_support clean
        _ = 0 := expect_constant _ _
    rw [zero, sub_zero, expect_map, Function.comp_def]
    calc
      _ = expect coupled (fun pair => (if pair ∈ departed then 1 else 0) * min rate 1) := by
        rw [expect_mul_const, ← expect_indicator]
        exact congrArg (· * min rate 1)
          (expect_congr_on_support fun _ _ => by split_ifs <;> rfl)
      _ ≤ _ := by
        refine expect_mono ?_ (payoffIntegrable_of_bounded _ _ (C := |min rate 1|) fun pair => by
          split <;> simp) (TerminalAudit.payoffIntegrable_charge _ _ _ _)
        intro pair supported
        by_cases bad : pair ∈ departed
        · simpa only [bad, ite_true, one_mul] using collected pair supported bad
        · simp only [bad, ite_false, zero_mul]
          exact ENNReal.toReal_nonneg
  apply TerminalAudit.settlement_le_of_departure_coupling coupled
    (fun pair => some pair.1) (fun pair => some pair.2.1) _ observe audit deposit who departed
      gap (min rate 1) originalIntegrable repairedIntegrable _ _ incremental nonnegative sufficient
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
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    [leaks.FiniteSupport]
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks) [network.FiniteSupport]
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (who : Player) (probability : Player → ℝ) (positive : 0 < probability who)
    (coverage : ∀ actual record, record ∈ actual → record.2.sender = who →
      record.1.permits record.2 = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (coupled : PMF ((application setup leaks).Control ×
      (application setup leaks).Control × BindingMemory (runtime setup) leaks))
    (realized : ∀ pair ∈ coupled.support,
      Nonempty (((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
          (some pair.1)))
    (permitted : ∀ pair ∈ coupled.support,
      Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
          (some pair.2.1)))
    (finished : ∀ pair ∈ coupled.support, pair.1.execution.application.config.cut.Terminal)
    (onlyBindings : ∀ pair ∈ coupled.support, pair.2.2.shadow.OwnBindings who)
    (related : ∀ pair ∈ coupled.support,
      (∃ record ∈ (application setup leaks).executionTraffic pair.1.execution,
        record.envelope.sender = who ∧
        (runtime setup).permittedServiceEnvelope record.observation record.ledger
          record.envelope = false) ∨
      pair.1.execution.application.publicView.missedBindingBy who = true ∨
      pair.2.2.Frame (runtime setup) leaks who pair.1.execution pair.2.1.execution) :
    let base := baseUtility setup leaks
      (fun state => utility (setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit setup leaks bounds rosters network base
      (fun owner => min (probability owner) 1)
    let settle := TerminalAudit.settlement base ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit
    expect ((coupled.map (fun pair => some pair.1)).bind settle) (fun payoffs => payoffs who) ≤
      expect ((coupled.map (fun pair => some pair.2.1)).bind settle)
        (fun payoffs => payoffs who) := by
  intro base deposit settle
  classical
  have ratePositive : 0 < min (probability who) 1 := lt_min positive zero_lt_one
  let payoff := fun history : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History =>
    base history.state who
  have : Nonempty ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History :=
    ⟨((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).initHistory⟩
  let lower := GameTheory.FinitePayoffBounds.lower payoff
  let upper := GameTheory.FinitePayoffBounds.upper payoff
  have inRange (history) : |payoff history| ≤ |lower| + |upper| := by
    have below := GameTheory.FinitePayoffBounds.lower_le payoff history
    have above := GameTheory.FinitePayoffBounds.le_upper payoff history
    rw [abs_le]
    constructor
    · linarith [neg_abs_le lower, abs_nonneg upper]
    · linarith [le_abs_self upper, abs_nonneg lower]
  have originalIntegrable : PayoffIntegrable coupled fun pair => base (some pair.1) who :=
    payoffIntegrable_of_bounded_on_support _ _ fun pair supported => by
      obtain ⟨trace⟩ := realized pair supported
      exact inRange ⟨some pair.1, trace⟩
  have repairedIntegrable : PayoffIntegrable coupled fun pair => base (some pair.2.1) who :=
    payoffIntegrable_of_bounded_on_support _ _ fun pair supported => by
      obtain ⟨trace⟩ := permitted pair supported
      exact inRange ((sourceServiceMenu_in_effective setup leaks bounds rosters).history
        (initialLaw setup) (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network) ⟨some pair.2.1, trace⟩)
  refine sourceService_repair_settlement_le setup leaks bounds values capacity rosters
    opportunities network parameter utility sample authentic who (probability who)
    (min (probability who) 1 * deposit who) deposit coverage
    (rosterAuditDeposit_nonnegative setup leaks bounds rosters network base _ who ratePositive)
    (le_refl _) coupled permitted
    (fun pair supported => by
      obtain ⟨trace⟩ := realized pair supported
      exact ⟨(bounds.menu (runtime setup) leaks).toRawTrace (initialLaw setup) _ _ trace⟩)
    finished onlyBindings related ?_ originalIntegrable repairedIntegrable
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

end Vegas
