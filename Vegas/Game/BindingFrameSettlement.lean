/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.BindingRepairReadout
import Vegas.Pending.ReactiveServiceAudit
import Interaction.ReactiveTrafficState

/-! # Actual settlement along a preserved private binding frame

A preserved frame keeps the full traffic history and final contract record.
The entire audit kernel therefore agrees, including collection for offenses
already present in the starting prefix. No clean-prefix, coverage or independence
hypothesis is needed.

For utilities of initial parameters and public source results, the concrete
binding repair also preserves base payoff. Consequently both expected audited
utility and the joint realized payoff vector agree. These statements assume a
preserved frame; they do not establish its closure under arbitrary continuations.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}

/-- Existing traffic and the actual settled record agree jointly. Control fuel
and the active-player field do not enter either audit input. -/
theorem serviceAuditObservation_eq
    (original repaired : (runtime.reactiveApplication leaks).Control)
    (frame : Frame runtime leaks memory owner original.execution repaired.execution) :
    runtime.serviceAuditObservation leaks (some original) =
      runtime.serviceAuditObservation leaks (some repaired) := by
  have traffic : (runtime.reactiveApplication leaks).executionTraffic original.execution =
      (runtime.reactiveApplication leaks).executionTraffic repaired.execution := by
    unfold ReactiveApplication.executionTraffic
    rw [frame.service, frame.environment]
  have record : runtime.settledRecord leaks original.execution =
      runtime.settledRecord leaks repaired.execution := by
    unfold settledRecord
    rw [frame.publicView, frame.receipts]
  change ((runtime.reactiveApplication leaks).executionTraffic original.execution,
    some (runtime.settledRecord leaks original.execution)) =
      ((runtime.reactiveApplication leaks).executionTraffic repaired.execution,
        some (runtime.settledRecord leaks repaired.execution))
  rw [traffic, record]

/-- Every actual collected-verdict law agrees, even for an audit whose sampling
depends on the complete final record and all earlier signed offenses. -/
theorem serviceAudit_eq
    (trafficAudit : SettledRecord graph →
      List (runtime.reactiveApplication leaks).TrafficRecord → PMF (Player → Bool))
    (original repaired : (runtime.reactiveApplication leaks).Control)
    (frame : Frame runtime leaks memory owner original.execution repaired.execution) :
    runtime.serviceAudit leaks trafficAudit
        (runtime.serviceAuditObservation leaks (some original)) =
      runtime.serviceAudit leaks trafficAudit
        (runtime.serviceAuditObservation leaks (some repaired)) := by
  rw [serviceAuditObservation_eq original repaired frame]

end Vegas.EventGraphRuntime.BindingMemory.Frame

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Enforcement
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- In the public-result payoff scope, both the complete expected-utility vector
and the complete sampled settlement vector agree on every preserved frame.
Existing charges need not vanish. -/
theorem bindingFrame_auditedSettlement {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (trafficAudit : SettledRecord (graph setup) →
      List (application setup leaks).TrafficRecord → PMF (Player → Bool))
    (deposit : Player → ℝ)
    (owner : Player) (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Control)
    (frame : memory.Frame (runtime setup) leaks owner original.execution repaired.execution)
    (onlyBindings : memory.shadow.OwnBindings owner) :
    let base := baseUtility setup leaks
      (fun source => utility (setup.parameterOutcome parameter source))
    let observe := (runtime setup).serviceAuditObservation leaks
    let audit := (runtime setup).serviceAudit leaks trafficAudit
    TerminalAudit.utility base observe audit deposit (some original) =
        TerminalAudit.utility base observe audit deposit (some repaired) ∧
      TerminalAudit.settlement base observe audit deposit (some original) =
        TerminalAudit.settlement base observe audit deposit (some repaired) := by
  intro base observe audit
  have baseEq := bindingFrame_baseUtility setup leaks parameter utility owner memory original
    repaired frame onlyBindings
  have observed := BindingMemory.Frame.serviceAuditObservation_eq original repaired frame
  change base (some original) = base (some repaired) at baseEq
  change observe (some original) = observe (some repaired) at observed
  constructor
  · funext who
    simp only [TerminalAudit.utility, TerminalAudit.charge, baseEq, observed]
  · simp only [TerminalAudit.settlement, baseEq, observed]

/-- A coupling supported on preserved frames gives equal actual settlement
laws. Its prior charges and the audit's correlated partial sampling are retained. -/
theorem bindingFrame_settlement_law {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (trafficAudit : SettledRecord (graph setup) →
      List (application setup leaks).TrafficRecord → PMF (Player → Bool))
    (deposit : Player → ℝ) (owner : Player)
    (coupled : PMF ((application setup leaks).Control ×
      (application setup leaks).Control × BindingMemory (runtime setup) leaks))
    (framed : ∀ pair ∈ coupled.support,
      pair.2.2.Frame (runtime setup) leaks owner pair.1.execution pair.2.1.execution)
    (onlyBindings : ∀ pair ∈ coupled.support, pair.2.2.shadow.OwnBindings owner) :
    let base := baseUtility setup leaks
      (fun source => utility (setup.parameterOutcome parameter source))
    let settle := TerminalAudit.settlement base ((runtime setup).serviceAuditObservation leaks)
      ((runtime setup).serviceAudit leaks trafficAudit) deposit
    (coupled.map (fun pair => some pair.1)).bind settle =
      (coupled.map (fun pair => some pair.2.1)).bind settle := by
  intro base settle
  rw [PMF.bind_map, PMF.bind_map]
  apply bind_congr_on_support _
  intro pair supported
  exact (bindingFrame_auditedSettlement setup leaks parameter utility trafficAudit deposit
    owner pair.2.2 pair.1 pair.2.1 (framed pair supported) (onlyBindings pair supported)).2

end Vegas
