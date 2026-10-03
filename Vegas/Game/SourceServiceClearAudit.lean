/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRiskPrefix
import Vegas.Game.SourceServiceAudit
import Vegas.Game.AsyncServiceForeignEscape

/-! # Audit soundness at an actual clear owner prefix

A legal risk-menu history and persistent owner clarity derive the verdict of
every earlier owner envelope against the current contract record, together
with absence of a public owner miss. Other owners may have used expanded raw
responses. Current opportunity protection is not required.

The same audit kernel consequently has zero owner charge on this prefix for
every authentic partial sample. At an unfinished event the current record
permits its pending packets; this does not make its current verdict immutable.
No statement concerns later responses after risk expansion, future collection,
watcher coverage, or equilibrium comparisons.

At source-compatible native information the owner's actual recalled input
derives the same clarity in every member hidden history. The current audit
therefore assigns zero owner charge throughout that fiber, even when other
owners' private risk is hidden.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability GameTheory.Enforcement
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Earlier actual owner traffic is permitted by the current record, and
there is no public owner miss. Clarity is owner-local and persistent only. -/
theorem sourceServiceRisk_history_clear
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (control : (application setup leaks).Control)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player)
    (clear : (runtime setup).persistentServiceRisk leaks bound who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) = false) :
    control.execution.application.publicView.missedDecisionBy who = false ∧
      ∀ record ∈ (application setup leaks).executionTraffic control.execution,
        record.envelope.sender = who →
          ((runtime setup).settledRecord leaks control.execution).permits record.envelope =
            true := by
  have noMiss := ((runtime setup).persistentServiceRisk_clear_iff leaks bound who _ _).mp clear
    |>.1.1
  obtain ⟨_, _, _, good⟩ := riskPacketFacts_history bounds bound contract control trace who clear
  let app := application setup leaks
  have rawTrace := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace
    (initialLaw setup) horizon scheduler trace
  have inputs := app.stateTraffic_inputs (initialLaw setup) horizon scheduler rawTrace
  change (app.executionTraffic control.execution).map ReactiveApplication.TrafficRecord.envelope =
    control.execution.network.inputs at inputs
  refine ⟨noMiss, ?_⟩
  intro record member authored
  have emitted : Emitted setup leaks control.execution record.envelope := by
    unfold Emitted
    rw [← inputs]
    exact List.mem_map.mpr ⟨record, member, rfl⟩
  exact (good record.envelope authored emitted).permits

/-- The current-record audit kernel assigns zero charge to a clear owner.
Authenticity suffices; complete observation and report coverage are absent. -/
theorem sourceServiceRisk_history_audit_clear
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (control : (application setup leaks).Control)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player)
    (clear : (runtime setup).persistentServiceRisk leaks bound who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) = false)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) (some control) who = 0 := by
  obtain ⟨noMiss, permits⟩ := sourceServiceRisk_history_clear bounds bound contract control trace
    who clear
  unfold sourceServiceAudit
  rw [(runtime setup).serviceAudit_charge, noMiss]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply (application setup leaks).sampledTrafficAudit_sound
  · exact authentic _
  · exact permits

end Vegas

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory.Math.Probability GameTheory.Enforcement
open Interaction EventGraphRuntime GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "menu" => service.bounds.riskMenu (runtime service.setup) service.leaks
  service.bound
local notation "model" => ReactiveApplication.ResponseMenu.information
  (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound)
  (initialLaw service.setup) service.horizon service.scheduler

/-- Actual compatible information excludes current owner charge pointwise
on its full hidden history fiber. Foreign private risk need not be clear. -/
theorem sourceCompatibleInfo_history_audit_clear (who : Player)
    (site : (model).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (history : (model).InformationHistory who site.1)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    TerminalAudit.charge ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) history.1.state who = 0 := by
  cases current : history.1.state with
  | none => exact (runtime service.setup).serviceAudit_charge_none service.leaks _ who
  | some control =>
      have clear := ((runtime service.setup).serviceRisk_clear_iff service.leaks service.bound who
        _ _).mp (service.sourceCompatibleInfo_history_focal_clear who site compatible history
          control current) |>.1
      have trace : ((menu).protocol (initialLaw service.setup) service.horizon
          service.scheduler).Trace (some control) := current ▸ history.1.trace
      exact sourceServiceRisk_history_audit_clear service.bounds service.bound service.contract
        control trace who clear sample authentic

end Vegas.AsyncServiceSpec
