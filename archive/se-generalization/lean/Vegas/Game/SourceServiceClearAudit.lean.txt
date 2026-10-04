/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRiskPrefix
import Vegas.Game.SourceServiceAudit
import Vegas.Game.AsyncServiceSourceSites

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

At source-compatible native information, own recall, public state and receipts
transfer the current owner verdict from an actual legal witness to every
initialized RAW history with that input. The current audit consequently has
zero owner charge there without restricting foreign effective or RAW choices.
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
local notation "runtime" => runtime service.setup
local notation "menu" => service.bounds.riskMenu (runtime) service.leaks service.bound

/-- The source-compatible local information itself certifies the current
owner's verdicts on any actual initialized raw history. Foreign unusable
commitments and other excluded responses are not ruled out by this premise. -/
theorem sourceCompatibleInfo_raw_history_clear
    (control : (app).Control)
    (trace : ((app).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some control)) (who : Player)
    (compatible : service.sourceCompatibleInfo who
      (some (control.execution.recall who, control.execution.observe (app) who))) :
    control.execution.application.publicView.missedDecisionBy who = false ∧
      ∀ record ∈ (app).executionTraffic control.execution,
        record.envelope.sender = who →
          ((runtime).settledRecord service.leaks control.execution).permits record.envelope =
            true := by
  obtain ⟨_profile, _turns, _timing, _permitted, _effective, history, remaining, witness,
    current, observed, _supported, allClear, _clear⟩ := compatible
  have witnessTrace : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).Trace (some ⟨remaining, some who, witness⟩) := current ▸ history.trace
  have input : (witness.recall who, witness.observe (app) who) =
      (control.execution.recall who, control.execution.observe (app) who) := by
    apply Option.some.inj
    have atState : ((menu).information (initialLaw service.setup) service.horizon
        service.scheduler).infoOf who history.trace = (app).observe who history.state :=
      (menu).info (initialLaw service.setup) service.horizon service.scheduler who history.trace
    rw [atState, current] at observed
    simpa only [ReactiveApplication.observe, ↓reduceIte] using observed
  have recalled : witness.recall who = control.execution.recall who := congrArg Prod.fst input
  have viewed : witness.observe (app) who = control.execution.observe (app) who :=
    congrArg Prod.snd input
  have publicEq : witness.application.publicView = control.execution.application.publicView :=
    congrArg (fun view : (app).PlayerView => view.application.publicView) viewed
  have receiptsEq : witness.receipts = control.execution.receipts :=
    congrArg ReactiveApplication.PlayerView.receipts viewed
  have settledEq : (runtime).settledRecord service.leaks witness =
      (runtime).settledRecord service.leaks control.execution := by
    unfold EventGraphRuntime.settledRecord
    rw [publicEq, receiptsEq]
  obtain ⟨noMiss, good⟩ := sourceServiceRisk_history_clear service.bounds service.bound
    service.contract ⟨remaining, some who, witness⟩ witnessTrace who (allClear who)
  have witnessRaw := (menu).toRawTrace (initialLaw service.setup) service.horizon service.scheduler
    witnessTrace
  have witnessFacts := legalFacts service.setup service.leaks service.horizon service.scheduler
    ⟨remaining, some who, witness⟩ witnessRaw
  have actualFacts := legalFacts service.setup service.leaks service.horizon service.scheduler
    control trace
  have actualTraffic := (app).stateTraffic_inputs (initialLaw service.setup) service.horizon
    service.scheduler trace
  have witnessTraffic := (app).stateTraffic_inputs (initialLaw service.setup) service.horizon
    service.scheduler witnessRaw
  change ((app).executionTraffic control.execution).map ReactiveApplication.TrafficRecord.envelope
    = control.execution.network.inputs at actualTraffic
  change ((app).executionTraffic witness).map ReactiveApplication.TrafficRecord.envelope =
    witness.network.inputs at witnessTraffic
  refine ⟨?_, ?_⟩
  · rw [← publicEq]
    exact noMiss
  · intro record member authored
    have emitted : record.envelope ∈ control.execution.network.inputs := by
      rw [← actualTraffic]
      exact List.mem_map.mpr ⟨record, member, rfl⟩
    have owned : record.envelope ∈ control.execution.network.inputs.filter
        (fun message => message.sender = who) :=
      List.mem_filter.mpr ⟨emitted, by simpa only [decide_eq_true_eq] using authored⟩
    rw [actualFacts.inputs who, ← recalled, ← witnessFacts.inputs who] at owned
    have prior : record.envelope ∈ witness.network.inputs := (List.mem_filter.mp owned).1
    rw [← witnessTraffic] at prior
    obtain ⟨priorRecord, priorMember, same⟩ := List.mem_map.mp prior
    rw [← settledEq, ← same]
    exact good priorRecord priorMember ((congrArg Message.sender same).trans authored)

/-- Authentic partial evidence has zero current charge in a compatible raw
history. No source-strategy, foreign-conformance, or risk-menu trace premise
is imposed on that history. -/
theorem sourceCompatibleInfo_raw_history_audit_clear
    (control : (app).Control)
    (trace : ((app).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some control)) (who : Player)
    (compatible : service.sourceCompatibleInfo who
      (some (control.execution.recall who, control.execution.observe (app) who)))
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    TerminalAudit.charge ((runtime).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) (some control) who = 0 := by
  obtain ⟨noMiss, good⟩ :=
    service.sourceCompatibleInfo_raw_history_clear control trace who compatible
  unfold sourceServiceAudit
  rw [(runtime).serviceAudit_charge, noMiss]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply (app).sampledTrafficAudit_sound
  · exact authentic _
  · exact good

/-- Every hidden member of a compatible native information site has zero
current charge. The supplied actual response menu may be the complete effective
menu or the retained risk menu; legal history derives raw initialization and
the owner's actual full input. No future charge or posterior claim follows. -/
theorem sourceCompatibleInfo_history_audit_clear
    (responseMenu : (application service.setup service.leaks).ResponseMenu)
    (who : Player)
    (site : (responseMenu.information (initialLaw service.setup) service.horizon
      service.scheduler).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (history : (responseMenu.information (initialLaw service.setup) service.horizon
      service.scheduler).InformationHistory who site.1)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    TerminalAudit.charge ((runtime).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) history.1.state who = 0 := by
  obtain ⟨past, view, observed, _identity, _clear⟩ :=
    service.sourceCompatibleInfo_clear who site.1 compatible
  rcases history with ⟨⟨state, trace⟩, same⟩
  change (responseMenu.signals (initialLaw service.setup) service.horizon
    service.scheduler).infoOf who trace = site.1 at same
  rw [responseMenu.info (initialLaw service.setup) service.horizon service.scheduler who trace,
    observed] at same
  cases state with
  | none => cases same
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at same
        have actualCompatible : service.sourceCompatibleInfo who
            (some (control.execution.recall who, control.execution.observe (app) who)) := by
          rw [observed] at compatible
          exact (congrArg some (Option.some.inj same)).symm ▸ compatible
        exact service.sourceCompatibleInfo_raw_history_audit_clear control
          (responseMenu.toRawTrace (initialLaw service.setup) service.horizon service.scheduler
            trace) who actualCompatible sample authentic
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at same
        cases same

end Vegas.AsyncServiceSpec
