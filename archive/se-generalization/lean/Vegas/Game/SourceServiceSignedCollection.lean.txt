/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAudit
import Vegas.Game.ServiceSettledEvidence
import Vegas.Pending.ReactiveSettledCollection
import Interaction.ReactiveLocalContinuation
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Collection after an actual committed signed packet

An information-site commitment performs its actual physical response. The
resulting signed packet is derived from that transition, then persists through
every later policy. Bounded terminal play supplies the remaining continuation
fuel and the complete-play contract supplies the final settled record.

The authentic backend covers signed packets forbidden by the final record,
with observation and conditional report-delivery bounds. The packet's final
forbiddenness remains an explicit operational obligation over actual reachable
complete records. No payoff comparison, send-time evidence, certain monitoring,
caller-supplied traffic or continuation-fuel premise is used.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

open Classical in
/-- An actual active history committing a packet forbidden at every reachable
complete record has the backend's collection bound under arbitrary later
behavioral policies. Actual emission, persistence and fuel are derived. -/
theorem settledPacket_collection_committed
    (menu : (application setup leaks).ResponseMenu)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (backend : EvidenceReportService (SettledEvidence setup))
    (profile : ∀ player,
      (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (who : Player) (remaining : Nat) (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (info : (menu.information (initialLaw setup) horizon scheduler).InfoState who)
    (choice : (menu.information (initialLaw setup) horizon scheduler).Choice who info)
    (observed : (menu.information (initialLaw setup) horizon scheduler).infoOf who
      history.trace = info)
    (material : (application setup leaks).Submission)
    (selected : choice.1 = some ⟨some material⟩)
    (forbidden : ∀ fuel
      (final : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).History),
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).ReachesWithin fuel
        (menu.toRawHistory (initialLaw setup) horizon scheduler history) final →
      ∀ control, final.state = some control → control.execution.application.config.cut.Terminal →
        Emitted setup leaks control.execution
          (⟨(who, execution.network.nextSerial who), (application setup leaks).packet
            ((application setup leaks).submit execution.application who material) who
              (execution.network.known who) material⟩ :
                Message Player (WitnessedPacket (graph setup))) →
        ((runtime setup).settledRecord leaks control.execution).permits
          (⟨(who, execution.network.nextSerial who), (application setup leaks).packet
            ((application setup leaks).submit execution.application who material) who
              (execution.network.known who) material⟩ :
                Message Player (WitnessedPacket (graph setup))) = false)
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate) :
    observationRate who * deliveryRate who ≤
      expect ((menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
        (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
        (Profile.update
          (sig := (menu.information (initialLaw setup) horizon scheduler).behavioralSignature)
          profile who ((profile who).commit info choice)) history)
        (fun final => TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
          (sourceServiceAudit setup leaks backend.sample) final.state who) := by
  classical
  subst info
  let app := application setup leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  let protocol := menu.protocol (initialLaw setup) horizon scheduler
  let updated := Profile.update (sig := model.behavioralSignature) profile who
    ((profile who).commit (model.infoOf who history.trace) choice)
  let observe := fun final : protocol.History =>
    (runtime setup).serviceAuditObservation leaks final.state
  let audit := sourceServiceAudit setup leaks backend.sample
  change observationRate who * deliveryRate who ≤
    expect (model.runBehavioralTerminalFrom
      (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories updated history)
      (fun final => TerminalAudit.charge observe audit final who)
  let record : app.TrafficRecord :=
    ⟨execution.application.publicView, execution.network.ledger,
      ⟨(who, execution.network.nextSerial who), app.packet
        (app.submit execution.application who material) who
          (execution.network.known who) material⟩⟩
  let rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler history.trace
  have traceBound := app.trace_bound (initialLaw setup) horizon scheduler rawTrace
  have traceLength : rawTrace.length = history.trace.length :=
    menu.toRawTrace_length (initialLaw setup) horizon scheduler history.trace
  have positive : 0 < app.rank horizon history.state := by
    rw [current]
    change 0 < 2 * remaining + 1
    omega
  let fuel := 2 * horizon + 1 - history.trace.length - 1
  have fuelEq : 1 + fuel = 2 * horizon + 1 - history.trace.length := by
    dsimp only [fuel]
    omega
  have committed := menu.run_commit_response (initialLaw setup) horizon scheduler profile
    history who remaining execution current choice ⟨some material⟩ selected
  change (model.runBehavioralFrom updated 1 history).map History.state = _ at committed
  rw [model.runBehavioralTerminalFrom_eq_remaining _ updated
    (menu.bounded (initialLaw setup) horizon scheduler) history, ← fuelEq,
    model.runBehavioralFrom_add,
    expect_bind_tower _ _ _ (TerminalAudit.payoffIntegrable_charge _ _ _ _)]
  calc
    observationRate who * deliveryRate who =
        expect (model.runBehavioralFrom updated 1 history)
          (fun _ => observationRate who * deliveryRate who) := (expect_constant _ _).symm
    _ ≤ _ := by
      refine expect_mono ?_ (payoffIntegrable_constant _ _) ?_
      rotate_left
      · exact payoffIntegrable_of_bounded _ _ (C := 1) fun next => by
          rw [abs_of_nonneg (expect_nonneg _ _ fun _ _ =>
            (TerminalAudit.charge_mem_Icc _ _ _ _).1)]
          exact expect_le_const _ _ (TerminalAudit.payoffIntegrable_charge _ _ _ _) _
            fun _ _ => (TerminalAudit.charge_mem_Icc _ _ _ _).2
      intro next supported
      have nextState : next.state =
          some ⟨remaining, none, execution.respond app who ⟨some material⟩⟩ := by
        have member : next.state ∈
            ((model.runBehavioralFrom updated 1 history).map History.state).support := by
          rw [PMF.support_map]
          exact ⟨next, supported, rfl⟩
        rw [committed] at member
        exact (PMF.mem_support_pure_iff _ _).mp member
      have path := protocol.runRandomizedFor_reachesWithin (model.randomizedChooser updated)
        1 history next supported
      have length : next.trace.length = history.trace.length + 1 := by
        cases path with
        | refl =>
            rw [current] at nextState
            cases nextState
        | step joint legal realized rest =>
            have same := protocol.reachesWithin_zero_iff.mp rest
            subst next
            rfl
      have activeTrace : (app.protocol (initialLaw setup) horizon scheduler).Trace
          (some ⟨remaining, some who, execution⟩) := current ▸ rawTrace
      have present : record ∈ app.stateTraffic next.state := by
        rw [nextState]
        exact (runtime setup).signed_response_traffic leaks execution who material activeTrace
      have enough : 2 * horizon + 1 ≤ next.trace.length + fuel := by
        dsimp only [fuel]
        omega
      apply (runtime setup).settledPacket_collection_continuation leaks menu (initialLaw setup)
        horizon scheduler backend observationRate deliveryRate delivery_nonnegative coverage
        updated fuel next record present
      intro final finalSupported control finalState
      have stopped : app.terminal final.state := by
        rcases protocol.runRandomizedFor_terminal_or_length (model.randomizedChooser updated)
            fuel next final finalSupported with terminal | terminalLength
        · exact terminal
        · have bound := app.trace_bound (initialLaw setup) horizon scheduler
            (menu.toRawTrace (initialLaw setup) horizon scheduler final.trace)
          rw [menu.toRawTrace_length] at bound
          have exhausted : app.rank horizon final.state = 0 := by omega
          exact (app.rank_zero horizon final.state).mp exhausted
      have terminalTrace : (app.protocol (initialLaw setup) horizon scheduler).Trace
          (some control) :=
        finalState ▸ menu.toRawTrace (initialLaw setup) horizon scheduler final.trace
      have complete := completes control terminalTrace (finalState ▸ stopped)
      have suffix := protocol.runRandomizedFor_reachesWithin (model.randomizedChooser updated)
        fuel next final finalSupported
      have kept : record ∈ app.stateTraffic final.state := by
        have persists := (menu.trafficAudit_reaches (initialLaw setup) horizon scheduler
          suffix).subset
        rw [menu.trafficAudit_eq_stateTraffic, menu.trafficAudit_eq_stateTraffic] at persists
        exact persists present
      have inputs := app.stateTraffic_inputs (initialLaw setup) horizon scheduler terminalTrace
      rw [finalState] at kept
      change (app.executionTraffic control.execution).map
        ReactiveApplication.TrafficRecord.envelope = control.execution.network.inputs at inputs
      have emitted : Emitted setup leaks control.execution record.envelope := by
        unfold Emitted
        rw [← inputs]
        exact List.mem_map.mpr ⟨record, kept, rfl⟩
      exact forbidden (1 + fuel) (menu.toRawHistory (initialLaw setup) horizon scheduler final)
        (menu.reaches_raw (initialLaw setup) horizon scheduler (path.trans suffix)) control
        finalState complete emitted

end Vegas
