/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAudit
import Vegas.Pending.ReactiveSettledCollection
import Interaction.ReactiveLocalContinuation
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Collection after an actual committed signed packet

An information-site commitment performs its actual physical response. The
resulting signed packet is derived from that transition, then persists through
every later policy. Bounded terminal play supplies the remaining continuation
fuel and the complete-play contract supplies the final settled record.

The authentic backend covers signed packets forbidden by the final record,
with observation and conditional report-delivery bounds. That every reachable
complete record after the commitment forbids some actual packet of the
committer remains an explicit operational obligation; the forbidden packet may
be the committed one or another. No payoff comparison, send-time evidence,
certain monitoring, caller-supplied traffic or continuation-fuel premise is
used.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

open Classical in
/-- An actual active history whose commitment leaves every reachable complete
record forbidding some actual packet of the committer has the backend's
collection bound under arbitrary later behavioral policies. Actual emission,
persistence and fuel are derived. -/
theorem forbiddenTraffic_collection_committed
    (menu : (serviceApplication setup mode deadline leaks).ResponseMenu)
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (completes : CompletesPlay (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler)
    (backend : EvidenceReportService (SettledEvidence setup mode))
    (profile : ∀ player,
      (menu.information (serviceInitialLaw setup mode) horizon scheduler).BehavioralPolicy player)
    (history : (menu.protocol (serviceInitialLaw setup mode) horizon scheduler).History)
    (who : Player) (remaining : Nat) (execution :
        (serviceApplication setup mode deadline leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (info : (menu.information (serviceInitialLaw setup mode) horizon scheduler).InfoState who)
    (choice : (menu.information (serviceInitialLaw setup mode) horizon scheduler).Choice who info)
    (observed : (menu.information (serviceInitialLaw setup mode) horizon scheduler).infoOf who
      history.trace = info)
    (material : (serviceApplication setup mode deadline leaks).Submission)
    (selected : choice.1 = some ⟨some material⟩)
    (charged : ∀ fuel
      (next final : ((serviceApplication setup mode deadline leaks).protocol
          (serviceInitialLaw setup mode) horizon scheduler).History),
      next.state = some ⟨remaining, none,
        execution.respond (serviceApplication setup mode deadline leaks) who ⟨some material⟩⟩ →
      ((serviceApplication setup mode deadline leaks).protocol
          (serviceInitialLaw setup mode) horizon scheduler).ReachesWithin fuel next final →
      ∀ control, final.state = some control → control.execution.application.config.cut.Terminal →
        ∃ record ∈ (serviceApplication setup mode deadline leaks).executionTraffic
            control.execution,
          record.envelope.sender = who ∧
          ((serviceRuntime setup mode deadline).settledRecord leaks control.execution).permits
            record.envelope = false)
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate) :
    observationRate who * deliveryRate who ≤
      expect ((menu.information
          (serviceInitialLaw setup mode) horizon scheduler).runBehavioralTerminalFrom
        (menu.bounded (serviceInitialLaw setup mode) horizon scheduler).wellFoundedHistories
        (Profile.update
          (sig := (menu.information
              (serviceInitialLaw setup mode) horizon scheduler).behavioralSignature)
          profile who ((profile who).commit info choice)) history)
        (fun final => TerminalAudit.charge
            ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
          (serviceSourceAudit setup mode deadline leaks backend.sample) final.state who) := by
  classical
  subst info
  let app := serviceApplication setup mode deadline leaks
  let model := menu.information (serviceInitialLaw setup mode) horizon scheduler
  let protocol := menu.protocol (serviceInitialLaw setup mode) horizon scheduler
  let updated := Profile.update (sig := model.behavioralSignature) profile who
    ((profile who).commit (model.infoOf who history.trace) choice)
  let observe := fun final : protocol.History =>
    (serviceRuntime setup mode deadline).serviceAuditObservation leaks final.state
  let audit := serviceSourceAudit setup mode deadline leaks backend.sample
  change observationRate who * deliveryRate who ≤
    expect (model.runBehavioralTerminalFrom
      (menu.bounded
          (serviceInitialLaw setup mode) horizon scheduler).wellFoundedHistories updated history)
      (fun final => TerminalAudit.charge observe audit final who)
  let record : app.TrafficRecord :=
    ⟨execution.application.publicView, execution.network.ledger,
      ⟨(who, execution.network.nextSerial who), app.packet
        (app.submit execution.application who material) who
          (execution.network.known who) material⟩⟩
  let rawTrace := menu.toRawTrace (serviceInitialLaw setup mode) horizon scheduler history.trace
  have traceBound := app.trace_bound (serviceInitialLaw setup mode) horizon scheduler rawTrace
  have traceLength : rawTrace.length = history.trace.length :=
    menu.toRawTrace_length (serviceInitialLaw setup mode) horizon scheduler history.trace
  have positive : 0 < app.rank horizon history.state := by
    rw [current]
    change 0 < 2 * remaining + 1
    omega
  let fuel := 2 * horizon + 1 - history.trace.length - 1
  have fuelEq : 1 + fuel = 2 * horizon + 1 - history.trace.length := by
    dsimp only [fuel]
    omega
  have committed := menu.run_commit_response
      (serviceInitialLaw setup mode) horizon scheduler profile
    history who remaining execution current choice ⟨some material⟩ selected
  change (model.runBehavioralFrom updated 1 history).map History.state = _ at committed
  rw [model.runBehavioralTerminalFrom_eq_remaining _ updated
    (menu.bounded (serviceInitialLaw setup mode) horizon scheduler) history, ← fuelEq,
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
      have activeTrace : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
          (some ⟨remaining, some who, execution⟩) := current ▸ rawTrace
      have present : record ∈ app.stateTraffic next.state := by
        rw [nextState]
        exact (serviceRuntime setup mode deadline).signed_response_traffic leaks execution who
            material activeTrace
      have enough : 2 * horizon + 1 ≤ next.trace.length + fuel := by
        dsimp only [fuel]
        omega
      apply (serviceRuntime setup mode deadline).forbiddenTraffic_collection_continuation leaks
        menu (serviceInitialLaw setup mode) horizon scheduler backend observationRate deliveryRate
        delivery_nonnegative coverage updated fuel next who
      intro final finalSupported
      have stopped : app.terminal final.state := by
        rcases protocol.runRandomizedFor_terminal_or_length (model.randomizedChooser updated)
            fuel next final finalSupported with terminal | terminalLength
        · exact terminal
        · have bound := app.trace_bound (serviceInitialLaw setup mode) horizon scheduler
            (menu.toRawTrace (serviceInitialLaw setup mode) horizon scheduler final.trace)
          rw [menu.toRawTrace_length] at bound
          have exhausted : app.rank horizon final.state = 0 := by omega
          exact (app.rank_zero horizon final.state).mp exhausted
      have suffix := protocol.runRandomizedFor_reachesWithin (model.randomizedChooser updated)
        fuel next final finalSupported
      have kept : record ∈ app.stateTraffic final.state := by
        have persists := (menu.trafficAudit_reaches (serviceInitialLaw setup mode) horizon
          scheduler suffix).subset
        rw [menu.trafficAudit_eq_stateTraffic, menu.trafficAudit_eq_stateTraffic] at persists
        exact persists present
      cases finalState : final.state with
      | none =>
          rw [finalState] at kept
          exact (List.not_mem_nil kept).elim
      | some control =>
          refine ⟨control, rfl, ?_⟩
          have terminalTrace : (app.protocol (serviceInitialLaw setup mode) horizon
              scheduler).Trace (some control) :=
            finalState ▸ menu.toRawTrace (serviceInitialLaw setup mode) horizon scheduler
              final.trace
          have complete := completes control terminalTrace (finalState ▸ stopped)
          exact charged fuel (menu.toRawHistory (serviceInitialLaw setup mode) horizon scheduler
              next) (menu.toRawHistory (serviceInitialLaw setup mode) horizon scheduler final)
            nextState (menu.reaches_raw (serviceInitialLaw setup mode) horizon scheduler suffix)
            control finalState complete

end Vegas
