/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceWithholdingGuessBound
import Vegas.Game.SourceServiceSignedCollection

/-! # A genuine current withholding followed by arbitrary native play

Committing the actual available withholding response emits its own persistent
traffic record. The existing terminal evaluator and LOW-first continuation
bound therefore apply to the entire later native policy, including further
packets. No inclusion probability or owner-silent continuation is supplied.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

open Classical in
/-- The first actual withholding bounds a complete native continuation by the
LOW-correct indicator, even if the continuation transmits further responses. -/
theorem sourceService_withhold_guess_committed_le
    (menu : (application setup leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (profile : ∀ who, (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (who : Player) (remaining : Nat) (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (info : (menu.information (initialLaw setup) horizon scheduler).InfoState who)
    (choice : (menu.information (initialLaw setup) horizon scheduler).Choice who info)
    (observed : (menu.information (initialLaw setup) horizon scheduler).infoOf who history.trace =
      info)
    (material : (application setup leaks).Submission)
    (selected : choice.1 = some ⟨some material⟩)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (withheld : material.call.packet = .withhold event)
    (backend : EvidenceReportService (SettledEvidence setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (high : Bool) (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit who)
    (sufficient : 1 ≤ observationRate who * deliveryRate who * deposit who) :
    expect ((menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
      (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
      (Profile.update
        (sig := (menu.information (initialLaw setup) horizon scheduler).behavioralSignature)
        profile who ((profile who).commit info choice)) history)
      (fun final => TerminalAudit.utility
        (fun state _ => sourcePublicationGuessValue setup leaks event payload outputEq high state)
        ((runtime setup).serviceAuditObservation leaks)
        (sourceServiceAudit setup leaks backend.sample) deposit final.state who) ≤
      if high then 0 else 1 := by
  subst info
  let app := application setup leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  let protocol := menu.protocol (initialLaw setup) horizon scheduler
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let updated := Profile.update (sig := model.behavioralSignature) profile who
    ((profile who).commit (model.infoOf who history.trace) choice)
  let value := fun final : protocol.History => TerminalAudit.utility
    (fun state _ => sourcePublicationGuessValue setup leaks event payload outputEq high state)
    ((runtime setup).serviceAuditObservation leaks)
    (sourceServiceAudit setup leaks backend.sample) deposit final.state who
  have integrable (law : PMF protocol.History) : PayoffIntegrable law value := by
    have baseIntegrable : PayoffIntegrable law (fun final =>
        sourcePublicationGuessValue setup leaks event payload outputEq high final.state) := by
      apply payoffIntegrable_of_bounded _ _ (C := 1)
      intro final
      have bounds := sourcePublicationGuessValue_mem_Icc setup leaks event payload outputEq high
        final.state
      rw [abs_of_nonneg bounds.1]
      exact bounds.2
    exact TerminalAudit.payoffIntegrable_utility law
      (fun final _ => sourcePublicationGuessValue setup leaks event payload outputEq high
        final.state)
      (fun final => (runtime setup).serviceAuditObservation leaks final.state)
      (sourceServiceAudit setup leaks backend.sample) deposit who baseIntegrable
  let rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler history.trace
  have traceBound := app.trace_bound (initialLaw setup) horizon scheduler rawTrace
  have lengthEq : rawTrace.length = history.trace.length := menu.toRawTrace_length ..
  have positive : 0 < app.rank horizon history.state := by
    rw [current]
    change 0 < 2 * remaining + 1
    omega
  let fuel := 2 * horizon + 1 - history.trace.length - 1
  have fuelEq : 1 + fuel = 2 * horizon + 1 - history.trace.length := by
    dsimp only [fuel]
    omega
  have committed := menu.run_commit_response (initialLaw setup) horizon scheduler profile history
    who remaining execution current choice ⟨some material⟩ selected
  change (model.runBehavioralFrom updated 1 history).map History.state = _ at committed
  change expect (model.runBehavioralTerminalFrom certificate updated history) value ≤ _
  rw [model.runBehavioralTerminalFrom_eq_remaining certificate updated
    (menu.bounded (initialLaw setup) horizon scheduler) history, ← fuelEq,
    model.runBehavioralFrom_add, expect_bind_tower _ _ _ (integrable _)]
  have bounded (final : protocol.History) : |value final| ≤ 1 + |deposit who| := by
    have score := sourcePublicationGuessValue_mem_Icc setup leaks event payload outputEq high
      final.state
    have charge := TerminalAudit.charge_mem_Icc ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks backend.sample) final.state who
    dsimp only [value, TerminalAudit.utility]
    calc
      _ ≤ |sourcePublicationGuessValue setup leaks event payload outputEq high final.state| +
          |TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
            (sourceServiceAudit setup leaks backend.sample) final.state who * deposit who| :=
        by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le
              (sourcePublicationGuessValue setup leaks event payload outputEq high final.state) 0
              (TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
                (sourceServiceAudit setup leaks backend.sample) final.state who * deposit who))
      _ ≤ 1 + |deposit who| := by
        rw [abs_of_nonneg score.1, abs_mul, abs_of_nonneg charge.1]
        exact add_le_add score.2 (mul_le_of_le_one_left (abs_nonneg _) charge.2)
  apply expect_le_const _ _ (payoffIntegrable_expect_of_bounded _ _ value
    (by positivity) bounded)
  intro next supported
  have nextState : next.state =
      some ⟨remaining, none, execution.respond app who ⟨some material⟩⟩ := by
    have member : next.state ∈ ((model.runBehavioralFrom updated 1 history).map
        History.state).support := PMF.support_map .. ▸ ⟨next, supported, rfl⟩
    rw [committed] at member
    exact (PMF.mem_support_pure_iff _ _).mp member
  have path := protocol.runRandomizedFor_reachesWithin (model.randomizedChooser updated)
    1 history next supported
  have nextLength : next.trace.length = history.trace.length + 1 := by
    cases path with
    | refl => rw [current] at nextState; cases nextState
    | step joint legal realized rest =>
        have same := protocol.reachesWithin_zero_iff.mp rest
        subst next
        rfl
  have runner := model.runBehavioralTerminalFrom_eq_remaining certificate updated
    (menu.bounded (initialLaw setup) horizon scheduler) next
  have nextFuel : 2 * horizon + 1 - next.trace.length = fuel := by
    dsimp only [fuel]
    omega
  rw [nextFuel] at runner
  rw [← runner]
  let record : app.TrafficRecord :=
    ⟨execution.application.publicView, execution.network.ledger,
      ⟨(who, execution.network.nextSerial who), app.packet
        (app.submit execution.application who material) who
          (execution.network.known who) material⟩⟩
  have present : record ∈ app.stateTraffic next.state := by
    rw [nextState]
    exact (runtime setup).signed_response_traffic leaks execution who material (current ▸ rawTrace)
  have call : record.envelope.payload.call = .withhold event := by
    change (material.emit (app.submit execution.application who material) who
      (execution.network.known who)).call = _
    rw [WitnessedSubmission.emit_eq_resolve]
    exact withheld
  exact sourceService_withhold_guess_continuation_le setup leaks menu horizon scheduler completes
    updated next backend observationRate deliveryRate delivery_nonnegative coverage record present
    event payload outputEq call high deposit nonnegative sufficient

end Vegas
