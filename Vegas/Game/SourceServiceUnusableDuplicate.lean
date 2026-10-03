/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceUnusableProtectedCall
import Vegas.Game.SourceServiceDuplicatePackets

/-! # Sole or duplicate traffic after an initial unusable protected binding

The actual recalled initial response remains in every supplied raw continuation.
Either its identifier is still the sole owner identifier for the event, or a
second actual recorded envelope supplies a genuine duplicate pair. At complete
settlement the first case records the selected handle, and the second case has
the existing conditional observation-and-delivery collection bound.

Collection is a lower bound on the one escrow's total charge. It is not renewed
collection after earlier punishment, and it need not be certain. These are
operational and audit statements, not a continuation utility comparison.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability
  GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Every failure of the actual sole-identifier condition produces two genuine
owner traffic records. One is exactly the initial residual's bare tokened packet.
No inclusion, terminality or watcher observation is assumed for this partition. -/
theorem unusableServiceBindingResponse_sole_or_duplicate
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (execution : (application setup leaks).Execution) (who : Player)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : (runtime setup).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false)
    (response : (application setup leaks).Action)
    (unusable : unusableServiceBindingResponse setup leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) response)
    (event : (graph setup).EventId)
    (named : (runtime setup).submittedEvent? leaks response = some event)
    (control : (application setup leaks).Control)
    (currentTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (later : List (application setup leaks).PlayerEntry)
    (continued : control.execution.recall who =
      (execution.respond (application setup leaks) who response).recall who ++ later) :
    (∀ other ∈ execution.recall who ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other event (who, execution.network.nextSerial who)) ∨
      ∃ first second : (application setup leaks).TrafficRecord,
        first ∈ (application setup leaks).executionTraffic control.execution ∧
          second ∈ (application setup leaks).executionTraffic control.execution ∧
          first.envelope = ⟨(who, execution.network.nextSerial who),
            ⟨.commitment event
              (who, .prepared (execution.application.publicView.bindingCount who)),
              none, some ⟨event⟩⟩⟩ ∧
          second.envelope.sender = who ∧ first.envelope.id ≠ second.envelope.id ∧
          second.envelope.payload.call.event? (graph setup) = some event := by
  classical
  by_cases sole : ∀ other ∈ execution.recall who ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other event (who, execution.network.nextSerial who)
  · exact Or.inl sole
  right
  push Not at sole
  obtain ⟨other, otherMember, second, secondEmitted, secondOwner, secondNamed, different⟩ := sole
  obtain ⟨payload, opening, _owned, _output, _ready, _unrecorded, _fresh, _fits, _response,
    _missing, _packet, recalled, call⟩ :=
    unusableServiceBindingResponse_protected_call bounds bound execution who trace clear response
      unusable event named
  let app := application setup leaks
  let candidate : Handle (graph setup) :=
    (who, .prepared (execution.application.publicView.bindingCount who))
  let first : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(who, execution.network.nextSerial who),
      ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩
  let entry : app.PlayerEntry := ⟨execution.observe app who, response, some first⟩
  have split : control.execution.recall who = execution.recall who ++ entry :: later := by
    rw [continued, recalled, List.append_assoc]
    rfl
  have firstMember : entry ∈ control.execution.recall who := by rw [split]; simp
  have secondMember : other ∈ control.execution.recall who := by
    rw [split]
    rcases List.mem_append.mp otherMember with before | after
    · exact List.mem_append_left _ before
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ after)
  have facts := legalFacts setup leaks horizon scheduler control currentTrace
  have inputs := app.stateTraffic_inputs (initialLaw setup) horizon scheduler currentTrace
  change (app.executionTraffic control.execution).map ReactiveApplication.TrafficRecord.envelope =
    control.execution.network.inputs at inputs
  have represented (recorded : app.PlayerEntry) (member : recorded ∈ control.execution.recall who)
      (message : Message Player (WitnessedPacket (graph setup)))
      (emitted : recorded.emitted = some message) :
      ∃ record ∈ app.executionTraffic control.execution, record.envelope = message := by
    have output : message ∈ app.outputs (control.execution.recall who) :=
      List.mem_filterMap.mpr ⟨recorded, member, emitted⟩
    rw [← facts.inputs who] at output
    have actual := (List.mem_filter.mp output).1
    rw [← inputs] at actual
    exact List.mem_map.mp actual
  obtain ⟨firstRecord, firstPresent, firstEq⟩ := represented entry firstMember first call.emitted
  obtain ⟨secondRecord, secondPresent, secondEq⟩ :=
    represented other secondMember second secondEmitted
  refine ⟨firstRecord, secondRecord, firstPresent, secondPresent, firstEq,
    secondEq ▸ secondOwner, ?_, secondEq ▸ secondNamed⟩
  rw [firstEq, secondEq]
  exact Ne.symm different

/-- At complete settlement, the actual initial residual either has its accepting
receipt and used handle, or its duplicate pair gives the backend's one-time
collection bound. Authentic conditional report coverage does not imply certainty. -/
theorem unusableServiceBindingResponse_association_or_collection
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (inclusion : ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon scheduler
      bound)
    (execution : (application setup leaks).Execution) (who : Player)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : (runtime setup).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false)
    (response : (application setup leaks).Action)
    (unusable : unusableServiceBindingResponse setup leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) response)
    (event : (graph setup).EventId)
    (named : (runtime setup).submittedEvent? leaks response = some event)
    (control : (application setup leaks).Control)
    (finalTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (later : List (application setup leaks).PlayerEntry)
    (continued : control.execution.recall who =
      (execution.respond (application setup leaks) who response).recall who ++ later)
    (complete : control.execution.application.config.cut.Terminal)
    (backend : EvidenceReportService (SettledEvidence setup))
    (observationRate deliveryRate : Player → ℝ)
    (deliveryNonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate) :
    (((who, execution.network.nextSerial who), true) ∈ control.execution.receipts ∧
      control.execution.application.publicView.accepted (.inr event) =
        some (who, .prepared (execution.application.publicView.bindingCount who)) ∧
      event ∉ control.execution.application.missedEvents) ∨
      observationRate who * deliveryRate who ≤
        TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
          (sourceServiceAudit setup leaks backend.sample) (some control) who := by
  rcases unusableServiceBindingResponse_sole_or_duplicate bounds bound execution who trace clear
      response unusable event named control finalTrace later continued with sole | duplicate
  · left
    have completed : event ∈ control.execution.application.config.cut.completed := by
      rw [complete]
      exact Finset.mem_univ event
    exact unusableServiceBindingResponse_completed_association bounds bound inclusion execution
      who trace clear response unusable event named control finalTrace later continued sole
        completed
  · right
    obtain ⟨first, second, firstPresent, secondPresent, firstEq, secondOwner, different,
      secondNamed⟩ := duplicate
    exact duplicateTraffic_collection control finalTrace event who first second firstPresent
      secondPresent (by rw [firstEq]; rfl) secondOwner different (by rw [firstEq]; rfl)
        secondNamed complete backend observationRate deliveryRate deliveryNonnegative coverage

end Vegas
