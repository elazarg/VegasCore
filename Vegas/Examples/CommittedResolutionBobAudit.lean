/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommittedResolutionBobService
import Interaction.ReactiveProvenance
import Interaction.ReactiveTrafficState
import Interaction.ReactiveRawRoundTrace

/-! # Actual zero-charge truthful response after arbitrary RAW prefixes

Bob has no prior response at his sole native activation. His canonical response
therefore accounts for every packet attributed to him along the passive suffix.
Authentic sampling of actual traffic collects no Bob charge. Earlier Alice
traffic is unrestricted; no clean-prefix assumption is needed.
-/

noncomputable section

namespace Vegas.Examples.CommittedResolutionBobAudit

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Enforcement
open CommittedResolutionService CommittedResolutionReadout CommittedResolutionBobService

/-- No retained input was authored by Bob before his one activation. -/
theorem bob_prefix_no_inputs (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob)
    (message : Message Player (WitnessedPacket nativeGraph))
    (present : message ∈ control.execution.network.inputs) : message.sender ≠ bob := by
  intro owned
  have provenance := app.history_provenance (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler trace
  obtain ⟨entry, recalled, _⟩ := provenance.inputs message present
  have empty := (recovery_bob_phase control trace active).2.2.1
  rw [owned, empty] at recalled
  simp at recalled

/-- Canonical TRUE is Bob's only packet throughout every future RAW suffix. -/
theorem canonical_bob_owner_inputs (players : Player → app.Policy) (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) :
    ∃ material : WitnessedSubmission nativeGraph, ∃ next : app.Execution,
      (runtime setup).canonicalServiceDecision leaks bob (control.execution.recall bob)
        (control.execution.observe app bob) bobEvent true = ⟨some material⟩ ∧
      app.round CommittedResolutionRecovery.scheduler players
        (control.execution.respond app bob ⟨some material⟩) = PMF.pure next ∧
      ∀ (future : Player → app.Policy) (count : Nat) (final : app.Execution),
        final ∈ (app.runRounds CommittedResolutionRecovery.scheduler future count next).support →
        final.application.config.store (.inr bobEvent) = some (.success true) ∧
        ((bobMessage control.execution).id, true) ∈ final.receipts ∧
        ∀ message ∈ final.network.inputs, message.sender = bob →
          message = bobMessage control.execution := by
  obtain ⟨material, next, decision, moved, published, accepted, _⟩ :=
    canonical_bob_round players control trace active
  obtain ⟨honest, canonical, _unchanged, packet, _⟩ :=
    canonical_bob_response control trace active
  have same : material = honest := by
    exact Option.some.inj (congrArg ReactiveApplication.Action.transmission
      (decision.symm.trans canonical))
  subst honest
  have cursor :
      11 ≤ (control.execution.respond app bob ⟨some material⟩).environmentRecall.length := by
    rw [app.respond_environmentRecall, (recovery_bob_phase control trace active).1]
  have nextReached : next ∈ (app.round CommittedResolutionRecovery.scheduler players
      (control.execution.respond app bob ⟨some material⟩)).support := by
    rw [moved]
    simp
  have retained := recovery_suffix_preserves_traffic players 1
    (control.execution.respond app bob ⟨some material⟩) next cursor
    (by simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using nextReached)
  have nextCursor : 11 ≤ next.environmentRecall.length := by
    have length := app.round_environmentRecall_length CommittedResolutionRecovery.scheduler players
      (control.execution.respond app bob ⟨some material⟩) next nextReached
    omega
  have nextInputs : next.network.inputs =
      List.append control.execution.network.inputs [bobMessage control.execution] := by
    rw [retained.2]
    change (control.execution.network.submit bob
      (app.packet (app.submit control.execution.application bob material) bob
        (control.execution.network.known bob) material)).2.inputs = _
    rw [packet]
    rfl
  refine ⟨material, next, decision, moved, ?_⟩
  intro future count final reached
  obtain ⟨output, receipt, _⟩ := bob_accepted_suffix future
    CommittedResolutionRecovery.scheduler count next final control.execution published accepted
    reached
  refine ⟨output, receipt, ?_⟩
  intro message member owned
  rw [(recovery_suffix_preserves_traffic future count next final nextCursor reached).2,
    nextInputs] at member
  rcases List.mem_append.mp member with earlier | same
  · exact False.elim (bob_prefix_no_inputs control trace active message earlier owned)
  · exact List.mem_singleton.mp same

/-- The actual audit charges Bob zero whenever all his input envelopes are his
accepted truthful opening. The premise concerns native retained traffic, not a
desired utility comparison. -/
theorem bob_audit_clear_of_only_opening (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (origin : app.Execution)
    (accepted : ((bobMessage origin).id, true) ∈ control.execution.receipts)
    (only : ∀ message ∈ control.execution.network.inputs, message.sender = bob →
      message = bobMessage origin)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) (some control) bob = 0 := by
  have clear : control.execution.application.publicView.missedBindingBy bob = false := by
    apply PublicView.missedBindingBy_of_publications
    intro event owner payload
    fin_cases event <;> intro equal <;> cases equal
  unfold sourceServiceAudit serviceSourceAudit
  rw [(runtime setup).serviceAudit_charge, clear]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply app.sampledTrafficAudit_sound
  · exact authentic _
  · intro record member owner
    have inputs := app.stateTraffic_inputs (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler trace
    change (app.executionTraffic control.execution).map
      ReactiveApplication.TrafficRecord.envelope = control.execution.network.inputs at inputs
    have present : record.envelope ∈ control.execution.network.inputs := by
      rw [← inputs]
      exact List.mem_map.mpr ⟨record, member, rfl⟩
    have same := only record.envelope present owner
    change ((runtime setup).settledRecord leaks control.execution).permits record.envelope = true
    rw [same]
    exact bob_message_permitted origin _ accepted

/-- Canonical TRUE has zero actual owner charge throughout its remaining
physical continuation after every legal RAW Bob prefix. Future policies and
all earlier Alice submissions are unrestricted. -/
theorem canonical_bob_audit_clear (players : Player → app.Policy)
    (remaining : Nat) (execution : app.Execution)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace
        (some ⟨remaining + 1, some bob, execution⟩))
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    ∃ material : WitnessedSubmission nativeGraph, ∃ next : app.Execution,
      (runtime setup).canonicalServiceDecision leaks bob (execution.recall bob)
        (execution.observe app bob) bobEvent true = ⟨some material⟩ ∧
      app.round CommittedResolutionRecovery.scheduler players
        (execution.respond app bob ⟨some material⟩) = PMF.pure next ∧
      ∀ (future : Player → app.Policy) (count : Nat), count ≤ remaining →
        ∀ final ∈ (app.runRounds CommittedResolutionRecovery.scheduler future count next).support,
        final.application.config.store (.inr bobEvent) = some (.success true) ∧
        TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
          (sourceServiceAudit setup leaks sample)
            (some ⟨remaining - count, none, final⟩) bob = 0 := by
  obtain ⟨material, next, decision, moved, only⟩ :=
    canonical_bob_owner_inputs players ⟨remaining + 1, some bob, execution⟩ trace rfl
  obtain ⟨responded⟩ := app.raw_trace_respond (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler
      (remaining + 1) execution bob ⟨some material⟩ trace
  have nextReached : next ∈ (app.round CommittedResolutionRecovery.scheduler players
      (execution.respond app bob ⟨some material⟩)).support := by
    rw [moved]
    simp
  obtain ⟨nextTrace⟩ := app.raw_trace_round (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler players
      remaining _ next responded nextReached
  refine ⟨material, next, decision, moved, ?_⟩
  intro future count within final reached
  obtain ⟨output, receipt, unique⟩ := only future count final reached
  have startTrace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace
        (some ⟨(remaining - count) + count, none, next⟩) := by
    simpa only [Nat.sub_add_cancel within] using nextTrace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler future
      (remaining - count) count next final startTrace reached
  exact ⟨output, bob_audit_clear_of_only_opening ⟨remaining - count, none, final⟩
    finalTrace execution receipt unique sample authentic⟩

end Vegas.Examples.CommittedResolutionBobAudit
