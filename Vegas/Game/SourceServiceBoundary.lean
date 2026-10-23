/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceCalendarState
import Vegas.Game.SourceServiceMenu
import Vegas.Game.ServiceRoster
import Interaction.ReactiveSubmissionSerial
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactiveServiceOpportunity
import Vegas.Game.SourceServiceCheckpoint
import Vegas.Pending.ReactiveBindingTranscript

/-! # Operational boundaries for the complete source syntax

These are facts about the existing source configuration and native execution.
The registry, accepted handles and candidate catalogue may change at each
source step. Public serial accounting and actual own-response counts are
recorded alongside semantic store agreement. There is no belief, equilibrium,
or observation-factorization premise.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A completed service prefix, including its dynamic private catalogues and
all native communication memory. Pending and privately known packets are
already public at this boundary. -/
structure ServiceBoundary (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (initial : State L setup.context)
    {Γ : SourceCtx Player L} (source : Config Player L Γ)
    (refs : ContextRefs (graph setup).layout Γ) (rank : Nat)
    (execution : (application setup leaks).Execution) : Prop
    extends SourceCheckpoint setup source refs rank execution.application.config where
  invariant : EventGraphRuntime.State.Invariant (graph := graph setup)
    (setup.eventInputs initial) execution.application
  binding : execution.application.BindingInvariant
  prepared : ∀ who, execution.application.PreparedPrefix who
  represented : execution.application.CandidatesRepresented
  acceptedRecorded : execution.application.AcceptedRecorded
  recall : execution.InputRecall (application setup leaks)
  serialRecall : execution.SerialRecall (application setup leaks)
  published : execution.network.Satisfies fun message =>
    message.id ∈ execution.network.ledger.map Message.id
  serials : execution.network.SerialsBeforeNext
  accounted : ∀ who, execution.network.nextSerial who =
    Message.distinctAuthoredCount execution.network.ledger who
  counts : ∀ who, (execution.recall who).length =
    (((List.finRange (graph setup).order.eventCount).take rank).flatMap rosters).count who
  unsent : ∀ who event, rank ≤ event.val →
    (runtime setup).eventRecorded leaks (execution.recall who) event = false
  clock : execution.application.clock = clockAt rank
  timely : ∀ event, event.val = rank → ((graph setup).actor? event).isSome = true →
    execution.application.WithinDeadline (runtime setup) event

/-- Operational boundary facts depend on the actual native execution. A
source checkpoint derived from its exact conditional branch may replace the
existential source witness returned by a supported service block. -/
theorem ServiceBoundary.withSourceCheckpoint
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ Δ : SourceCtx Player L} {source : Config Player L Γ} {other : Config Player L Δ}
    {refs : ContextRefs (graph setup).layout Γ}
    {otherRefs : ContextRefs (graph setup).layout Δ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (checkpoint : SourceCheckpoint setup other otherRefs rank execution.application.config) :
    ServiceBoundary setup leaks rosters initial other otherRefs rank execution :=
  { boundary with toSourceCheckpoint := checkpoint }

/-- The complete source service starts at each actual supplied initial state.
Initial types may be correlated and the source may contain any constructor. -/
theorem serviceBoundary_initial
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (initial : State L setup.context) :
    ServiceBoundary setup leaks rosters initial (setup.initialConfig initial)
      (ContextRefs.initial setup.context (outputLayout setup.program)) 0
      (ReactiveApplication.Execution.initial (application setup leaks)
        (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial))) := by
  refine {
    toSourceCheckpoint := SourceCheckpoint.initial setup initial
    invariant := EventGraphRuntime.State.initial_invariant _
    binding := EventGraphRuntime.State.initial_bindingInvariant _
    prepared := EventGraphRuntime.State.preparedPrefix_initial _
    represented := EventGraphRuntime.State.candidatesRepresented_initial _
    acceptedRecorded := EventGraphRuntime.State.acceptedRecorded_initial _
    recall := (application setup leaks).initial_inputRecall _
    serialRecall := (application setup leaks).initial_serialRecall _
    published := ?_
    serials := MessageNetwork.SerialsBeforeNext.empty
    accounted := ?_
    counts := ?_
    unsent := ?_
    clock := rfl
    timely := ?_ }
  · exact MessageNetwork.Satisfies.empty
  · intro who
    rfl
  · intro who
    simp only [List.take_zero, List.flatMap_nil, List.count_nil]
    rfl
  · intro who event _
    rfl
  · intro event first strategic
    apply EventGraphRuntime.State.initial_withinDeadline _ (runtime setup) event _ strategic
      (runtime_deadline_pos setup event)
    have ordered := EventOrder.Cut.empty_isPrefix (graph setup).order
    have positive : 0 < (graph setup).order.eventCount := by omega
    have same : (⟨0, positive⟩ : (graph setup).EventId) = event := Fin.ext first.symm
    rw [← same]
    exact ordered.ready positive

/-- Readiness is derived from the actual completed prefix, including chance
and dynamically allocated commitment events. -/
theorem ServiceBoundary.ready {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (event : (graph setup).EventId) (atRank : event.val = rank) :
    execution.application.config.cut.Ready event :=
  (ready_iff_rank setup _ rank boundary.ordered event).mpr atRank

/-- The offset used by the local binding policy is the actual number of this
player's previous service responses, including all harmless aliases. -/
theorem ServiceBoundary.response_offset {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (event : (graph setup).EventId) (atRank : event.val = rank) (who : Player) :
    (execution.recall who).length = rosterOffset setup rosters who event := by
  rw [boundary.counts]
  simp only [rosterOffset, atRank]

/-- A ready binding uses the canonical fresh catalogue entry and has no
accepted handle yet. These are consequences of the boundary invariants, not
additional resource assumptions on the source policy. -/
theorem ServiceBoundary.binding_resources {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (event : (graph setup).EventId) (atRank : event.val = rank) (owner : Player) :
    let serial := execution.application.publicView.bindingCount owner
    reactiveFreshSlot (execution.observe (application setup leaks) owner).application =
        some serial ∧
      execution.application.candidates.lookup (owner, .prepared serial) = .fresh ∧
      execution.application.HandleUnused (owner, .prepared serial) ∧
      execution.application.accepted (.inr event) = none := by
  dsimp only
  have candidate := (boundary.prepared owner
    (execution.application.publicView.bindingCount owner)).mpr (Nat.le_refl _)
  refine ⟨(boundary.prepared owner).freshSlot (runtime setup) leaks, candidate,
    fun field associated => boundary.binding.accepted_fixed field _ associated candidate, ?_⟩
  cases associated : execution.application.accepted (.inr event) with
  | none => rfl
  | some candidate =>
      exact False.elim ((boundary.ready event atRank).1
        (boundary.binding.toAssociationInvariant.accepted_complete event candidate associated))

/-- One prepared slot per source event suffices for every binding boundary.
The count uses actual completed binding events, so earlier samples and
publications consume no private allocation capacity. -/
theorem ServiceBoundary.binding_capacity {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (bounds : MessageBounds (graph setup))
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (event : (graph setup).EventId) (atRank : event.val = rank) (who : Player) :
    execution.application.publicView.bindingCount who < bounds.candidateCount := by
  classical
  let history := execution.application.config.history.map EventGraph.Completion.event
  have absent : event ∉ history := fun present =>
    (boundary.ready event atRank).1
      ((execution.application.config.history_exact event).mp present)
  have distinct : (event :: history).Nodup :=
    List.nodup_cons.mpr ⟨absent, execution.application.config.history_nodup⟩
  have lengthBound := distinct.length_le_card
  change history.countP _ < bounds.candidateCount
  apply lt_of_le_of_lt List.countP_le_length
  simp only [List.length_cons, Fintype.card_fin] at lengthBound
  omega

/-- Passive sampling retains every boundary fact, while keeping its actual
known-envelope updates and environment record in the execution. -/
theorem ServiceBoundary.sampledActivation {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (who : Player) (sample : Finset (MessageId Player)) :
    ServiceBoundary setup leaks rosters initial source refs rank
      (execution.sampledActivation (application setup leaks) who sample) :=
  { boundary with
    published := boundary.published.learn who sample
    serials := boundary.serials.learn who sample }

/-- One actual roster block has exactly its declared number of clock ticks. -/
theorem rosterBlock_ticks (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    serviceTicks (rosterBlock setup rosters event) = event.val + 1 := by
  unfold rosterBlock
  cases (graph setup).actor? event <;>
    simp [serviceTicks, ServiceInstruction.ticks, Function.comp_def]

end Vegas
