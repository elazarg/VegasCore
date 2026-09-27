/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingCheckpoint
import Vegas.Game.RevealServiceCalendarState
import Vegas.Pending.ReactiveBindingPrefix
import Interaction.ReactiveSubmissionSerial
import Vegas.Pending.ReactiveServiceRecall
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactiveServiceOpportunity

/-! # Operational boundaries for the complete source syntax

These are facts about the existing source configuration and native execution.
The registry, accepted handles and candidate catalogue may change at each
source step. Public serial accounting and actual own-response counts are
recorded alongside semantic store agreement. There is no belief, equilibrium,
or observation-factorization premise.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A completed service prefix, including its dynamic private catalogues and
all native communication memory. Pending and privately known packets are
already public at this boundary; their copies are retained. -/
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
    execution.network.ledger.countP (fun message => message.sender = who)
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

/-- The actual grant command records the environment transition while leaving
every completed-prefix fact intact. -/
theorem ServiceBoundary.grant {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) (event : (graph setup).EventId) :
    ∃ granted, ServiceBoundary setup leaks rosters initial source refs rank granted ∧
      granted.application.serviceGrant = some event ∧
      granted.application = { execution.application with serviceGrant := some event } ∧
      granted.recall = execution.recall ∧
      (runtime setup).interactionStep leaks players network (.grant event) execution =
        FinDist.pure granted := by
  let app := application setup leaks
  let granted : app.Execution := { execution with
    application := { execution.application with serviceGrant := some event }
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application (.grant event)⟩] }
  refine ⟨granted, ?_, rfl, rfl, rfl, ?_⟩
  · exact { boundary with
      invariant := boundary.invariant.copy rfl rfl rfl
      binding := boundary.binding.copy rfl rfl rfl }
  · simp only [interactionStep, interactionInstruction, FinDist.pure_bind]
    change (execution.environmentStep app (.application (.grant event))).bind FinDist.pure = _
    rw [FinDist.bind_pure]
    simp only [ReactiveApplication.Execution.environmentStep,
      app, application, reactiveApplication, environmentStep, FinDist.map_pure]
    rfl

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

/-- Core runtime invariants hold after every supported actual continuation,
including raw responses. They need not be established separately in each
source constructor. -/
theorem ServiceBoundary.run_core {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (plan : List (ServiceInstruction (graph setup)))
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network plan
      execution).support) :
    EventGraphRuntime.State.Invariant (graph := graph setup)
        (setup.eventInputs initial) final.application ∧
      final.application.BindingInvariant ∧ final.InputRecall (application setup leaks) ∧
      final.SerialRecall (application setup leaks) ∧ final.network.SerialsBeforeNext := by
  let app := application setup leaks
  refine ⟨?_, ?_, (runtime setup).runInteractionPlan_inputRecall leaks players network plan
    execution final boundary.recall reached, ?_,
      (runtime setup).runInteractionPlan_serials leaks players network plan execution final
        boundary.serials reached⟩
  · exact (runtime setup).runInteractionPlan_preserves leaks players network _
      (ReactiveApplication.Invariant.policyInvariant app
        ((runtime setup).reactiveStateInvariant leaks (setup.eventInputs initial)) players)
      plan execution final boundary.invariant reached
  · exact (runtime setup).runInteractionPlan_preserves leaks players network _
      (ReactiveApplication.Invariant.policyInvariant app
        ((runtime setup).reactiveBindingInvariant leaks) players)
      plan execution final boundary.binding reached
  · have preserved : app.PolicyInvariant players (fun state => state.SerialRecall app) := {
      respond := fun state who response valid _ => app.respond_serialRecall state who response valid
      environment := app.environment_serialRecall }
    exact (runtime setup).runInteractionPlan_preserves leaks players network _ preserved plan
      execution final boundary.serialRecall reached

/-- Finishing the real roster advances every player's response offset by
exactly the number of their scheduled opportunities, independently of actions. -/
theorem ServiceBoundary.roster_counts {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (atRank : event.val = rank)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (rosterBlock setup rosters event) execution).support) (who : Player) :
    (final.recall who).length = List.count who
      (((List.finRange (graph setup).order.eventCount).take (rank + 1)).flatMap rosters) := by
  rw [fixed_plan_response_counts setup leaks network players _
    (rosterBlock_no_wire setup rosters event) execution final reached who,
      rosterBlock_actors, boundary.counts]
  have counts := congrArg (fun plan => (plan.filterMap instructionActor).count who)
    (rosterPlanPrefix_succ setup rosters event)
  simpa only [List.filterMap_append, rosterPlanPrefix_actors, rosterBlock_actors,
    List.count_append, atRank] using counts.symm

/-- One actual roster block has exactly its declared number of clock ticks. -/
theorem rosterBlock_ticks (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    serviceTicks (rosterBlock setup rosters event) = event.val + 1 := by
  unfold rosterBlock
  cases (graph setup).actor? event <;>
    simp [serviceTicks, ServiceInstruction.ticks, Function.comp_def]

/-- Every actual completed roster block leaves its successor timely. Only
the completed cut is constructor-specific: clock advancement and activation
age follow from the existing runtime transition laws for arbitrary policies. -/
theorem ServiceBoundary.roster_successor_timing
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (atRank : event.val = rank)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (rosterBlock setup rosters event) execution).support)
    (ordered : final.application.config.cut.IsPrefix (rank + 1)) :
    final.application.clock = clockAt (rank + 1) ∧
      ∀ next, next.val = rank + 1 → ((graph setup).actor? next).isSome = true →
        final.application.WithinDeadline (runtime setup) next := by
  have progress := (runtime setup).runInteractionPlan_facts leaks (setup.eventInputs initial)
    players network (rosterBlock setup rosters event) execution final boundary.invariant reached
  have advanced : final.application.clock = execution.application.clock + (rank + 1) := by
    simpa only [rosterBlock_ticks, atRank] using progress.clock
  refine ⟨by rw [advanced, boundary.clock, clockAt_succ], ?_⟩
  intro next nextRank strategic
  have ready := (ready_iff_rank setup _ (rank + 1) ordered next).mpr nextRank
  obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp
    ((progress.invariant.activated_iff next).mpr ⟨ready, strategic⟩)
  have origin := (runtime setup).runInteractionPlan_activationOrigin leaks
    (setup.eventInputs initial) players network (rosterBlock setup rosters event)
      execution final boundary.invariant reached
  have lower : execution.application.clock ≤ entered := by
    rcases origin next entered activated ready.1 with retained | recent
    · have beforeReady := ((boundary.invariant.activated_iff next).mp
        (Option.isSome_iff_exists.mpr ⟨entered, retained⟩)).1
      have same := (ready_iff_rank setup _ rank boundary.ordered next).mp beforeReady
      omega
    · exact recent
  unfold EventGraphRuntime.State.WithinDeadline
  rw [activated, advanced]
  change execution.application.clock + (rank + 1) - entered < next.val + 1
  omega

end Vegas.SourceProgram.RevealService
