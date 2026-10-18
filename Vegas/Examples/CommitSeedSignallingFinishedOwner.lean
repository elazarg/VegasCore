/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingProperOpening

/-! # Survival after an owner's final successful native event -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

theorem completed_of_keepsStore (before after : EventGraphRuntime.State graph)
    (keeps : KeepsStore before after) (event : graph.EventId)
    (done : event ∈ before.config.cut.completed) :
    event ∈ after.config.cut.completed := by
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
    ((before.config.output_available event).mpr done)
  exact (after.config.output_available event).mp
    (Option.isSome_iff_exists.mpr ⟨value, keeps (.inr event) value stored⟩)

private theorem excludeEvent_keeps_foreign (excluded : Finset Player) (owner : Player)
    (active : owner ∉ excluded) (event : graph.EventId)
    (foreign : graph.actor? event ≠ some owner) :
    owner ∉ RecoveryState.excludeEvent excluded event := by
  unfold RecoveryState.excludeEvent
  cases actor : graph.actor? event with
  | none => exact active
  | some other =>
      have different : owner ≠ other := by
        intro same
        exact foreign (actor.trans (congrArg some same.symm))
      simpa only [Finset.mem_insert, not_or] using And.intro different active

private theorem inclusion_keeps_finished_owner (state : RecoveryState graph)
    (native : EventGraphRuntime.State graph)
    (message : Message Player (CommitAttemptPacket graph)) (owner : Player)
    (finished : ∀ event, graph.actor? event = some owner →
      event ∈ state.native.config.cut.completed)
    (active : owner ∉ state.excluded)
    (accepted : handle runtime state.native
      ⟨message.id, message.payload.packet.call⟩ = some native) :
    owner ∉ (state.inclusionResult message.payload.packet.call native).excluded := by
  cases call : message.payload.packet.call with
  | malformed =>
      simpa only [call, RecoveryState.inclusionResult] using active
  | commitment =>
      simpa only [call, RecoveryState.inclusionResult] using active
  | opening event candidate raw =>
      have actual : handle runtime state.native
          ⟨message.id, .opening event candidate raw⟩ = some native := by
        simpa only [call] using accepted
      obtain ⟨ready, _action, _supported, _clock, _activated, _rest⟩ :=
        runtime.handle_opening_config_step state.native native message.id event candidate raw
          actual
      have foreign : graph.actor? event ≠ some owner :=
        fun acting => ready.1 (finished event acting)
      dsimp only [RecoveryState.inclusionResult]
      split
      · exact excludeEvent_keeps_foreign state.excluded owner active event foreign
      · exact active

private theorem environment_keeps_finished_owner (state : RecoveryState graph)
    (native : EventGraphRuntime.State graph) (command : EnvironmentCommand graph)
    (owner : Player)
    (finished : ∀ event, graph.actor? event = some owner →
      event ∈ state.native.config.cut.completed)
    (active : owner ∉ state.excluded) :
    owner ∉ (state.environmentResult command native).excluded := by
  cases command with
  | advanceClock => exact active
  | executeSample => exact active
  | expire event =>
      dsimp only [RecoveryState.environmentResult]
      split
      · rename_i newly
        have foreign : graph.actor? event ≠ some owner :=
          fun acting => newly.1 (finished event acting)
        exact excludeEvent_keeps_foreign state.excluded owner active event foreign
      · exact active

/-- After all of an active owner's events are complete in the publication
suffix, no future raw operation can exclude that owner. Foreign policies and
all future malformed submissions remain unrestricted. -/
theorem finished_owner_invariant (owner : Player) :
    app.Invariant (fun state => state.phases <:+ [publicationPhase] ∧
      (∀ event, graph.actor? event = some owner →
        event ∈ state.current.native.config.cut.completed) ∧
      owner ∉ state.current.excluded) where
  submit state who material valid := by
    have next := (publication_tail_store_invariant state.current.native).submit state who
      material ⟨valid.1, fun _ _ stored => stored⟩
    exact ⟨next.1, fun event acting =>
      completed_of_keepsStore state.current.native _ next.2 event (valid.2.1 event acting),
      valid.2.2⟩
  handle state message next valid accepted := by
    have stored := (publication_tail_store_invariant state.current.native).handle state message
      next ⟨valid.1, fun _ _ stored => stored⟩ accepted
    refine ⟨stored.1, fun event acting =>
      completed_of_keepsStore state.current.native next.current.native stored.2 event
        (valid.2.1 event acting), ?_⟩
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      change owner ∉ (PhaseRuntimeState.settle _ _ _ _ _).current.excluded
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).1]
      exact inclusion_keeps_finished_owner state.current native message owner valid.2.1
        valid.2.2 handled
    · cases accepted
  environment state command next valid reached := by
    have stored := (publication_tail_store_invariant state.current.native).environment state
      command next ⟨valid.1, fun _ _ stored => stored⟩ reached
    refine ⟨stored.1, fun event acting =>
      completed_of_keepsStore state.current.native next.current.native stored.2 event
        (valid.2.1 event acting), ?_⟩
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, _supported, rfl⟩ := PMF.support_map .. ▸ reached
      change owner ∉ (PhaseRuntimeState.settle _ _ _ _ _).current.excluded
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).1]
      exact environment_keeps_finished_owner state.current native command owner valid.2.1
        valid.2.2
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid.2.2

/-- The owner's survival holds on every actual supported whole continuation,
without any optimality or properness assumption about later responses. -/
theorem finished_owner_run_survives (selected : app.Scheduler)
    (players : Player → app.Policy) (count : Nat) (before after : app.Execution)
    (owner : Player) (tail : before.application.phases <:+ [publicationPhase])
    (finished : ∀ event, graph.actor? event = some owner →
      event ∈ before.application.current.native.config.cut.completed)
    (active : owner ∉ before.application.current.excluded)
    (supported : after ∈ (app.runRounds selected players count before).support) :
    owner ∉ after.application.current.excluded := by
  have final := ((finished_owner_invariant owner).policyInvariant app players).runRounds
    selected count before after ⟨tail, finished, active⟩ supported
  exact final.2.2


/-- In this graph the owner's binding is a predecessor of its only reveal,
so completing that reveal completes every event owned by that player. -/
theorem own_events_completed_of_reveal (config : graph.Config) (owner : Player)
    (done : revealEvent owner ∈ config.cut.completed) :
    ∀ event, graph.actor? event = some owner → event ∈ config.cut.completed := by
  fin_cases owner
  · change aliceReveal ∈ config.cut.completed at done
    intro event acting
    fin_cases event
    · exact config.cut.predecessor_closed done (by
        rw [reveal_predecessors.1]
        exact Finset.mem_insert_self _ _)
    · change some bob = some alice at acting
      norm_num [bob, alice] at acting
    · exact done
    · change some bob = some alice at acting
      norm_num [bob, alice] at acting
  · change bobReveal ∈ config.cut.completed at done
    intro event acting
    fin_cases event
    · change some alice = some bob at acting
      norm_num [bob, alice] at acting
    · exact config.cut.predecessor_closed done (by
        rw [reveal_predecessors.2]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · change some alice = some bob at acting
      norm_num [bob, alice] at acting
    · exact done

theorem successful_opening_not_failed (native : EventGraphRuntime.State graph)
    (owner : Player) (value : Bool)
    (output : native.config.outputs (revealEvent owner) = some
      (cast (congrArg EventField.Value (revealEvent_layout owner).symm)
        (PublicationResult.success value))) :
    RecoveryState.publicationFailed native (revealEvent owner) = false := by
  cases node : nodeView graph (revealEvent owner) with
  | bind author payload kind code => cases kind.symm.trans (revealEvent_layout owner)
  | sample payload law kind code => cases kind.symm.trans (revealEvent_layout owner)
  | resolve author payload binding checks kind code =>
      have same := EventField.publication.inj (kind.symm.trans (revealEvent_layout owner))
      subst payload
      rw [RecoveryState.publicationFailed, node, output]
      simp only [cast_cast, cast_eq]

/-- A genuine counted truthful opening, when selected by its real network
identifier while ready and timely, makes its owner immune to every later raw
exclusion. The normalized state may already have completed the entire graph. -/
theorem counted_successful_opening_finished
    (sourceScheduler : app.Scheduler) (control : app.Control)
    (trace : (countedMenu.protocol initial horizon sourceScheduler).Trace (some control))
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ control.execution.network.inputs)
    (lookup : control.execution.network.lookup message.id = some message)
    (candidate : Handle graph) (raw : Raw simpleExpr)
    (opening : message.payload.packet.call = .opening (revealEvent owner) candidate raw)
    (request : control.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, revealEvent owner⟩)
    (timely : control.execution.application.current.native.WithinDeadline runtime
      (revealEvent owner)) (value : Bool)
    (stored : control.execution.application.current.native.config.store
      (.inr (bindingEvent owner)) = some
        (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
          (PublicationResult.success value)))
    (nextExecution : app.Execution)
    (includedStep : nextExecution ∈
      (control.execution.environmentStep app (.include message.id)).support) :
    nextExecution.application.phases <:+ [publicationPhase] ∧
      (∀ event, graph.actor? event = some owner →
        event ∈ nextExecution.application.current.native.config.cut.completed) ∧
      owner ∉ nextExecution.application.current.excluded := by
  classical
  have ready : control.execution.application.current.native.config.cut.Ready
      (revealEvent owner) := request.2.2.1
  have predecessors : graph.order.predecessors (revealEvent owner) =
      {aliceBinding, bobBinding} := by
    unfold revealEvent
    split
    · exact reveal_predecessors.1
    · exact reveal_predecessors.2
  have aliceDone : aliceBinding ∈
      control.execution.application.current.native.config.cut.completed :=
    ready.2 (by rw [predecessors]; exact Finset.mem_insert_self _ _)
  have bobDone : bobBinding ∈
      control.execution.application.current.native.config.cut.completed :=
    ready.2 (by rw [predecessors]
                exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have tail := completed_bindings_publication_tail sourceScheduler control
    (countedMenu.toRawTrace initial horizon sourceScheduler trace) aliceDone bobDone
  obtain ⟨native, next, _handled, completed, output, normalized, phaseHandled⟩ :=
    counted_successful_opening_accepted sourceScheduler control trace owner message member candidate
      raw opening request timely value stored
  have nativeKeeps : KeepsStore native next.current.native := by
    rw [normalized]
    exact settle_publication_keepsStore control.execution.application.phases
      control.execution.application.generation control.execution.application.entry
      (control.execution.application.current.inclusionResult message.payload.packet.call native)
      control.execution.application.retired tail
  have nextTail : next.phases <:+ [publicationPhase] := by
    rw [normalized]
    exact (PhaseRuntimeState.settle_suffix _ _ _ _ _).trans tail
  have finished : ∀ event, graph.actor? event = some owner →
      event ∈ next.current.native.config.cut.completed := by
    intro event acting
    exact completed_of_keepsStore native next.current.native nativeKeeps event
      (own_events_completed_of_reveal native.config owner completed event acting)
  have actor : graph.actor? (revealEvent owner) = some owner := by
    fin_cases owner <;> rfl
  have sender : message.sender = owner :=
    Option.some.inj (request.2.2.2.1.symm.trans actor)
  have beforeActive : owner ∉ control.execution.application.current.excluded := by
    simpa only [sender] using request.2.2.2.2
  have noFailure := successful_opening_not_failed native owner value output
  have active : owner ∉ next.current.excluded := by
    rw [normalized]
    change owner ∉ (PhaseRuntimeState.settle _ _ _ _ _).current.excluded
    rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).1]
    simp only [opening, RecoveryState.inclusionResult, noFailure, Bool.false_eq_true,
      ↓reduceIte]
    exact beforeActive
  have included : (control.execution.includePending app message.id).application = next := by
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      lookup, phaseHandled, Option.getD_some]
  have actualApplication : nextExecution.application = next := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at includedStep
    cases (PMF.mem_support_pure_iff _ _).mp includedStep
    exact included
  refine ⟨?_, ?_, ?_⟩
  · rwa [actualApplication]
  · rwa [actualApplication]
  · rwa [actualApplication]

/-- The actual successful inclusion makes its owner safe for every later
raw continuation, with source and future schedulers independent. -/
theorem counted_successful_opening_future_survives
    (sourceScheduler : app.Scheduler) (control : app.Control)
    (trace : (countedMenu.protocol initial horizon sourceScheduler).Trace (some control))
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ control.execution.network.inputs)
    (lookup : control.execution.network.lookup message.id = some message)
    (candidate : Handle graph) (raw : Raw simpleExpr)
    (opening : message.payload.packet.call = .opening (revealEvent owner) candidate raw)
    (request : control.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, revealEvent owner⟩)
    (timely : control.execution.application.current.native.WithinDeadline runtime
      (revealEvent owner)) (value : Bool)
    (stored : control.execution.application.current.native.config.store
      (.inr (bindingEvent owner)) = some
        (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
          (PublicationResult.success value)))
    (nextExecution : app.Execution)
    (includedStep : nextExecution ∈
      (control.execution.environmentStep app (.include message.id)).support)
    (selected : app.Scheduler) (players : Player → app.Policy) (count : Nat)
    (after : app.Execution)
    (supported : after ∈ (app.runRounds selected players count nextExecution).support) :
    owner ∉ after.application.current.excluded := by
  obtain ⟨tail, finished, active⟩ := counted_successful_opening_finished sourceScheduler control
    trace owner message member lookup candidate raw opening request timely value stored
      nextExecution includedStep
  exact finished_owner_run_survives selected players count nextExecution after owner tail finished
    active supported

end Vegas.Examples.CommitSeedSignalling
