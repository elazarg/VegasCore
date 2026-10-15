/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseResolutionPersistence
import Vegas.Pending.PhaseReadyRequests
import Interaction.ReactivePolicyInvariant

/-! # A genuine ready coordinate persists until physical resolution -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Automatic phase normalization retains every ready nonexcluded request,
including its physical namespace. Such an event prevents phase closure. -/
theorem SeedRequest.normalize {state : PhaseRuntimeState graph} {owner : Player}
    {coordinate : CommitAttemptEvent graph} (requested : state.SeedRequest owner coordinate) :
    state.normalize.attempt = state.attempt ∧ state.normalize.SeedRequest owner coordinate := by
  classical
  rcases state with ⟨phases, generation, entry, current, retired⟩
  cases phases with
  | nil =>
      obtain ⟨phase, installed, _⟩ := requested.2.1
      cases installed
  | cons phase remaining =>
      have inside : coordinate.event ∈ phase.events := by
        obtain ⟨actual, installed, member⟩ := requested.2.1
        have same : actual = phase := by
          change some phase = some actual at installed
          exact (Option.some.inj installed).symm
        exact same ▸ member
      have unfinished : coordinate.event ∉ (phase.drain current).native.config.cut.completed := by
        intro completed
        exact requested.2.2.1.1 ((phase.drainFuel_completed_survivor
          current.native.config.remaining current coordinate.event owner requested.2.2.2.1
            requested.2.2.2.2).mp completed)
      have notFinished : ¬ phase.Finished (phase.drain current) :=
        fun finished => unfinished (finished inside)
      have normalized : (⟨phase :: remaining, generation, entry, current, retired⟩ :
          PhaseRuntimeState graph).normalize =
          ⟨phase :: remaining, generation, entry, phase.drain current, retired⟩ := by
        simp only [PhaseRuntimeState.normalize, settle, ite_eq_right notFinished]
      rw [normalized]
      refine ⟨rfl, requested.1, requested.2.1, ?_, requested.2.2.2.1, ?_⟩
      · exact ⟨unfinished, requested.2.2.1.2.trans (phase.drain_completed current)⟩
      · simpa only [phase.drain_excluded] using requested.2.2.2.2

/-- Namespace progress and native completion progress suffice to retain the
complete request on a normalized live state, unless the coordinate resolved. -/
theorem SeedRequest.after_progress (ordered : graph.RevealRelaxedOrdered)
    {inputs : graph.Inputs} {before after : PhaseRuntimeState graph}
    (namespaceProgress : before.attempt.generation ≤ after.attempt.generation ∧
      before.attempt.phase ≤ after.attempt.phase)
    (progress : before.attempt = after.attempt → ∃ ticks,
      State.ServiceProgress inputs ticks before.current.native after.current.native)
    (frontier : after.Frontier) (live : after.Live)
    (maximal : after.phases.IsChain fun first second =>
      first.kind ≠ second.kind ∨ first.kind = .sample)
    (quiescent : ∀ event, ¬ after.current.AutomaticReady event)
    {owner : Player} {coordinate : CommitAttemptEvent graph}
    (requested : before.SeedRequest owner coordinate) :
    after.SeedRequest owner coordinate ∨ coordinate.Resolved after := by
  by_cases same : before.attempt = after.attempt
  · obtain ⟨ticks, service⟩ := progress same
    rcases service.ready_or_completed coordinate.event requested.2.2.1 with completed | ready
    · exact Or.inr (CommitAttemptEvent.Resolved.of_step coordinate before after
        requested.1 namespaceProgress
        (Or.inr completed))
    · have newRequest := after.request_of_ready ordered frontier live maximal quiescent
        coordinate.event ready owner requested.2.2.2.1
      have tag := requested.1.trans same
      have sameCoordinate : (⟨after.attempt, coordinate.event⟩ : CommitAttemptEvent graph) =
          coordinate := by
        cases coordinate with
        | mk attempt event =>
            exact congrArg (fun current => CommitAttemptEvent.mk current event) tag.symm
      exact Or.inl (sameCoordinate ▸ newRequest)
  · exact Or.inr (CommitAttemptEvent.Resolved.of_step coordinate before after
      requested.1 namespaceProgress
      (Or.inl fun tag => same (requested.1.symm.trans tag)))

end PhaseRuntimeState

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private def CoordinateStatus (inputs : graph.Inputs) (owner : Player)
    (coordinate : CommitAttemptEvent graph) (execution : (app).Execution) : Prop :=
  execution.application.Invariant inputs ∧
    (execution.application.Frontier ∧ execution.application.Live) ∧
    (execution.application.Frontier ∧
      (execution.application.phases.IsChain fun first second =>
        first.kind ≠ second.kind ∨ first.kind = .sample) ∧
      ∀ event, ¬ execution.application.current.AutomaticReady event) ∧
    (execution.application.SeedRequest owner coordinate ∨ coordinate.Resolved execution.application)

private theorem coordinateStatus_respond (ordered : graph.RevealRelaxedOrdered)
    {inputs : graph.Inputs} {owner : Player} {coordinate : CommitAttemptEvent graph}
    (execution : (app).Execution) (who : Player) (action : (app).Action)
    (valid : CoordinateStatus runtime leaks inputs owner coordinate execution) :
    CoordinateStatus runtime leaks inputs owner coordinate (execution.respond app who action) := by
  obtain ⟨nativeValid, live, geometry, status⟩ := valid
  have nativeAfter := (phaseApplication_invariant runtime leaks inputs).respond
    execution who action nativeValid
  have liveAfter := (phaseApplication_live runtime leaks).respond execution who action live
  have geometryAfter := (phaseApplication_quiescent runtime leaks ordered).respond
    execution who action geometry
  refine ⟨nativeAfter, liveAfter, geometryAfter, ?_⟩
  have planOrdered : execution.application.Ordered := live.1.adjacent
  rcases status with requested | resolved
  · exact PhaseRuntimeState.SeedRequest.after_progress ordered
      ((phaseApplication_namespace_progress runtime leaks).respond execution who action planOrdered)
      ((phaseApplication_serviceProgress runtime leaks).respond execution who action inputs
        nativeValid planOrdered)
      liveAfter.1 liveAfter.2 geometryAfter.2.1 geometryAfter.2.2 requested
  · exact Or.inr ((phaseApplication_resolution runtime leaks coordinate).respond execution who
      action inputs nativeValid planOrdered resolved)

private theorem coordinateStatus_environment (ordered : graph.RevealRelaxedOrdered)
    {inputs : graph.Inputs} {owner : Player} {coordinate : CommitAttemptEvent graph}
    (execution next : (app).Execution) (command : (app).Command)
    (valid : CoordinateStatus runtime leaks inputs owner coordinate execution)
    (reached : next ∈ (execution.environmentStep app command).support) :
    CoordinateStatus runtime leaks inputs owner coordinate next := by
  obtain ⟨nativeValid, live, geometry, status⟩ := valid
  have nativeAfter := (phaseApplication_invariant runtime leaks inputs).environmentStep
    execution next command nativeValid reached
  have liveAfter := (phaseApplication_live runtime leaks).environmentStep
    execution next command live reached
  have geometryAfter := (phaseApplication_quiescent runtime leaks ordered).environmentStep
    execution next command geometry reached
  refine ⟨nativeAfter, liveAfter, geometryAfter, ?_⟩
  have planOrdered : execution.application.Ordered := live.1.adjacent
  rcases status with requested | resolved
  · exact PhaseRuntimeState.SeedRequest.after_progress ordered
      ((phaseApplication_namespace_progress runtime leaks).environmentStep execution next command
        reached planOrdered)
      ((phaseApplication_serviceProgress runtime leaks).environmentStep execution next command
        reached inputs nativeValid planOrdered)
      liveAfter.1 liveAfter.2 geometryAfter.2.1 geometryAfter.2.2 requested
  · exact Or.inr ((phaseApplication_resolution runtime leaks coordinate).environmentStep
      execution next command reached inputs nativeValid planOrdered resolved)

/-- Arbitrary future responses, leaks and remainder commands cannot silently
remove a ready request: every supported endpoint either retains it or has
physically completed or retired that exact event coordinate. -/
theorem runRounds_request_or_resolved (ordered : graph.RevealRelaxedOrdered)
    {inputs : graph.Inputs} (scheduler : (app).Scheduler) (players : Player → (app).Policy)
    (count : Nat) (execution next : (app).Execution)
    (valid : execution.application.Invariant inputs)
    (frontier : execution.application.Frontier) (live : execution.application.Live)
    (maximal : execution.application.phases.IsChain fun first second =>
      first.kind ≠ second.kind ∨ first.kind = .sample)
    (quiescent : ∀ event, ¬ execution.application.current.AutomaticReady event)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (requested : execution.application.SeedRequest owner coordinate)
    (reached : next ∈ ((app).runRounds scheduler players count execution).support) :
    next.application.SeedRequest owner coordinate ∨ coordinate.Resolved next.application := by
  let invariant : (app).PolicyInvariant players
      (CoordinateStatus runtime leaks inputs owner coordinate) := {
    respond execution who action before _ :=
      coordinateStatus_respond runtime leaks ordered execution who action before
    environment execution next command before moved :=
      coordinateStatus_environment runtime leaks ordered execution next command before moved }
  exact (invariant.runRounds scheduler count execution next
    ⟨valid, ⟨frontier, live⟩, ⟨frontier, maximal, quiescent⟩, Or.inl requested⟩ reached).2.2.2

end Vegas.EventGraphRuntime
