/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastCountedSeedTrace
import Vegas.Examples.CommitSeedBroadcastTailRecall
import Vegas.Examples.CommitSeedBroadcastProperPolicy
import Vegas.Pending.PhaseBindingIdleMenu
import Vegas.Pending.PhaseOpeningMenuShape
import Vegas.Pending.PhaseBindingFreshness
import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseRecordedCountedRequest

/-! # Unsubmitted coordinates at genuine continuation callbacks -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem coordinate_eq_of_fields (left right : CommitAttemptEvent graph)
    (tags : left.attempt = right.attempt) (names : left.event = right.event) : left = right := by
  cases left
  cases right
  cases tags
  cases names
  rfl

private theorem recalled_coordinate_fields (seed : Seeds) (current : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall owner)
    (material : app.Submission) (transmitted : entry.action.transmission = some material)
    (message : Message Player (CommitAttemptPacket graph)) (emitted : entry.emitted = some message)
    (coordinate : CommitAttemptEvent graph)
    (named : PhaseCount.event? message.payload = some coordinate) :
    coordinate.attempt = entry.beforeView.application.2.attempt ∧
      material.call.packet.event? graph = some coordinate.event := by
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  obtain ⟨produced, recalled, _sender, call⟩ := PhaseCount.recalled_submission_emitted runtime leaks
    initial horizon (family seed) raw owner entry recorded material transmitted
  have same : produced = message := Option.some.inj (recalled.symm.trans emitted)
  rw [same] at call
  change ((message.payload.packet.call.event? graph).map fun event =>
    (⟨message.payload.attempt, event⟩ : CommitAttemptEvent graph)) = some coordinate at named
  obtain ⟨event, found, coordinateEq⟩ := Option.map_eq_some_iff.mp named
  have attempt := phase_recalled_emission_attempt runtime leaks initial horizon (family seed)
    raw owner entry recorded message emitted
  refine ⟨(congrArg CommitAttemptEvent.attempt coordinateEq).symm.trans attempt, ?_⟩
  rw [← call, found]
  exact congrArg (fun event => some event) (congrArg CommitAttemptEvent.event coordinateEq)

private theorem recorded_coordinate_request (seed : Seeds) (current : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall owner)
    (material : app.Submission) (transmitted : entry.action.transmission = some material)
    (message : Message Player (CommitAttemptPacket graph)) (emitted : entry.emitted = some message)
    (coordinate : CommitAttemptEvent graph)
    (named : PhaseCount.event? message.payload = some coordinate) :
    PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate := by
  have compiledTrace := trace
  rw [initial_eq_compiled] at compiledTrace
  obtain ⟨actual, requested, attempt, event⟩ := PhaseCount.recorded_material_request runtime leaks
    bounds plan (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
    (setup.initialLaw.map encodeInputs) horizon (family seed) current compiledTrace owner entry
      recorded
      material transmitted
  have fields := recalled_coordinate_fields seed current trace owner entry recorded material
    transmitted message emitted coordinate named
  have same := coordinate_eq_of_fields actual coordinate (attempt.trans fields.1.symm)
    (Option.some.inj (event.symm.trans fields.2))
  exact same ▸ requested

private theorem fixed_tail_callback_no_previous_request (menu : app.ResponseMenu)
    (silence : ∀ owner past view, (⟨none⟩ : app.Action) ∈ menu.actions owner past view)
    (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (owner : Player)
    (trace : (menu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (coordinate : CommitAttemptEvent graph) (retired : coordinate.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner coordinate)
    (entry : app.PlayerEntry) (member : entry ∈ execution.recall owner)
    (previous : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate) :
    False := by
  classical
  obtain ⟨responded⟩ := menu.trace_respond initial horizon (family seed) remaining execution
    owner ⟨none⟩ trace (silence owner _ _)
  let last : app.PlayerEntry := ⟨execution.observe app owner, ⟨none⟩, none⟩
  have publicRequest : PhaseRuntimeState.requests last.beforeView.application.2 owner
      coordinate :=
    (execution.application.requests_publicView
      (raw_native_valid (family seed) _
        (menu.toRawTrace initial horizon (family seed) trace)) owner coordinate).mpr request
  obtain ⟨earlier, later, recalled⟩ := List.mem_iff_append.mp member
  have full : (execution.respond app owner ⟨none⟩).recall owner =
      earlier ++ entry :: (later ++ last :: []) := by
    simp only [ReactiveApplication.Execution.respond]
    change execution.recall owner ++ [last] = _
    rw [recalled]
    simp only [List.append_assoc, List.cons_append]
  exact tail_recalled_callbacks_no_repeat menu silence seed
    ⟨remaining, none, execution.respond app owner ⟨none⟩⟩ responded coordinate owner retired
      earlier later [] entry last full previous publicRequest

/-- An actual requested continuation callback has no earlier recalled response
for the same coordinate, even on an off-path raw history. -/
theorem tail_callback_no_previous_request (menu : app.ResponseMenu)
    (silence : ∀ owner past view, (⟨none⟩ : app.Action) ∈ menu.actions owner past view)
    (remaining : Nat) (execution : app.Execution)
    (owner : Player)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (coordinate : CommitAttemptEvent graph) (retired : coordinate.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner coordinate)
    (entry : app.PlayerEntry) (member : entry ∈ execution.recall owner)
    (previous : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate) :
    False := by
  obtain ⟨seed, ⟨fixed⟩⟩ := menu_trace_fixed_seed menu silence
    ⟨remaining, some owner, execution⟩ trace
  exact fixed_tail_callback_no_previous_request menu silence seed remaining execution owner fixed
    coordinate retired request entry member previous

theorem fixed_tail_callback_unsubmitted (seed : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (coordinate : CommitAttemptEvent graph) (retired : coordinate.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner coordinate) :
    ∀ message ∈ execution.network.inputs, message.sender = owner →
      PhaseCount.event? message.payload ≠ some coordinate := by
  classical
  intro message member sender named
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have provenance := app.history_provenance initial horizon (family seed) raw
  obtain ⟨entry, recalledEntry, material, transmitted, emitted, _packet⟩ :=
    provenance.inputs message member
  rw [sender] at recalledEntry
  have firstRequest := recorded_coordinate_request seed ⟨remaining, some owner, execution⟩ trace
    owner entry recalledEntry material transmitted message emitted coordinate named
  exact fixed_tail_callback_no_previous_request countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) seed remaining execution owner trace
      coordinate retired request entry recalledEntry firstRequest

/-- The original counted callback has no earlier owned packet for its full
coordinate. This includes off-path histories and arbitrary retired traffic;
no posterior-support or successful-preparation assumption is used. -/
theorem counted_tail_callback_unsubmitted (remaining : Nat) (execution : app.Execution)
    (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (coordinate : CommitAttemptEvent graph) (retired : coordinate.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner coordinate) :
    ∀ message ∈ execution.network.inputs, message.sender = owner →
      PhaseCount.event? message.payload ≠ some coordinate := by
  obtain ⟨seed, ⟨fixed⟩⟩ := menu_trace_fixed_seed countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) ⟨remaining, some owner, execution⟩ trace
  exact fixed_tail_callback_unsubmitted seed remaining execution owner fixed coordinate retired
    request

end Vegas.Examples.CommitSeedBroadcast
