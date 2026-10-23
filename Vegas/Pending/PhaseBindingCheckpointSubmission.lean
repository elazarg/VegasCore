/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingCountTransport
import Vegas.Pending.PhaseStoredCheckpoint

/-! # Physical preparations at an older saved semantic frontier -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- A preparation changes only the globally persistent catalogue. The selected
event need not yet be ready at the older saved semantic frontier. -/
theorem checkpoint_submit_state (saved current : State graph) (who : Player)
    (material : WitnessedSubmission graph) :
    ({ saved with candidates :=
      ((runtime.reactiveApplication (nativeLeaks (graph := graph))).submit current who material
        ).candidates } : State graph) =
      (runtime.reactiveApplication (nativeLeaks (graph := graph))).submit
        { saved with candidates := current.candidates } who material := by
  rcases material with ⟨⟨packet, opening⟩, evidence⟩
  cases packet with
  | commitment event candidate =>
      rcases candidate with ⟨owner, slot⟩
      cases slot <;> cases opening <;>
        by_cases same : owner = who <;>
          simp only [reactiveApplication, Submission.register, submitStep, same,
            ite_true, ite_false]
  | opening | malformed => rfl

/-- The old saved application receives the actual new preparation, without
borrowing the live event frontier or its new response observation. -/
theorem checkpoint_response_application (physical : (phaseApplication runtime leaks).Execution)
    (who : Player) (response : (phaseApplication runtime leaks).Action) :
    (checkpoint runtime leaks
      (physical.respond (phaseApplication runtime leaks) who response)).application =
      ((checkpoint runtime leaks physical).respond
        (runtime.reactiveApplication (nativeLeaks (graph := graph))) who
          (action runtime leaks response)).application := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      exact checkpoint_submit_state runtime physical.application.entry.native
        physical.application.current.native who material

/-- Remembering an eventual result does not fabricate a value or an action at
an earlier uncompleted saved event, even when that event is not ready there. -/
theorem shadow_missing_event (memory : BindingShadow graph) (state : State graph)
    (who : Player) (event : graph.EventId) (uncompleted : event ∉ state.config.cut.completed)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    (memory.rememberCompletion event action value).view (state.playerView who) =
      memory.view (state.playerView who) := by
  apply memory.rememberCompletion_unavailable
  · change graph.playerStore who state.config.store (.inr event) = none
    have absent : state.config.outputs event = none := by
      cases stored : state.config.outputs event with
      | none => rfl
      | some result =>
          have present : (state.config.outputs event).isSome := by rw [stored]; rfl
          exact False.elim (uncompleted ((state.config.output_available event).mp present))
    simp only [EventGraph.playerStore, EventGraph.Config.store_output, absent, ite_self]
  · intro recorded member same
    change recorded ∈ graph.ownCompletions who state.config.history at member
    have seen := List.mem_map.mpr ⟨recorded, (List.mem_filter.mp member).1, same⟩
    exact uncompleted ((state.config.history_exact event).mp seen)

omit [DecidableEq Player] in
/-- A genuinely ready live binding has no saved completion: every saved cell
is still present in the live store, whereas readiness excludes its own output. -/
theorem saved_uncompleted_of_ready (state : PhaseRuntimeState graph)
    (stored : state.StoredCheckpoint) (event : graph.EventId)
    (ready : state.current.native.config.cut.Ready event) :
    event ∉ state.entry.native.config.cut.completed := by
  intro completed
  have present := (state.entry.native.config.output_available event).mpr completed
  cases value : state.entry.native.config.outputs event with
  | none => simp only [value, Option.isSome_none, Bool.false_eq_true] at present
  | some result =>
      have after : state.current.native.config.outputs event = some result :=
        stored (.inr event) result value
      apply ready.1
      apply (state.current.native.config.output_available event).mp
      rw [after]
      rfl

variable {runtime leaks}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- The owner remembers its actual preparation immediately, while an eventual
completion remains absent at the saved frontier. No saved-event readiness is assumed. -/
theorem checkpoint_binding_shadow (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (serial : Nat) (first second : Option (Raw L))
    (uncompleted : event ∉ repaired.application.entry.native.config.cut.completed)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
    let sourceCall : Submission graph := ⟨.commitment event (owner, .prepared serial), first⟩
    let targetCall : Submission graph := ⟨.commitment event (owner, .prepared serial), second⟩
    let catalog := memory.shadow.rememberCandidate (.prepared serial)
      (sourceCall.candidateAfter owner
        (original.application.current.native.playerView owner).candidates (.prepared serial))
    (catalog.rememberCompletion event action value).view
        ((nativeApp.submit (checkpoint runtime leaks repaired).application owner
          ⟨targetCall, .none⟩).playerView owner) =
      (nativeApp.submit (checkpoint runtime leaks original).application owner
        ⟨sourceCall, .none⟩).playerView owner := by
  let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
  let sourceCall : Submission graph := ⟨.commitment event (owner, .prepared serial), first⟩
  let targetCall : Submission graph := ⟨.commitment event (owner, .prepared serial), second⟩
  let catalog := memory.shadow.rememberCandidate (.prepared serial)
    (sourceCall.candidateAfter owner
      (original.application.current.native.playerView owner).candidates (.prepared serial))
  have observed : memory.shadow.view
      ((checkpoint runtime leaks repaired).application.playerView owner) =
      (checkpoint runtime leaks original).application.playerView owner :=
    congrArg ReactiveApplication.PlayerView.application frame.saved.observed
  have candidateSource : (memory.shadow.view
      ((checkpoint runtime leaks repaired).application.playerView owner)).candidates =
      (original.application.current.native.playerView owner).candidates := by
    have matched := congrArg PlayerView.candidates observed
    exact matched
  have prepared := memory.shadow.rememberCandidate_submit_view runtime
    (nativeLeaks (graph := graph)) (checkpoint runtime leaks original).application
    (checkpoint runtime leaks repaired).application owner observed event serial first second
  change (memory.shadow.rememberCandidate (.prepared serial)
    (sourceCall.candidateAfter owner (memory.shadow.view
      ((checkpoint runtime leaks repaired).application.playerView owner)).candidates
        (.prepared serial))).view
      ((nativeApp.submit (checkpoint runtime leaks repaired).application owner
        ⟨targetCall, .none⟩).playerView owner) = _ at prepared
  rw [candidateSource] at prepared
  have absent : event ∉ (nativeApp.submit (checkpoint runtime leaks repaired).application owner
      ⟨targetCall, .none⟩).config.cut.completed := by
    change event ∉ (submitStep
      (targetCall.register (checkpoint runtime leaks repaired).application owner)
        owner targetCall.packet).config.cut.completed
    rw [submitStep_config, (targetCall.register_facts owner
      (checkpoint runtime leaks repaired).application).1]
    exact uncompleted
  change (catalog.rememberCompletion event action value).view _ = _
  rw [shadow_missing_event catalog _ owner event absent action value]
  exact prepared

end Vegas.EventGraphRuntime.PhaseBindingRepair
