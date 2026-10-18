/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPublicationAfterSubmission
import Vegas.Examples.CommitSeedBroadcastTailDecision
import Vegas.Examples.CommitSeedBroadcastProperBindingRecords
import Vegas.Pending.EventHandleObservation

/-! # Truthful opening availability and own-value observation at protected callbacks -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- A successful binding is visible to its owner, independently of every
foreign private field in the two compared physical histories. -/
theorem binding_store_eq_of_owner_view
    (left right : EventGraphRuntime.State graph) (owner : Player)
    (views : left.playerView owner = right.playerView owner) :
    left.config.store (.inr (bindingEvent owner)) =
      right.config.store (.inr (bindingEvent owner)) := by
  have stores := congrArg PlayerObservation.store
    (left.playerView_observation_eq right owner views)
  have visible : graph.fieldVisibleTo owner (.inr (bindingEvent owner)) := by
    change (graph.layout (.inr (bindingEvent owner))).VisibleTo owner
    rw [bindingEvent_layout]
    simp only [EventField.VisibleTo]
  exact (graph.playerStore_of_visible owner left.config.store _ visible).symm.trans
    ((congrFun stores (.inr (bindingEvent owner))).trans
      (graph.playerStore_of_visible owner right.config.store _ visible))

/-- The actual tail timer makes every genuine publication callback timely. -/
theorem counted_tail_request_timely
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (coordinate : CommitAttemptEvent graph) (retired : coordinate.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner coordinate) :
    execution.application.current.native.WithinDeadline runtime coordinate.event := by
  obtain ⟨seed, ⟨fixed⟩⟩ := menu_trace_fixed_seed countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) _ trace
  exact family_tail_ready_timely seed remaining execution owner fixed coordinate retired request

/-- A surviving successful binding at a real publication callback supplies
an actual legal truthful opening, with no assumed candidate or menu witness. -/
theorem counted_tail_truthful_opening_available
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value))) :
    ∃ candidate, PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
      ⟨.bool, value⟩ ∈ countedMenu.actions owner (execution.recall owner)
        (execution.observe app owner) := by
  classical
  have unsubmitted := counted_tail_callback_unsubmitted remaining execution owner trace
    ⟨execution.application.attempt, revealEvent owner⟩ retired request
  have recalledInputs := PhaseCount.countRecall_history runtime leaks
    (countedMenu.toRawTrace initial horizon scheduler trace)
  have unsent (message : Message Player (CommitAttemptPacket graph))
      (member : message ∈ app.outputs (execution.recall owner)) :
      PhaseCount.event? message.payload ≠
        some ⟨execution.application.attempt, revealEvent owner⟩ := by
    rw [← recalledInputs.1 owner] at member
    exact unsubmitted message (List.mem_filter.mp member).1
      (of_decide_eq_true (List.mem_filter.mp member).2)
  have typed : (ownBindingRef owner).get? execution.application.current.native.config.store =
      some (.success value) := by
    fin_cases owner <;> exact stored
  obtain ⟨checks, codeEq, node⟩ := own_reveal_descriptor owner
  obtain ⟨candidate, _accepted, literal⟩ := properPolicy_opening_response
    (fun _ _ _ => true) scheduler ⟨remaining, some owner, execution⟩ trace owner (revealEvent owner)
      (ownBindingRef owner) checks (revealEvent_layout owner) codeEq node request unsent value typed
  refine ⟨candidate, ?_⟩
  apply properPolicy_counted (fun _ _ _ => true) owner _ _ _
  rw [literal]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

end Vegas.Examples.CommitSeedBroadcast
