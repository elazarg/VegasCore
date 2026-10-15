/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedRecall
import Vegas.Pending.PhaseCountMenu
import Interaction.ReactiveServiceRounds

/-! # A phased source choice is sampled only at its first callback

Own recall records silence as well as packets. Repeated callbacks therefore
cannot redraw a sampled physical omission; a new attempt remains a new choice.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Own recall contains a response to this exact physical coordinate,
including a response that deliberately emitted nothing. -/
def ResponseRecorded (owner : Player) (coordinate : CommitAttemptEvent graph)
    (past : List (app).PlayerEntry) : Prop :=
  ∃ entry ∈ past, PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate

open Classical in
/-- The first callback uses the prescribed law; every subsequent callback
in the same physical namespace is silent. -/
def phaseOncePolicy (owner : Player) (event : graph.EventId) (policy : (app).Policy) :
    (app).Policy := fun past view =>
  if ResponseRecorded runtime leaks owner ⟨view.application.2.attempt, event⟩ past then
    PMF.pure ⟨none⟩ else policy past view

theorem ResponseRecorded.mono {owner : Player} {coordinate : CommitAttemptEvent graph}
    {past more : List (app).PlayerEntry} (recorded : ResponseRecorded runtime leaks owner
      coordinate past) (contains : past ⊆ more) : ResponseRecorded runtime leaks owner
      coordinate more := by
  obtain ⟨entry, member, request⟩ := recorded
  exact ⟨entry, contains member, request⟩

/-- Every actual response, including silence, records the requested event. -/
theorem responseRecorded_respond {inputs : graph.Inputs} (execution : (app).Execution)
    (valid : execution.application.Invariant inputs) (owner : Player)
    (coordinate : CommitAttemptEvent graph)
    (request : execution.application.SeedRequest owner coordinate) (response : (app).Action) :
    ResponseRecorded runtime leaks owner coordinate
      ((execution.respond app owner response).recall owner) := by
  have publicRequest := (PhaseRuntimeState.requests_publicView execution.application valid owner
    coordinate).mpr request
  rcases response with ⟨_ | material⟩
  all_goals
    unfold ResponseRecorded
    simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
    refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    exact publicRequest

/-- Once recorded, a decision remains in own information under arbitrary
future player policies, environment commands, retirement and rollback. -/
theorem ResponseRecorded.runRounds {owner : Player} {coordinate : CommitAttemptEvent graph}
    (scheduler : (app).Scheduler) (players : Player → (app).Policy) (count : Nat)
    (execution next : (app).Execution)
    (recorded : ResponseRecorded runtime leaks owner coordinate (execution.recall owner))
    (reached : next ∈ ((app).runRounds scheduler players count execution).support) :
    ResponseRecorded runtime leaks owner coordinate (next.recall owner) := by
  have invariant : (app).ServiceInvariant scheduler (fun state =>
      ResponseRecorded runtime leaks owner coordinate (state.recall owner)) := {
    respond := fun current who response valid => ResponseRecorded.mono runtime leaks valid
      ((app).respond_recall_mono current who owner response)
    environment := fun current future command valid _ moved => by
      rw [(app).environmentStep_recall current future command moved]
      exact valid }
  exact invariant.runRounds players count execution next recorded reached

/-- The original first-callback law is retained exactly. -/
theorem phaseOncePolicy_first (owner : Player) (event : graph.EventId) (policy : (app).Policy)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (first : ¬ ResponseRecorded runtime leaks owner ⟨view.application.2.attempt, event⟩ past) :
    phaseOncePolicy runtime leaks owner event policy past view = policy past view := by
  simp only [phaseOncePolicy, first, ↓reduceIte]

/-- Sampling a physical omission cannot be reversed at a later callback for
that coordinate, even after arbitrary intervening private and public behavior. -/
theorem phaseOncePolicy_later {inputs : graph.Inputs} (execution : (app).Execution)
    (valid : execution.application.Invariant inputs) (owner : Player)
    (coordinate : CommitAttemptEvent graph)
    (request : execution.application.SeedRequest owner coordinate) (response : (app).Action)
    (scheduler : (app).Scheduler) (players : Player → (app).Policy) (count : Nat)
    (next : (app).Execution)
    (reached : next ∈ ((app).runRounds scheduler players count
      (execution.respond app owner response)).support)
    (again : next.application.SeedRequest owner coordinate) (policy : (app).Policy) :
    phaseOncePolicy runtime leaks owner coordinate.event policy (next.recall owner)
      (next.observe app owner) = PMF.pure ⟨none⟩ := by
  have remembered := (responseRecorded_respond runtime leaks execution valid owner coordinate
    request response).runRounds runtime leaks scheduler players count _ next reached
  have address : ⟨(next.observe app owner).application.2.attempt, coordinate.event⟩ =
      coordinate := by
    change CommitAttemptEvent.mk next.application.attempt coordinate.event = coordinate
    rw [← again.1]
  simp only [phaseOncePolicy, address, remembered, ↓reduceIte]

section FiniteMenu

variable [Fintype Player] (bounds : MessageBounds graph)

/-- First-response persistence preserves global one-packet legality. -/
theorem phaseOncePolicy_covered (owner : Player) (event : graph.EventId) (policy : (app).Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ onePacketActions runtime leaks bounds owner past view)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈
      (phaseOncePolicy runtime leaks owner event policy past view).support) :
    response ∈ onePacketActions runtime leaks bounds owner past view := by
  unfold phaseOncePolicy at supported
  split at supported
  · cases (PMF.mem_support_pure_iff _ _).mp supported
    exact silence_onePacket runtime leaks bounds owner past view
  · exact covered past view response supported

end FiniteMenu
end Vegas.EventGraphRuntime.PhaseCount
