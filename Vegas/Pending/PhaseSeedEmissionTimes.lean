/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedRecordedWait
import Vegas.Pending.PhaseSeedEmissionPersistence
import Interaction.ReactiveRecordedResponse

/-! # Future envelopes cannot predate an actual unsent callback -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private theorem unsent_word_lower (coordinate : CommitAttemptEvent graph) (owner : Player)
    (past : List (app).PlayerEntry)
    (unsent : ∀ message ∈ (app).outputs past, ownPacket coordinate owner message = false)
    (origin : Nat) :
    ∀ record ∈ ownerWord runtime leaks coordinate owner past,
      ∀ message ∈ record.2, origin ≤ record.1 := by
  classical
  intro record recorded message emitted
  obtain ⟨entry, member, same⟩ := List.mem_map.mp recorded
  rw [← same] at emitted
  obtain ⟨output, selected⟩ := List.mem_filter.mp emitted
  have actual : entry.emitted = some message := Option.mem_toList.mp output
  have inPast := (List.mem_filter.mp member).1
  have authored : message ∈ (app).outputs past := List.mem_filterMap.mpr ⟨entry, inPast, actual⟩
  rw [unsent message authored] at selected
  cases selected

private theorem ownerWord_lower_respond {inputs : graph.Inputs}
    (execution : (app).Execution) (valid : execution.application.Invariant inputs)
    (coordinate : CommitAttemptEvent graph) (owner : Player) (tick entered : Nat)
    (bound : ClosedCoordinateBound runtime tick entered coordinate
      execution.application)
    (lower : ∀ record ∈ ownerWord runtime leaks coordinate owner (execution.recall owner),
      ∀ message ∈ record.2, tick - entered ≤ record.1)
    (acting : Player) (action : (app).Action) :
    ∀ record ∈ ownerWord runtime leaks coordinate owner
      ((execution.respond app acting action).recall owner),
      ∀ message ∈ record.2, tick - entered ≤ record.1 := by
  classical
  by_cases sameOwner : owner = acting
  · subst acting
    intro record recorded message emitted
    obtain ⟨emittedEnvelope, recalled⟩ := (app).respond_recall_entry execution owner action
    rw [recalled] at recorded
    simp only [ownerWord, List.filter_append, List.map_append, List.mem_append] at recorded
    rcases recorded with old | fresh
    · exact lower record old message emitted
    · obtain ⟨entry, member, entryEq⟩ := List.mem_map.mp fresh
      obtain ⟨member, selected⟩ := List.mem_filter.mp member
      have entrySame := List.mem_singleton.mp member
      subst entry
      have requested : execution.application.SeedRequest owner coordinate :=
        (PhaseRuntimeState.requests_publicView execution.application valid owner coordinate).mp
          (of_decide_eq_true selected)
      have stamp : execution.application.current.native.activatedAt coordinate.event =
          some entered := by
        rcases bound.event requested.1 with completed | ready
        · exact (requested.2.2.1.1 completed).elim
        · exact ready.2.1
      have clockEq := congrArg Prod.fst entryEq
      rw [← clockEq]
      change tick - entered ≤ execution.application.current.native.clock -
        (execution.application.current.native.activatedAt coordinate.event).getD
          execution.application.current.native.clock
      rw [stamp, Option.getD_some]
      exact Nat.sub_le_sub_right bound.clock entered
  · rw [(app).respond_recall_other execution acting owner sameOwner action]
    exact lower

/-- At an initially unsent callback, every envelope later visible for this
physical coordinate was authored at or after the original relative clock. -/
theorem runRounds_unsent_emissions_lower (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    {inputs : graph.Inputs} (valid : execution.application.Invariant inputs)
    (ordered : execution.application.Ordered) (words : WordRecall runtime leaks execution)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (requested : execution.application.SeedRequest owner coordinate)
    (entered : Nat)
    (activated : execution.application.current.native.activatedAt coordinate.event = some entered)
    (started : entered ≤ execution.application.current.native.clock)
    (timely : execution.application.current.native.clock - entered <
      runtime.deadline coordinate.event)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      ownPacket coordinate owner message = false)
    (reached : next ∈ ((app).runRounds scheduler players count execution).support) :
    ∀ emission ∈ (localInput runtime leaks coordinate owner next.environmentRecall
      (next.observeEnvironment app)).emissions,
      execution.application.current.native.clock - entered ≤ emission.1 := by
  let tick := execution.application.current.native.clock
  let lower := fun current : (app).Execution =>
    ∀ record ∈ ownerWord runtime leaks coordinate owner (current.recall owner),
      ∀ message ∈ record.2, tick - entered ≤ record.1
  let property := fun current : (app).Execution =>
    current.application.Invariant inputs ∧ current.application.Ordered ∧
      ClosedCoordinateBound runtime tick entered coordinate current.application ∧
        lower current
  have invariant : (app).ServiceInvariant scheduler property := {
    respond := fun current acting action before =>
      ⟨(phaseApplication_invariant runtime leaks inputs).respond current acting action before.1,
        (phaseApplication_seedOrder runtime leaks).respond current acting action before.2.1,
        ClosedCoordinateBound.respond runtime leaks current acting action before.1
          before.2.1 before.2.2.1,
        ownerWord_lower_respond runtime leaks current before.1 coordinate owner tick entered
          before.2.2.1 before.2.2.2 acting action⟩
    environment := fun current after command before _ moved => by
      refine ⟨(phaseApplication_invariant runtime leaks inputs).environmentStep current after
        command
        before.1 moved, (phaseApplication_seedOrder runtime leaks).environmentStep current after
        command before.2.1 moved, ClosedCoordinateBound.environmentStep runtime
        leaks current after command before.1 before.2.1 moved before.2.2.1, ?_⟩
      unfold lower
      rw [(app).environmentStep_recall current after command moved]
      exact before.2.2.2 }
  have initialBound : ClosedCoordinateBound runtime tick entered coordinate
      execution.application :=
    ⟨le_rfl, started, by rw [requested.1], by rw [requested.1],
      fun _ => Or.inr ⟨requested.2.2.1, activated, timely⟩⟩
  have before : property execution := ⟨valid, ordered, initialBound,
    unsent_word_lower runtime leaks coordinate owner (execution.recall owner) unsent
      (tick - entered)⟩
  have after := (invariant.runRounds players count execution next before reached).2.2.2
  have nextWords := runRounds_wordRecall runtime leaks scheduler players count execution next
    words reached
  intro emission member
  rw [localInput_word, nextWords owner coordinate] at member
  obtain ⟨record, recorded, member⟩ := List.mem_flatMap.mp member
  obtain ⟨message, emitted, same⟩ := List.mem_map.mp member
  rw [← same]
  exact after record recorded message emitted

end Vegas.EventGraphRuntime.PhaseSeedScheduler
