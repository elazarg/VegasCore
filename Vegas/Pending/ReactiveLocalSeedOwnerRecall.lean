/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedActivation
import Interaction.ReactiveHistory

/-! # Positive local queries reconstructed from real owner recall

The owner's complete response entries record every selected-event activation
input, including repeated activations at an unchanged public clock.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => runtime.reactiveApplication leaks

/-- Count actual owner decisions made while the selected event was ready. -/
def readyActivationCount (event : graph.EventId) (past : List (app).PlayerEntry) : Nat :=
  (past.filter fun entry => entry.beforeView.application.publicView.EventReady event).length

/-- Reconstruct the positive queries at their original actual owner recall prefixes. -/
def ownerActivationQueriesFrom (event : graph.EventId) (earlier : List (app).PlayerEntry) :
    List (app).PlayerEntry → List (CurrentSeedQuery graph)
  | [] => []
  | entry :: rest =>
      let remaining := ownerActivationQueriesFrom event (earlier ++ [entry]) rest
      if entry.beforeView.application.publicView.EventReady event then
        ⟨runtime.ownerSeedInput leaks event earlier entry.beforeView,
          runtime.readyActivationCount leaks event earlier⟩ :: remaining
      else remaining

/-- The positive-query history readable by the owner, before its current response. -/
def ownerActivationQueries (event : graph.EventId) (past : List (app).PlayerEntry) :
    List (CurrentSeedQuery graph) := runtime.ownerActivationQueriesFrom leaks event [] past

theorem ownerActivationQueriesFrom_append (event : graph.EventId)
    (earlier left right : List (app).PlayerEntry) :
    runtime.ownerActivationQueriesFrom leaks event earlier (left ++ right) =
      runtime.ownerActivationQueriesFrom leaks event earlier left ++
        runtime.ownerActivationQueriesFrom leaks event (earlier ++ left) right := by
  induction left generalizing earlier with
  | nil => simp only [List.nil_append, ownerActivationQueriesFrom, List.append_nil]
  | cons entry rest ih =>
      simp only [List.cons_append, ownerActivationQueriesFrom]
      split_ifs <;>
        simp only [ih, List.cons_append, List.append_assoc, List.nil_append]

theorem ownerActivationQueries_snoc (event : graph.EventId) (past : List (app).PlayerEntry)
    (entry : (app).PlayerEntry) :
    runtime.ownerActivationQueries leaks event (past ++ [entry]) =
      runtime.ownerActivationQueries leaks event past ++
        if entry.beforeView.application.publicView.EventReady event then
          [⟨runtime.ownerSeedInput leaks event past entry.beforeView,
            runtime.readyActivationCount leaks event past⟩] else [] := by
  simp only [ownerActivationQueries, ownerActivationQueriesFrom_append,
    ownerActivationQueriesFrom, List.nil_append]

theorem readyActivationCount_snoc (event : graph.EventId) (past : List (app).PlayerEntry)
    (entry : (app).PlayerEntry) :
    runtime.readyActivationCount leaks event (past ++ [entry]) =
      runtime.readyActivationCount leaks event past +
        if entry.beforeView.application.publicView.EventReady event then 1 else 0 := by
  classical
  simp only [readyActivationCount, List.filter_append, List.length_append]
  split_ifs <;> simp_all

/-- Positive-query indices are observable counts of ready owner decisions. -/
theorem ownerActivationQueries_length (event : graph.EventId) (past : List (app).PlayerEntry) :
    (runtime.ownerActivationQueries leaks event past).length =
      runtime.readyActivationCount leaks event past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [runtime.ownerActivationQueries_snoc, runtime.readyActivationCount_snoc,
        List.length_append]
      split_ifs <;> simp_all

private theorem respond_recall_entry (execution : (app).Execution) (owner : Player)
    (action : (app).Action) :
    ∃ emitted, (execution.respond app owner action).recall owner =
      execution.recall owner ++ [⟨execution.observe app owner, action, emitted⟩] := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨none, by simp only [ReactiveApplication.Execution.respond, ↓reduceIte]⟩
  | some material =>
      exact ⟨some (execution.network.submit owner
        ((app).packet ((app).submit execution.application owner material) owner
          (execution.network.known owner) material)).1, by
            simp only [ReactiveApplication.Execution.respond, ↓reduceIte]⟩

/-- A real owner response records exactly one positive query when its selected
event was ready; this statement retains the full emitted-envelope prefix. -/
theorem respond_ownerActivationQueries (execution : (app).Execution) (owner : Player)
    (event : graph.EventId) (action : (app).Action) :
    runtime.ownerActivationQueries leaks event ((execution.respond app owner action).recall owner) =
      runtime.ownerActivationQueries leaks event (execution.recall owner) ++
        if execution.application.publicView.EventReady event then
          [⟨runtime.ownerSeedInput leaks event (execution.recall owner)
            (execution.observe app owner), runtime.readyActivationCount leaks event
              (execution.recall owner)⟩] else [] := by
  obtain ⟨emitted, recorded⟩ := runtime.respond_recall_entry leaks execution owner action
  rw [recorded, runtime.ownerActivationQueries_snoc]
  rfl

/-- Sampling pending knowledge at activation leaves the complete local seed
input unchanged, although the player's leaked-message view may change. -/
theorem environmentActivation_ownerSeedInput (execution next : (app).Execution)
    (actor owner : Player) (event : graph.EventId)
    (reached : next ∈ (execution.environmentStep app (.activate actor)).support) :
    runtime.ownerSeedInput leaks event (next.recall owner) (next.observe app owner) =
      runtime.ownerSeedInput leaks event (execution.recall owner)
        (execution.observe app owner) := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at reached
  obtain ⟨selected, chosen, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  rfl

private theorem environmentActivation_application (execution next : (app).Execution)
    (actor : Player)
    (reached : next ∈ (execution.environmentStep app (.activate actor)).support) :
    next.application = execution.application := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at reached
  obtain ⟨selected, chosen, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  rfl

open Classical in
/-- Each genuine dispatch appends precisely the positive selected-event query
visible in its owner's new response entry, or preserves that query history. -/
theorem dispatch_ownerActivationQueries (players : Player → (app).Policy)
    (execution next : (app).Execution) (command : (app).Command) (owner : Player)
    (event : graph.EventId)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    runtime.ownerActivationQueries leaks event (next.recall owner) =
      runtime.ownerActivationQueries leaks event (execution.recall owner) ++
        if command = .activate owner ∧ execution.application.publicView.EventReady event then
          [⟨runtime.ownerSeedInput leaks event (execution.recall owner)
            (execution.observe app owner), runtime.readyActivationCount leaks event
              (execution.recall owner)⟩] else [] := by
  classical
  obtain ⟨middle, moved, responded⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have recallEq := (app).environmentStep_recall execution middle command moved
  cases command with
  | activate actor =>
      change next ∈ ((players actor (middle.recall actor) (middle.observe app actor)).map
        (middle.respond app actor)).support at responded
      obtain ⟨action, chosen, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp responded
      by_cases same : actor = owner
      · subst actor
        rw [runtime.respond_ownerActivationQueries]
        rw [runtime.environmentActivation_application leaks execution middle owner moved]
        rw [runtime.environmentActivation_ownerSeedInput leaks execution middle owner owner event
          moved]
        rw [recallEq]
        simp
      · rw [(app).respond_recall_other middle actor owner (Ne.symm same) action, recallEq]
        simp only [ReactiveApplication.Command.activate.injEq, same, false_and, ↓reduceIte,
          List.append_nil]
  | «include» id =>
      cases (PMF.mem_support_pure_iff _ _).mp responded
      rw [recallEq]
      simp
  | application command =>
      cases (PMF.mem_support_pure_iff _ _).mp responded
      rw [recallEq]
      simp
  | wait =>
      cases (PMF.mem_support_pure_iff _ _).mp responded
      rw [recallEq]
      simp

end Vegas.EventGraphRuntime
