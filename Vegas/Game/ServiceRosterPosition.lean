/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ServiceRoster

/-! # Positions and public block-entry observations in roster plans

Each tagged instruction retains its block and local offset. Recording the first
command of a block fixes its public entry snapshot, which subsequent recall
extensions preserve independently of later application views.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem rosterPlan_getElem_block (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId)
    (offset : Nat) (inside : offset < (rosterBlock setup rosters event).length) :
    (rosterPlan setup rosters)[(rosterPlanPrefix setup rosters event.val).length + offset]? =
      ((rosterBlock setup rosters event)[offset]?).map (Prod.mk event) := by
  obtain ⟨suffix, split⟩ := rosterPlan_split setup rosters event
  rw [split, List.append_assoc, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simpa only [List.length_map] using inside),
    List.getElem?_map]

theorem rosterPlan_length_block (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    (rosterPlanPrefix setup rosters event.val).length +
        (rosterBlock setup rosters event).length ≤ (rosterPlan setup rosters).length := by
  obtain ⟨suffix, split⟩ := rosterPlan_split setup rosters event
  rw [split]
  simp only [List.length_append, List.length_map]
  omega

theorem rosterPlanPrefix_eventCount (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) :
    rosterPlanPrefix setup rosters (graph setup).order.eventCount = rosterPlan setup rosters := by
  simp only [rosterPlanPrefix, rosterPlan]
  rw [List.take_of_length_le (by simp only [List.length_finRange]; omega)]

theorem rosterBlock_roster (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId)
    (offset : Nat) (inside : offset < (rosters event).length) :
    (rosterBlock setup rosters event)[offset]? =
      some (.player ((rosters event)[offset]'inside)) := by
  rw [rosterBlock_eq_ending,
    List.getElem?_append_left (by simpa only [List.length_map] using inside),
    List.getElem?_map, List.getElem?_eq_getElem inside]
  rfl

theorem rosterBlock_ending (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId)
    (offset : Nat) :
    (rosterBlock setup rosters event)[(rosters event).length + offset]? =
      (rosterPhaseEnding setup event)[offset]? := by
  rw [rosterBlock_eq_ending, List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.add_sub_cancel_left]

theorem rosterPhaseEnding_first (setup : Setup (Player := Player) (L := L))
    (event : (graph setup).EventId) :
    (rosterPhaseEnding setup event)[0]? = some (match (graph setup).actor? event with
      | none => .sample event
      | some owner => .includeLatest event owner) := by
  unfold rosterPhaseEnding
  cases (graph setup).actor? event <;> rfl

theorem rosterPhaseEnding_tick (setup : Setup (Player := Player) (L := L))
    (event : (graph setup).EventId) (index : Nat) (inside : index < event.val + 1) :
    (rosterPhaseEnding setup event)[index + 1]? = some .tick := by
  have shape : rosterPhaseEnding setup event =
      (match (graph setup).actor? event with
        | none => ServiceInstruction.sample event
        | some owner => .includeLatest event owner) ::
        (List.replicate (event.val + 1) .tick ++ [.expire event]) := by
    unfold rosterPhaseEnding
    cases (graph setup).actor? event <;> rfl
  rw [shape, List.getElem?_cons_succ,
    List.getElem?_append_left (by simpa only [List.length_replicate] using inside),
    List.getElem?_replicate_of_lt inside]

theorem rosterPhaseEnding_expire (setup : Setup (Player := Player) (L := L))
    (event : (graph setup).EventId) :
    (rosterPhaseEnding setup event)[event.val + 2]? = some (.expire event) := by
  have shape : rosterPhaseEnding setup event =
      (match (graph setup).actor? event with
        | none => ServiceInstruction.sample event
        | some owner => .includeLatest event owner) ::
        (List.replicate (event.val + 1) .tick ++ [.expire event]) := by
    unfold rosterPhaseEnding
    cases (graph setup).actor? event <;> rfl
  rw [shape, List.getElem?_cons_succ,
    List.getElem?_append_right (by simp only [List.length_replicate]; omega)]
  simp only [List.length_replicate, Nat.sub_self, List.getElem?_cons_zero]

section EntrySnapshot

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (rosters : (graph setup).EventId → List Player)
  (past extra : List (application setup (Vegas.runtime setup) leaks).EnvironmentEntry)
  (view nextView : (application setup (Vegas.runtime setup) leaks).EnvironmentView)
  (event : (graph setup).EventId)

/-- Before recording a block's first command, the current public view supplies
its entry observation. -/
theorem rosterBlockCompleted_at_start
    (position : past.length = (rosterPlanPrefix setup rosters event.val).length) :
    rosterBlockCompleted setup leaks rosters past view event ↔
      event ∈ view.application.observation.completionOrder := by
  unfold rosterBlockCompleted
  rw [List.getElem?_eq_none (by omega)]
  rfl

/-- Once the block's first entry is recorded, later recall and current-view
changes preserve the block-completion test. -/
theorem rosterBlockCompleted_append
    (recorded : (rosterPlanPrefix setup rosters event.val).length < past.length) :
    rosterBlockCompleted setup leaks rosters (past ++ extra) nextView event ↔
      rosterBlockCompleted setup leaks rosters past view event := by
  unfold rosterBlockCompleted
  rw [List.getElem?_append_left recorded, List.getElem?_eq_getElem recorded]
  rfl

/-- Recording a command with its current public view preserves the entry test,
including the first command of a block. -/
theorem rosterBlockCompleted_record
    (command : (application setup (Vegas.runtime setup) leaks).Command)
    (position : (rosterPlanPrefix setup rosters event.val).length ≤ past.length) :
    rosterBlockCompleted setup leaks rosters (past ++ [⟨view, command⟩]) nextView event ↔
      rosterBlockCompleted setup leaks rosters past view event := by
  rcases position.eq_or_lt with atStart | recorded
  · have boundary : past.length = (rosterPlanPrefix setup rosters event.val).length :=
      atStart.symm
    rw [rosterBlockCompleted_at_start setup leaks rosters past view event boundary]
    unfold rosterBlockCompleted
    rw [List.getElem?_append_right (by omega), ← boundary, Nat.sub_self,
      List.getElem?_cons_zero]
    rfl
  · exact rosterBlockCompleted_append setup leaks rosters past [⟨view, command⟩]
      view nextView event recorded

end EntrySnapshot

end Vegas
