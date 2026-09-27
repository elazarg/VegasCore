/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterPolicy
import Vegas.Game.RevealServiceClock

/-! # Finite activation rosters in the existing native service

Each event has a public finite activation roster, then protected inclusion or
public sampling, followed by clock ticks and expiry. Every listed player has
the full native response interface and its given passive observation rule.
The scheduler reads its own command count; that count is not added to player
observations. This is a service instance, not another interpreter or language.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

def rosterBlock (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    List (ServiceInstruction (graph setup)) :=
  [.grant event] ++ (rosters event).map ServiceInstruction.player ++
    (match (graph setup).actor? event with
    | none => [.sample event]
    | some owner => [.includeLatest event owner]) ++
      List.replicate (event.val + 1) .tick ++ [.expire event]

def rosterPlanPrefix (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (rank : Nat) :
    List (ServiceInstruction (graph setup)) :=
  ((List.finRange (graph setup).order.eventCount).take rank).flatMap (rosterBlock setup rosters)

def rosterPlan (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) : List (ServiceInstruction (graph setup)) :=
  (List.finRange (graph setup).order.eventCount).flatMap (rosterBlock setup rosters)

def rosterScheduler (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) : (application setup leaks).Scheduler :=
  fun past view => match (rosterPlan setup rosters)[past.length]? with
    | none => FinDist.pure .wait
    | some instruction => (runtime setup).interactionInstruction leaks network past view instruction

theorem rosterBlock_of_owner (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId)
    (owner : Player) (owned : (graph setup).actor? event = some owner) :
    rosterBlock setup rosters event = [.grant event] ++
      (((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        List.replicate (event.val + 1) .tick ++ [.expire event]) := by
  simp only [rosterBlock, owned, List.append_assoc]

theorem rosterBlock_length (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    (rosterBlock setup rosters event).length = (rosters event).length + event.val + 4 := by
  unfold rosterBlock
  cases (graph setup).actor? event <;>
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
      List.length_replicate] <;> omega

theorem rosterBlock_actors (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    (rosterBlock setup rosters event).filterMap instructionActor = rosters event := by
  unfold rosterBlock
  cases (graph setup).actor? event <;> simp [instructionActor]

theorem rosterBlock_no_wire (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    ServiceInstruction.wire ∉ rosterBlock setup rosters event := by
  unfold rosterBlock
  cases (graph setup).actor? event <;> simp

theorem rosterPlanPrefix_succ (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    rosterPlanPrefix setup rosters (event.val + 1) =
      rosterPlanPrefix setup rosters event.val ++ rosterBlock setup rosters event := by
  simp only [rosterPlanPrefix, List.take_add_one, List.flatMap_append]
  have selected : (List.finRange (graph setup).order.eventCount)[event.val]? = some event := by
    rw [List.getElem?_eq_getElem (by simpa only [List.length_finRange] using event.isLt),
      List.getElem_finRange]
    exact congrArg some (Fin.ext rfl)
  simp only [selected, Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem rosterPlanPrefix_actors (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (rank : Nat) :
    (rosterPlanPrefix setup rosters rank).filterMap instructionActor =
      ((List.finRange (graph setup).order.eventCount).take rank).flatMap rosters := by
  simp only [rosterPlanPrefix, List.filterMap_flatMap, rosterBlock_actors]

theorem rosterPlanPrefix_no_wire (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (rank : Nat) :
    ServiceInstruction.wire ∉ rosterPlanPrefix setup rosters rank := by
  intro member
  obtain ⟨event, _, inside⟩ := List.mem_flatMap.mp member
  exact rosterBlock_no_wire setup rosters event inside

theorem rosterPlan_split (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    ∃ suffix, rosterPlan setup rosters =
      rosterPlanPrefix setup rosters event.val ++ rosterBlock setup rosters event ++ suffix := by
  let events := List.finRange (graph setup).order.eventCount
  refine ⟨(events.drop (event.val + 1)).flatMap (rosterBlock setup rosters), ?_⟩
  have split := congrArg (List.flatMap (rosterBlock setup rosters))
    (events.take_append_drop (event.val + 1))
  rw [List.flatMap_append] at split
  change rosterPlanPrefix setup rosters (event.val + 1) ++ _ = rosterPlan setup rosters at split
  rw [rosterPlanPrefix_succ] at split
  exact split.symm

/-- The plan evaluator is exactly the existing native game scheduler, from
every supported service position and for arbitrary response policies. -/
theorem roster_suffix_rounds (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (players : Player → (application setup leaks).Policy)
    (before rest : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ rest)
    (execution : (application setup leaks).Execution)
    (position : execution.environmentRecall.length = before.length) :
    (application setup leaks).runRounds (rosterScheduler setup leaks rosters network)
      players rest.length execution =
        (runtime setup).runInteractionPlan leaks players network rest execution := by
  induction rest generalizing before execution with
  | nil => rfl
  | cons instruction rest ih =>
      have selected : (rosterPlan setup rosters)[before.length]? = some instruction := by
        rw [split, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      have step : (application setup leaks).round (rosterScheduler setup leaks rosters network)
          players execution = (runtime setup).interactionStep leaks players network
            instruction execution := by
        simp only [ReactiveApplication.round, rosterScheduler, position, selected, interactionStep]
      rw [List.length_cons, ReactiveApplication.runRounds, step, runInteractionPlan]
      apply FinDist.bind_congr
      intro next supported
      apply ih (before ++ [instruction])
      · simpa only [List.append_assoc, List.singleton_append] using split
      · have advanced := (runtime setup).interactionStep_recall leaks players network instruction
          execution next supported
        simp only [List.length_append, List.length_singleton]
        omega

end Vegas.SourceProgram.RevealService
