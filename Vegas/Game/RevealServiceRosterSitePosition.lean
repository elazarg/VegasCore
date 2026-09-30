/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRosterClock

/-! # One physical phase position across an information site

The player already remembers its responses. Their number identifies its
current scheduled occurrence, so all histories in one information site have
the same environment position. Since each roster slot lies inside its event's
block, that position identifies the same event and roster slot, including
off-path sites.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_same_information_position
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (menu : (application setup leaks).ResponseMenu)
    (who : Player) (left right : (application setup leaks).Control)
    (leftTrace : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Trace (some left))
    (rightTrace : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Trace (some right))
    (leftActive : left.actor = some who) (rightActive : right.actor = some who)
    (same : (application setup leaks).observe who (some left) =
      (application setup leaks).observe who (some right)) :
    left.execution.environmentRecall.length = right.execution.environmentRecall.length := by
  simp only [ReactiveApplication.observe, leftActive, rightActive, ↓reduceIte,
    Option.some.injEq] at same
  have recall := congrArg Prod.fst same
  exact ((application setup leaks).scheduled_decision_position (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
    ((rosterPlan setup rosters).map instructionActor)
    (roster_scheduled_actor setup leaks rosters network) who left right
    (menu.toRawTrace _ _ _ leftTrace) (menu.toRawTrace _ _ _ rightTrace)
    leftActive rightActive (congrArg List.length recall)).1

theorem roster_site_position
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (menu : (application setup leaks).ResponseMenu)
    (who : Player) (site : (menu.information (initialLaw setup)
      (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).InformationSite who)
    (left right : (menu.information (initialLaw setup)
      (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).InformationHistory who site.1)
    (leftControl rightControl : (application setup leaks).Control)
    (leftState : left.1.state = some leftControl)
    (rightState : right.1.state = some rightControl) :
    leftControl.execution.environmentRecall.length =
      rightControl.execution.environmentRecall.length := by
  have leftActive := InformationModel.InformationSite.active _ site left
  have rightActive := InformationModel.InformationSite.active _ site right
  rw [leftState] at leftActive
  rw [rightState] at rightActive
  have same := left.2.trans right.2.symm
  change (menu.signals _ _ _).infoOf who left.1.trace =
    (menu.signals _ _ _).infoOf who right.1.trace at same
  rw [menu.info, menu.info, leftState, rightState] at same
  exact roster_same_information_position setup leaks rosters network menu who leftControl
    rightControl (leftState ▸ left.1.trace) (rightState ▸ right.1.trace)
    leftActive rightActive same

private theorem rosterPlanPrefix_length_le (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) {rank rank' : Nat}
    (le : rank ≤ rank') :
    (rosterPlanPrefix setup rosters rank).length ≤
      (rosterPlanPrefix setup rosters rank').length := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  simp only [rosterPlanPrefix, List.take_add, List.flatMap_append, List.length_append]
  omega

/-- A roster slot of an earlier event lies before every later event's block. -/
private theorem roster_slot_before (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (early late : (graph setup).EventId)
    (slot : Nat) (bound : slot < (rosters early).length) (before : early.val < late.val) :
    (rosterPlanPrefix setup rosters early.val).length + slot <
      (rosterPlanPrefix setup rosters late.val).length := by
  have grows := rosterPlanPrefix_length_le setup rosters (Nat.succ_le_of_lt before)
  rw [rosterPlanPrefix_succ, List.length_append, rosterBlock_length] at grows
  omega

/-- The event and within-event slot are common to the entire information
fiber, not merely to histories with positive limiting strategy probability. -/
theorem roster_site_phase
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (menu : (application setup leaks).ResponseMenu)
    (who : Player) (site : (menu.information (initialLaw setup)
      (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).InformationSite who)
    (left right : (menu.information (initialLaw setup)
      (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).InformationHistory who site.1)
    (leftControl rightControl : (application setup leaks).Control)
    (leftState : left.1.state = some leftControl)
    (rightState : right.1.state = some rightControl)
    (leftEvent rightEvent : (graph setup).EventId) (leftSlot rightSlot : Nat)
    (leftBound : leftSlot < (rosters leftEvent).length)
    (rightBound : rightSlot < (rosters rightEvent).length)
    (leftPosition : leftControl.execution.environmentRecall.length =
      (rosterPlanPrefix setup rosters leftEvent.val).length + leftSlot + 1)
    (rightPosition : rightControl.execution.environmentRecall.length =
      (rosterPlanPrefix setup rosters rightEvent.val).length + rightSlot + 1) :
    leftEvent = rightEvent ∧ leftSlot = rightSlot := by
  have position := roster_site_position setup leaks rosters network menu who site
    left right leftControl rightControl leftState rightState
  rcases Nat.lt_trichotomy leftEvent.val rightEvent.val with before | same | after
  · have := roster_slot_before setup rosters leftEvent rightEvent leftSlot leftBound before
    omega
  · have events : leftEvent = rightEvent := Fin.ext same
    subst events
    exact ⟨rfl, by omega⟩
  · have := roster_slot_before setup rosters rightEvent leftEvent rightSlot rightBound after
    omega

/-- Any current raw response advances the same public roster count. This is
independent of its packet, inclusion effect, and private passive sample. -/
theorem roster_after_response_counts
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (players : Player → (application setup leaks).Policy)
    (event : (graph setup).EventId)
    (initial current : (application setup leaks).Execution)
    (counts : ∀ player, (initial.recall player).length = rosterOffset setup rosters player event)
    (visited remaining : List Player) (who : Player)
    (split : rosters event = visited ++ who :: remaining)
    (reached : current ∈ ((runtime setup).runInteractionPlan leaks players network
      (visited.map ServiceInstruction.player) initial).support)
    (sample : Finset (MessageId Player)) (response : (application setup leaks).Action) :
    ∀ player, (((current.sampledActivation (application setup leaks) who sample).respond
      (application setup leaks) who response).recall player).length + remaining.count player =
      (((List.finRange (graph setup).order.eventCount).take (event.val + 1)).flatMap
        rosters).count player := by
  intro player
  have visitedCount := fixed_plan_response_counts setup leaks network players
    (visited.map ServiceInstruction.player) (by simp) initial current reached player
  simp only [List.filterMap_map, instructionActor, Function.comp_def, List.filterMap_some,
    counts player] at visitedCount
  have phaseCount := congrArg
    (fun plan : List (ServiceInstruction (graph setup)) =>
      (plan.filterMap instructionActor).count player)
    (rosterPlanPrefix_succ setup rosters event)
  rw [List.filterMap_append, List.count_append, rosterPlanPrefix_actors,
    rosterPlanPrefix_actors, rosterBlock_actors, split, List.count_append,
    List.count_cons] at phaseCount
  rw [ReactiveApplication.respond_recall_length]
  change (current.recall player).length + (if who = player then 1 else 0) +
    remaining.count player = _
  change _ = rosterOffset setup rosters player event +
    (visited.count player + (remaining.count player + (if who == player then 1 else 0)))
    at phaseCount
  simp only [beq_iff_eq] at phaseCount
  omega

end Vegas
