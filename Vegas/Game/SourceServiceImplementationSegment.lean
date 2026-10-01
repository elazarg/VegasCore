/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRosterCounts
import Interaction.ReactiveImplementation

/-! # Exact private implementation memory through reserved service

A real roster-plan segment without the focal player's activation uses the
ordinary physical service law and leaves its private implementation memory
unchanged. Other players and passive samples remain arbitrary. This equation
composes reserved inclusion and expiry with the single joint runner.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem resume_other_joint {app : ReactiveApplication Player} {Memory : Type}
    (implementation : app.Implementation Memory) (owner : Player)
    (players : Player → app.Policy) (actor : Option Player)
    (different : actor ≠ some owner) (execution : app.Execution) (memory : Memory) :
    implementation.resume owner players actor execution memory =
      (app.resume players actor execution).map (fun next => (next, memory)) := by
  cases actor with
  | none =>
      simp only [ReactiveApplication.Implementation.resume, ReactiveApplication.resume,
        PMF.pure_map]
  | some who =>
      have other : who ≠ owner := fun same => different (congrArg some same)
      simp only [ReactiveApplication.Implementation.resume, other, ↓reduceIte,
        ReactiveApplication.resume]

private theorem resume_position {app : ReactiveApplication Player} {Memory : Type}
    (implementation : app.Implementation Memory) (owner : Player)
    (players : Player → app.Policy) (actor : Option Player)
    (execution : app.Execution) (memory : Memory) (next : app.Execution × Memory)
    (supported : next ∈
      (implementation.resume owner players actor execution memory).support) :
    next.1.environmentRecall = execution.environmentRecall := by
  cases actor with
  | none =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | some who =>
      by_cases same : who = owner
      · subst who
        simp only [ReactiveApplication.Implementation.resume, ↓reduceIte,
          PMF.support_map] at supported
        obtain ⟨response, _, rfl⟩ := supported
        exact app.respond_environmentRecall execution owner response.1
      · rw [resume_other_joint implementation owner players (some who)
          (fun equal => same (Option.some.inj equal)) execution memory] at supported
        obtain ⟨middle, chosen, rfl⟩ := PMF.support_map .. ▸ supported
        exact app.resume_environmentRecall players (some who) execution middle chosen

private theorem joint_position {app : ReactiveApplication Player} {Memory : Type}
    (implementation : app.Implementation Memory) (owner : Player)
    (players : Player → app.Policy) (scheduler : app.Scheduler)
    (count : Nat) (execution : app.Execution) (memory : Memory) (next : app.Execution × Memory)
    (supported : next ∈
      (implementation.runJoint owner players scheduler count execution memory).support) :
    next.1.environmentRecall.length = execution.environmentRecall.length + count := by
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | succ count ih =>
      obtain ⟨middle, advanced, reached⟩ := Set.mem_iUnion₂.mp
        (PMF.support_bind .. ▸ supported)
      have rest := ih middle.1 middle.2 reached
      obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp
        (PMF.support_bind .. ▸ advanced)
      obtain ⟨activated, moved, resumed⟩ := Set.mem_iUnion₂.mp
        (PMF.support_bind .. ▸ dispatched)
      have unchanged := resume_position implementation owner players (command.actor? app)
        activated memory middle resumed
      obtain ⟨updated, _, same⟩ := PMF.support_map .. ▸ moved
      have entered : activated.environmentRecall.length =
          execution.environmentRecall.length + 1 := by
        rw [← same]
        simp only [List.length_append, List.length_singleton]
      rw [unchanged] at rest
      omega

/-- No hidden memory is discarded at an environment/foreign-player segment.
The right side is the existing physical service, including all observations. -/
theorem roster_segment_runJoint
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    {Memory : Type} (implementation : (application setup leaks).Implementation Memory)
    (owner : Player) (players : Player → (application setup leaks).Policy)
    (before segment after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ segment ++ after)
    (absent : ServiceInstruction.player owner ∉ segment)
    (execution : (application setup leaks).Execution) (memory : Memory)
    (position : execution.environmentRecall.length = before.length) :
    implementation.runJoint owner players (rosterScheduler setup leaks rosters network)
      segment.length execution memory =
        ((runtime setup).runInteractionPlan leaks players network segment execution).map
          (fun next => (next, memory)) := by
  let app := application setup leaks
  induction segment generalizing before execution with
  | nil =>
      simp only [List.length_nil, ReactiveApplication.Implementation.runJoint,
        runInteractionPlan, PMF.pure_map]
  | cons instruction segment ih =>
      have selected : (rosterPlan setup rosters)[before.length]? = some instruction := by
        rw [split, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      have fixed : instruction ≠ .wire := by
        intro same
        obtain ⟨event, _, member⟩ := List.mem_flatMap.mp (List.mem_of_getElem? selected)
        exact rosterBlock_no_wire setup rosters event (same ▸ member)
      have actorDifferent : instructionActor instruction ≠ some owner := by
        cases instruction with
        | player who =>
            intro same
            cases Option.some.inj same
            exact absent List.mem_cons_self
        | wire => intro impossible; cases impossible
        | includeLatest _ _ => intro impossible; cases impossible
        | sample _ => intro impossible; cases impossible
        | tick => intro impossible; cases impossible
        | expire _ => intro impossible; cases impossible
      have step : implementation.round owner players
          (rosterScheduler setup leaks rosters network) execution memory =
            ((runtime setup).interactionStep leaks players network instruction execution).map
              (fun next => (next, memory)) := by
        simp only [ReactiveApplication.Implementation.round, rosterScheduler, position, selected,
          interactionStep, PMF.map_bind]
        apply bind_congr_on_support _
        intro command supported
        have actor := roster_instruction_actor setup leaks network execution.environmentRecall
          (execution.observeEnvironment app) instruction fixed command supported
        simp only [ReactiveApplication.dispatch, PMF.map_bind]
        apply bind_congr_on_support _
        intro next _
        apply resume_other_joint
        rw [actor]
        exact actorDifferent
      rw [List.length_cons, ReactiveApplication.Implementation.runJoint, step,
        PMF.bind_map, runInteractionPlan, PMF.map_bind]
      apply bind_congr_on_support _
      intro next reached
      apply ih (before ++ [instruction])
      · simpa only [List.append_assoc, List.singleton_append] using split
      · exact fun member => absent (List.mem_cons_of_mem _ member)
      · have advanced := (runtime setup).interactionStep_recall leaks players network instruction
          execution next reached
        simp only [List.length_append, List.length_singleton]
        omega

/-- Append reserved inclusion/expiry (or foreign visits) to a joint private
prefix without changing its memory distribution or physical service law. -/
theorem roster_runJoint_append_reserved
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    {Memory : Type} (implementation : (application setup leaks).Implementation Memory)
    (owner : Player) (players : Player → (application setup leaks).Policy)
    (before leading reserved after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ leading ++ reserved ++ after)
    (absent : ServiceInstruction.player owner ∉ reserved)
    (execution : (application setup leaks).Execution) (memory : Memory)
    (position : execution.environmentRecall.length = before.length) :
    implementation.runJoint owner players (rosterScheduler setup leaks rosters network)
      (leading ++ reserved).length execution memory =
        (implementation.runJoint owner players (rosterScheduler setup leaks rosters network)
          leading.length execution memory).bind (fun next =>
            ((runtime setup).runInteractionPlan leaks players network reserved next.1).map
              fun final => (final, next.2)) := by
  rw [List.length_append, ReactiveApplication.Implementation.runJoint_add]
  apply bind_congr_on_support _
  intro next supported
  apply roster_segment_runJoint setup leaks rosters network implementation owner players
    (before ++ leading) reserved after split absent next.1 next.2
  rw [joint_position implementation owner players (rosterScheduler setup leaks rosters network)
    leading.length execution memory next supported, position, List.length_append]

/-- Split the actual joint runner at an owner's next scheduled response.
The preceding segment may contain arbitrary instructions, including earlier
owner responses: its complete execution and memory distribution is retained. -/
theorem roster_runJoint_at_owner
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    {Memory : Type} (implementation : (application setup leaks).Implementation Memory)
    (owner : Player) (players : Player → (application setup leaks).Policy)
    (before leading rest after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ leading ++ (.player owner :: rest) ++ after)
    (execution : (application setup leaks).Execution) (memory : Memory)
    (position : execution.environmentRecall.length = before.length) :
    implementation.runJoint owner players (rosterScheduler setup leaks rosters network)
        (leading.length + 1 + rest.length) execution memory =
      (implementation.runJoint owner players (rosterScheduler setup leaks rosters network)
        leading.length execution memory).bind fun pair =>
          (pair.1.environmentStep (application setup leaks) (.activate owner)).bind fun observed =>
            (implementation.resume owner players (some owner) observed pair.2).bind fun resumed =>
              implementation.runJoint owner players (rosterScheduler setup leaks rosters network)
                rest.length resumed.1 resumed.2 := by
  rw [show leading.length + 1 + rest.length = leading.length + (rest.length + 1) by omega,
    ReactiveApplication.Implementation.runJoint_add]
  apply bind_congr_on_support _
  intro pair supported
  have cursor := joint_position implementation owner players
    (rosterScheduler setup leaks rosters network) leading.length execution memory pair supported
  rw [position] at cursor
  have arranged : rosterPlan setup rosters =
      (before ++ leading) ++ .player owner :: (rest ++ after) := by
    simpa only [List.append_assoc, List.cons_append] using split
  have selected : (rosterPlan setup rosters)[pair.1.environmentRecall.length]? =
      some (.player owner) := by
    rw [cursor, ← List.length_append, arranged,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  simp only [ReactiveApplication.Implementation.runJoint,
    ReactiveApplication.Implementation.round, rosterScheduler, selected,
    interactionInstruction, PMF.pure_bind, ReactiveApplication.Command.actor?,
    PMF.bind_bind]

end Vegas
