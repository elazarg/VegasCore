/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceCompletion
import Interaction.ReactiveScheduleEvaluation
import GameTheoryExtensions.Math.Probability.FinDist

/-! # Counted native histories at service-prefix boundaries

A scheduler instruction consumes one protocol transition, and a player
activation consumes one additional response transition. The actual history
runner therefore reaches each service boundary at an exact common depth.
The equality retains the complete execution, including all private recall.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime GameTheory.Math.Probability
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Execute any actual service segment, counting the protocol transition for
each command and the additional transition for each response. -/
theorem segment_control_steps (watcher : Player)
    (players : Player → (application setup leaks).Policy)
    (before segment rest : List (ServiceInstruction (graph setup)))
    (split : plan setup watcher = before ++ segment ++ rest)
    (execution : (application setup leaks).Execution)
    (position : execution.environmentRecall.length = before.length) :
    (fun law => law.bind ((application setup leaks).controlStep (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher) players))^[
        segment.length + (segment.filterMap instructionActor).length]
        (FinDist.pure (some ⟨segment.length + rest.length, none, execution⟩)) =
      ((runtime setup).runInteractionPlan leaks players
        ((runtime setup).reportNetwork leaks watcher) segment execution).map
          (fun next => some ⟨rest.length, none, next⟩) := by
  induction segment generalizing before execution with
  | nil => simp only [List.length_nil, List.filterMap_nil, Nat.zero_add,
      Function.iterate_zero_apply, runInteractionPlan, FinDist.map_pure]
  | cons instruction segment ih =>
      let first := 1 + (instructionActor instruction).toList.length
      let later := segment.length + (segment.filterMap instructionActor).length
      have count : (instruction :: segment).length +
          ((instruction :: segment).filterMap instructionActor).length = later + first := by
        cases actor : instructionActor instruction <;>
          simp [actor, first, later] <;> omega
      have located : (plan setup watcher)[before.length]? = some instruction := by
        rw [split, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      have schedulerEq : (scheduler setup leaks watcher) execution.environmentRecall
          (execution.observeEnvironment (application setup leaks)) =
          (runtime setup).interactionInstruction leaks ((runtime setup).reportNetwork leaks watcher)
            execution.environmentRecall
            (execution.observeEnvironment (application setup leaks)) instruction := by
        simp only [scheduler, position, located]
      have scheduled : ∀ command ∈ ((scheduler setup leaks watcher) execution.environmentRecall
          (execution.observeEnvironment (application setup leaks))).support,
          command.actor? (application setup leaks) = instructionActor instruction := by
        rw [schedulerEq]
        exact instruction_actor setup leaks watcher execution.environmentRecall
          (execution.observeEnvironment (application setup leaks)) instruction
      have one := (application setup leaks).control_round (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher) players
        (segment.length + rest.length) execution (instructionActor instruction) scheduled
      have start : (instruction :: segment).length + rest.length =
          segment.length + rest.length + 1 := by simp only [List.length_cons]; omega
      rw [count, start, Function.iterate_add_apply, one]
      have step : (application setup leaks).round
          (scheduler setup leaks watcher) players execution =
          (runtime setup).interactionStep leaks players
            ((runtime setup).reportNetwork leaks watcher) instruction execution := by
        simp only [ReactiveApplication.round, schedulerEq, interactionStep]
      rw [step, FinDist.map_eq_bind, FinDist.iterate_bind, runInteractionPlan, FinDist.map_bind]
      apply FinDist.bind_congr
      intro next reached
      apply ih (before ++ [instruction])
      · simpa only [List.append_assoc, List.singleton_append] using split
      · have advanced := (runtime setup).interactionStep_recall leaks players
          ((runtime setup).reportNetwork leaks watcher) instruction execution next reached
        simp only [List.length_append, List.length_singleton]
        omega

/-- An arbitrary finite-menu profile has the same state law as iteration of
the actual native control kernel, even before termination. -/
theorem menu_run_control_steps [Fintype Player]
    (responses : (application setup leaks).ResponseMenu) (watcher : Player)
    (profile : ∀ who, (responses.information (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).BehavioralPolicy who)
    (fuel : Nat) (history : (responses.protocol (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).History) :
    ((responses.information (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).runBehavioralFrom profile fuel history).map History.state =
      (fun law => law.bind ((application setup leaks).controlStep (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)
        (responses.decodeProfile (initialLaw setup) (horizon setup watcher)
          (scheduler setup leaks watcher) profile)))^[fuel] (FinDist.pure history.state) := by
  let app := application setup leaks
  let players := responses.decodeProfile (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) profile
  have encoded : (fun who => app.encodePolicy (players who)) =
      fun who => responses.embedPolicy (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) who (profile who) := by
    funext who
    exact app.encode_decodePolicy _
  calc
    _ = (((responses.information (initialLaw setup) (horizon setup watcher)
          (scheduler setup leaks watcher)).runBehavioralFrom profile fuel history).map
          (responses.toRawHistory (initialLaw setup) (horizon setup watcher)
            (scheduler setup leaks watcher))).map History.state := by
      rw [FinDist.map_comp]
      rfl
    _ = _ := by
      rw [responses.run_embed,
        ← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
        (app.information (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher))
        (app.singleMover (initialLaw setup) (horizon setup watcher)
          (scheduler setup leaks watcher)),
        ← encoded, app.run_map_state]
      rfl

/-- The actual native history law at a block boundary is exactly the initialized
service-prefix execution law. This holds for every response menu and profile. -/
theorem menu_prefix_state [Fintype Player]
    (responses : (application setup leaks).ResponseMenu) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (profile : ∀ who, (responses.information (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).BehavioralPolicy who)
    (count : Nat) (within : count ≤ (graph setup).order.eventCount) :
    ((responses.information (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).runBehavioral profile
        (blockOffset count + 2 * count + 1)).map History.state =
      (initialLaw setup).bind (fun state =>
        ((runtime setup).runInteractionPlan leaks
          (responses.decodeProfile (initialLaw setup) (horizon setup watcher)
            (scheduler setup leaks watcher) profile)
          ((runtime setup).reportNetwork leaks watcher) (planPrefix setup watcher count)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).map
            (fun execution =>
              some ⟨horizon setup watcher - blockOffset count, none, execution⟩)) := by
  rw [InformationModel.runBehavioral, menu_run_control_steps,
    Function.iterate_succ_apply, FinDist.pure_bind]
  change (fun law => law.bind ((application setup leaks).controlStep (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)
      (responses.decodeProfile (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) profile)))^[blockOffset count + 2 * count]
      ((initialLaw setup).map (fun state => some ⟨horizon setup watcher, none,
        ReactiveApplication.Execution.initial (application setup leaks) state⟩)) = _
  rw [FinDist.map_eq_bind, FinDist.iterate_bind]
  apply FinDist.bind_congr
  intro state _supported
  let rest := ((List.finRange (graph setup).order.eventCount).drop count).flatMap
    (block setup watcher)
  have split : plan setup watcher = planPrefix setup watcher count ++ rest := by
    have joined := congrArg (List.flatMap (block setup watcher))
      ((List.finRange (graph setup).order.eventCount).take_append_drop count)
    simpa only [plan, planPrefix, rest, List.flatMap_append] using joined.symm
  have lengths : horizon setup watcher =
      (planPrefix setup watcher count).length + rest.length := by
    change (plan setup watcher).length = _
    rw [split, List.length_append]
  have segment := segment_control_steps setup leaks watcher
    (responses.decodeProfile (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) profile) [] (planPrefix setup watcher count) rest
    (by simpa only [List.nil_append] using split)
    (ReactiveApplication.Execution.initial (application setup leaks) state) rfl
  rw [← lengths, planPrefix_length setup watcher reveals count within,
    planPrefix_actors_length setup watcher reveals count within] at segment
  have restLength : rest.length = horizon setup watcher - blockOffset count := by
    rw [planPrefix_length setup watcher reveals count within] at lengths
    omega
  rw [restLength] at segment
  exact segment

end Vegas
