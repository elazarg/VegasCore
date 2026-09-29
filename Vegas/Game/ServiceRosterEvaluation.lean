/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterMixing
import Interaction.ReactiveScheduleEvaluation

/-! # The finite roster game evaluates the physical runtime

Finite restriction agrees at every legal history. Exact prefix laws retain
the complete execution, and transfer physical support to uniformly retained
responses without requiring policy coverage at inconsistent inputs.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_restrict_prefix_state
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (menu : (application setup leaks).ResponseMenu)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who, menu.Admissible (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who (players who))
    (count : Nat) (within : count ≤ (rosterPlan setup rosters).length) :
    ((menu.information (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).runBehavioral
      (fun who => menu.restrictPolicy (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) who (players who))
      (count + (((rosterPlan setup rosters).take count).filterMap instructionActor).length + 1)).map
        History.state =
      ((initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks players network
          ((rosterPlan setup rosters).take count)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).map
        (fun next => some ⟨(rosterPlan setup rosters).length - count, none, next⟩) := by
  rw [InformationModel.runBehavioral, menu.run_restrict_control_steps _ _ _ players covered]
  have exactLaw := (application setup leaks).scheduled_prefix_control_steps (initialLaw setup)
    (rosterScheduler setup leaks rosters network) ((rosterPlan setup rosters).map instructionActor)
    (roster_scheduled_actor setup leaks rosters network) players count
      (by simpa only [List.length_map] using within)
  simp only [List.length_map, ← List.map_take, List.filterMap_map, Function.id_comp] at exactLaw
  rw [roster_roundsFrom setup leaks rosters network players count within] at exactLaw
  exact exactLaw

/-- The next scheduled activation is included, but its response has not yet
occurred. This is the actual finite game's law at a player decision, retaining
the private passive sample and complete response recall. -/
theorem roster_restrict_activation_state
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (menu : (application setup leaks).ResponseMenu)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who, menu.Admissible (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who (players who))
    (count : Nat) (who : Player)
    (selected : (rosterPlan setup rosters)[count]? = some (.player who)) :
    ((menu.information (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).runBehavioral
      (fun player => menu.restrictPolicy (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) player (players player))
      (count + (((rosterPlan setup rosters).take count).filterMap instructionActor).length + 2)).map
        History.state =
      (((initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks players network
          ((rosterPlan setup rosters).take count)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
        fun before => before.environmentStep (application setup leaks) (.activate who)).map
          (fun next => some ⟨(rosterPlan setup rosters).length - count - 1, some who, next⟩) := by
  have within : count < (rosterPlan setup rosters).length :=
    List.getElem?_eq_some_iff.mp selected |>.1
  rw [InformationModel.runBehavioral, menu.run_restrict_control_steps _ _ _ players covered]
  change (fun law => law.bind ((application setup leaks).controlStep (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) players))^[
      count + (((rosterPlan setup rosters).take count).filterMap instructionActor).length + 2]
        (PMF.pure none) = _
  have prefixLaw := (application setup leaks).scheduled_prefix_control_steps (initialLaw setup)
    (rosterScheduler setup leaks rosters network) ((rosterPlan setup rosters).map instructionActor)
    (roster_scheduled_actor setup leaks rosters network) players count
      (by simpa only [List.length_map] using within.le)
  simp only [List.length_map, ← List.map_take, List.filterMap_map, Function.id_comp] at prefixLaw
  rw [roster_roundsFrom setup leaks rosters network players count within.le] at prefixLaw
  rw [show count + (((rosterPlan setup rosters).take count).filterMap instructionActor).length + 2 =
      (count + (((rosterPlan setup rosters).take count).filterMap instructionActor).length + 1) + 1
      by omega, Function.iterate_succ_apply', prefixLaw, PMF.bind_map, PMF.map_bind,
    PMF.bind_bind]
  simp only [PMF.bind_bind]
  apply bind_congr_on_support _
  intro initial _
  apply bind_congr_on_support _
  intro before supported
  have position := (runtime setup).runInteractionPlan_recall leaks players network
    ((rosterPlan setup rosters).take count)
    (ReactiveApplication.Execution.initial (application setup leaks) initial) before supported
  have countEq : before.environmentRecall.length = count := by
    simpa only [ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_add,
      List.length_take_of_le within.le] using position
  have remaining : (rosterPlan setup rosters).length - count =
      ((rosterPlan setup rosters).length - count - 1) + 1 := by omega
  conv_lhs => rw [remaining]
  simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
    ReactiveApplication.transition, rosterScheduler, countEq, selected,
    interactionInstruction, PMF.pure_bind, ReactiveApplication.Command.actor?]

omit [Fintype Player] in
/-- The depth of an actual pending activation follows from its existing
scheduler recall and the public roster, without adding a clock observation. -/
theorem roster_decision_depth
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (menu : (application setup leaks).ResponseMenu)
    (who : Player) (control : (application setup leaks).Control)
    (trace : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Trace (some control))
    (active : control.actor = some who) (count : Nat)
    (position : control.execution.environmentRecall.length = count + 1) :
    trace.length = count +
      (((rosterPlan setup rosters).take count).filterMap instructionActor).length + 2 := by
  obtain ⟨found, located, selected, _, depth⟩ :=
    (application setup leaks).scheduled_decision_counts (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
      ((rosterPlan setup rosters).map instructionActor)
      (roster_scheduled_actor setup leaks rosters network) who control
      (menu.toRawTrace _ _ _ trace) active
  have same : found = count := by omega
  subst found
  rw [List.take_add_one, selected] at depth
  simp only [menu.toRawTrace_length, List.filterMap_append, Option.toList_some,
    List.filterMap_cons, List.filterMap_nil, id_eq, List.length_append,
    List.length_singleton, ← List.map_take, List.filterMap_map, Function.comp_def] at depth
  change trace.length = count + 1 +
    ((((rosterPlan setup rosters).take count).filterMap instructionActor).length + 1) at depth
  omega

omit [Fintype Player] in
theorem rosterPlanPrefix_isPrefix (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (count : Nat) :
    (rosterPlanPrefix setup rosters count).IsPrefix (rosterPlan setup rosters) := by
  refine ⟨((List.finRange (graph setup).order.eventCount).drop count).flatMap
    (rosterBlock setup rosters), ?_⟩
  simp only [rosterPlanPrefix, rosterPlan, ← List.flatMap_append, List.take_append_drop]

omit [Fintype Player] in
/-- Physical prefixes of an admissible implementation are also supported by
the uniformly retained service, including all environment and player recall. -/
theorem roster_restrict_prefix_support [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (menu : (application setup leaks).ResponseMenu)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who, menu.Admissible (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who (players who))
    (count : Nat) (finished : (application setup leaks).Execution)
    (supported : finished ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support) :
    finished ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks menu.uniformResponses network
        (rosterPlanPrefix setup rosters count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support := by
  let planPrefix := rosterPlanPrefix setup rosters count
  have before := rosterPlanPrefix_isPrefix setup rosters count
  have within : planPrefix.length ≤ (rosterPlan setup rosters).length := before.length_le
  have prefixEq : (rosterPlan setup rosters).take planPrefix.length = planPrefix := by
    obtain ⟨suffix, split⟩ := before
    rw [← split]
    exact List.take_left
  have reach : finished ∈ ((application setup leaks).roundsFrom (initialLaw setup)
      (rosterScheduler setup leaks rosters network) players planPrefix.length).support := by
    rw [roster_roundsFrom setup leaks rosters network players planPrefix.length within, prefixEq]
    exact supported
  have transferred := menu.restrict_scheduled_prefix_support (initialLaw setup)
    (rosterScheduler setup leaks rosters network) ((rosterPlan setup rosters).map instructionActor)
    (roster_scheduled_actor setup leaks rosters network) players
      (by simpa only [List.length_map] using covered) planPrefix.length
      (by simpa only [List.length_map] using within) finished reach
  rw [roster_roundsFrom setup leaks rosters network menu.uniformResponses planPrefix.length
    within, prefixEq] at transferred
  exact transferred

end Vegas
