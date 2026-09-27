/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterCounts
import Interaction.ReactiveScheduleClock
import Interaction.ReactiveRoundReachability

/-! # Actual protocol decisions under finite activation rosters

The full raw protocol retains every bounded response and passive observation.
The public roster fixes only who is activated at each scheduler position. Own
response recall therefore identifies the decision depth at every information
site, including sites outside an equilibrium's support.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_scheduled_actor (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (past : List (application setup leaks).EnvironmentEntry)
    (view : (application setup leaks).EnvironmentView)
    (command : (application setup leaks).Command)
    (supported : command ∈ (rosterScheduler setup leaks rosters network past view).support) :
    command.actor? (application setup leaks) =
      (((rosterPlan setup rosters).map instructionActor)[past.length]?).join := by
  unfold rosterScheduler at supported
  rw [List.getElem?_map]
  cases selected : (rosterPlan setup rosters)[past.length]? with
  | none =>
      rw [selected, FinDist.mem_support_pure] at supported
      subst command
      rfl
  | some instruction =>
      rw [selected] at supported
      have fixed : instruction ≠ .wire := by
        intro same
        obtain ⟨event, _, member⟩ := List.mem_flatMap.mp (List.mem_of_getElem? selected)
        exact rosterBlock_no_wire setup rosters event (same ▸ member)
      exact roster_instruction_actor setup leaks network past view instruction fixed
        command supported

/-- The common-depth certificate applies to the full bounded target menu
as well as each retained-response restriction. It needs no dedicated observer. -/
theorem roster_menu_common_depth (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (responses : (application setup leaks).ResponseMenu)
    (who : Player) (site : (responses.information (initialLaw setup)
      (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).InformationSite who) :
    ∃ depth, InformationModel.InformationSite.CommonDepth
      (responses.information (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)) site depth :=
  (application setup leaks).scheduled_menu_common_depth (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
      ((rosterPlan setup rosters).map instructionActor)
      (roster_scheduled_actor setup leaks rosters network) responses who site

/-- The plan-prefix evaluator realizes precisely the scheduler prefix at
initialization. All private recall and pending-network state remain in the law. -/
theorem roster_roundsFrom (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (players : Player → (application setup leaks).Policy)
    (count : Nat) (within : count ≤ (rosterPlan setup rosters).length) :
    (application setup leaks).roundsFrom (initialLaw setup)
        (rosterScheduler setup leaks rosters network) players count =
      (initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks players network
          ((rosterPlan setup rosters).take count)
          (ReactiveApplication.Execution.initial (application setup leaks) state) := by
  unfold ReactiveApplication.roundsFrom
  apply FinDist.bind_congr
  intro state _
  have length : ((rosterPlan setup rosters).take count).length = count :=
    List.length_take_of_le within
  simpa only [length] using roster_segment_rounds setup leaks rosters network players []
    ((rosterPlan setup rosters).take count) ((rosterPlan setup rosters).drop count)
    (by simp only [List.nil_append, List.take_append_drop])
    (ReactiveApplication.Execution.initial (application setup leaks) state) rfl

/-- Every legal decision is an actual partial round of the original service
under uniformly supported retained responses. No equilibrium support is required. -/
theorem roster_decision_supported (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (responses : (application setup leaks).ResponseMenu)
    (who : Player) (control : (application setup leaks).Control)
    (trace : (responses.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Trace (some control))
    (active : control.actor = some who) :
    ∃ count prior, count < (rosterPlan setup rosters).length ∧
      control.execution.environmentRecall.length = count + 1 ∧
      prior.environmentRecall.length = count ∧
      (rosterPlan setup rosters)[count]? = some (.player who) ∧
      prior ∈ ((initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks responses.uniformResponses network
          ((rosterPlan setup rosters).take count)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).support ∧
      control.execution ∈
        (prior.environmentStep (application setup leaks) (.activate who)).support := by
  have supported := responses.roundSupported_uniform (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) trace
  rcases control with ⟨remaining, actor, execution⟩
  change actor = some who at active
  subst actor
  obtain ⟨accounted, count, prior, command, position, priorSupport,
    commandSupport, actorEq, observed⟩ := supported
  have priorCount := (application setup leaks).roundsFrom_recall (initialLaw setup)
    (rosterScheduler setup leaks rosters network) responses.uniformResponses count prior
    priorSupport
  have within : count < (rosterPlan setup rosters).length := by omega
  have source := commandSupport
  change command ∈ (rosterScheduler setup leaks rosters network prior.environmentRecall
    (prior.observeEnvironment (application setup leaks))).support at source
  unfold rosterScheduler at source
  rw [priorCount] at source
  cases selected : (rosterPlan setup rosters)[count]? with
  | none =>
      rw [selected, FinDist.mem_support_pure] at source
      subst command
      cases actorEq
  | some instruction =>
      rw [selected] at source
      have fixed : instruction ≠ .wire := by
        intro same
        obtain ⟨event, _, member⟩ := List.mem_flatMap.mp (List.mem_of_getElem? selected)
        exact rosterBlock_no_wire setup rosters event (same ▸ member)
      have actorFound := roster_instruction_actor setup leaks network _ _ instruction fixed
        command source
      rw [actorEq] at actorFound
      have instructionEq : instruction = .player who := by
        cases instruction <;> simp_all [instructionActor]
      subst instruction
      change command ∈ (FinDist.pure (.activate who)).support at source
      cases FinDist.mem_support_pure.mp source
      refine ⟨count, prior, within, position, priorCount, selected, ?_, observed⟩
      rw [roster_roundsFrom setup leaks rosters network responses.uniformResponses count
        within.le] at priorSupport
      exact priorSupport

end Vegas.SourceProgram.RevealService
