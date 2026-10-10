/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobRationality
import Vegas.Examples.LateOpeningRuntimeBobSubmissionService
import Interaction.ReactiveTrafficIdentity
import Interaction.ReactiveReceiptIdentity

/-! # Hidden-history independence of the final native receiver response

At any actual last disclosure callback, a fixed raw response determines the
whole terminal owner observation. The only remaining service commands are
immediate author inclusion, four clock ticks and disclosure expiry. Hidden
initial labels and unseen foreign packets cannot change that readout law.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobFinalObservation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobService
  LateOpeningRuntimeBobAudit LateOpeningRuntimeBobIncentive LateOpeningRuntimeBobInformation
open LateOpeningRuntimeBobResponseState (responseState)
open LateOpeningRuntimeLatePrefix (recorded recorded_clock)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def serviced (execution : app.Execution) (response : app.Action) : app.Execution :=
  let submitted := execution.respond app bob response
  let command := match response.transmission with
    | none => ReactiveApplication.Command.wait
    | some _ => ReactiveApplication.Command.include (bob, execution.network.nextSerial bob)
  let included := match response.transmission with
    | none => submitted
    | some _ => submitted.includePending app (bob, execution.network.nextSerial bob)
  { included with environmentRecall := submitted.environmentRecall ++
    [⟨submitted.observeEnvironment app, command⟩] }

theorem serviced_round (remaining : Nat) (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨remaining, some bob, execution⟩))
    (response : app.Action) (players : Player → app.Policy) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players (execution.respond
      app bob response) =
      PMF.pure (serviced execution response) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      have chosen := protected_response_scheduler weight nonnegative
        ⟨remaining, some bob, execution⟩ trace bob rfl ⟨none⟩ (Or.inl rfl)
      have selected : latestAuthor bob
          ((execution.respond app bob ⟨none⟩).observeEnvironment app) = .wait := by
        change latestAuthor bob (execution.observeEnvironment app) = .wait
        exact latestAuthor_bob_wait_of_active weight nonnegative
          ⟨remaining, some bob, execution⟩ trace (by simp)
      rw [ReactiveApplication.round, chosen, selected, PMF.pure_bind,
        ReactiveApplication.dispatch]
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
      rfl
  | some material =>
      exact LateOpeningRuntimeBobSubmissionService.submission_round
        weight nonnegative remaining execution trace material players

theorem serviced_physical (remaining : Nat) (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨remaining, some bob, execution⟩))
    (response : app.Action) :
    (serviced execution response).application = responseState execution response := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      exact LateOpeningRuntimeBobSubmissionService.submission_physical
        weight nonnegative remaining execution trace material

theorem serviced_cursor (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨6, some bob, execution⟩))
    (response : app.Action) : (serviced execution response).environmentRecall.length = 21 := by
  have cursor := LateOpeningRuntimeBobService.final_cursor weight nonnegative execution trace
  rcases response with ⟨transmission⟩
  cases transmission <;> simp only [serviced, ReactiveApplication.respond_environmentRecall,
    List.length_append, List.length_singleton, cursor]

private def tick (execution : app.Execution) : app.Execution :=
  recorded execution (.application .advanceClock)
    { execution.application with clock := execution.application.clock + 1 }

private theorem tick_view (first second : app.Execution)
    (same : first.application.playerView bob = second.application.playerView bob) :
    (tick first).application.playerView bob = (tick second).application.playerView bob := by
  have maintained := LateOpeningRuntimeService.runtime.maintenance_playerView_congr
    first.application second.application bob .advanceClock (by intro event; simp) same
  simp only [EventGraphRuntime.environmentStep, PMF.pure_map] at maintained
  have sameLaw : PMF.pure ((tick first).application.playerView bob) =
      PMF.pure ((tick second).application.playerView bob) := maintained
  have member : (tick first).application.playerView bob ∈
      (PMF.pure ((tick first).application.playerView bob)).support :=
    (PMF.mem_support_pure_iff _ _).mpr rfl
  rw [sameLaw] at member
  exact (PMF.mem_support_pure_iff _ _).mp member

private theorem clock_round (players : Player → app.Policy) (execution : app.Execution)
    (position : Fin 4) (cursor : execution.environmentRecall.length = 21 + position.val) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players execution =
      PMF.pure (tick execution) := by
  have selected : stageChoice weight nonnegative (21 + position.val)
      (execution.observeEnvironment app) = PMF.pure (.application .advanceClock) := by
    fin_cases position <;> rfl
  exact (LateOpeningRuntimeLatePrefix.fixed_round weight nonnegative players execution
    (tick execution) (21 + position.val) (.application .advanceClock) cursor selected
      (recorded_clock execution)).trans rfl

private theorem expiry_round (players : Player → app.Policy) (execution : app.Execution)
    (cursor : execution.environmentRecall.length = 25) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players execution =
      execution.environmentStep app (.application (.expire bobRevealEvent)) := by
  have chosen : LateOpeningRuntimeService.scheduler weight nonnegative execution.environmentRecall
      (execution.observeEnvironment app) = PMF.pure (.application (.expire bobRevealEvent)) := by
    change stageChoice weight nonnegative execution.environmentRecall.length _ = _
    rw [cursor]
    rfl
  rw [ReactiveApplication.round, chosen, PMF.pure_bind, ReactiveApplication.dispatch]
  change (execution.environmentStep app (.application (.expire bobRevealEvent))).bind
    (fun next => PMF.pure next) = _
  rw [PMF.bind_pure]

theorem tail_owner_law (players : Player → app.Policy) (execution : app.Execution)
    (cursor : execution.environmentRecall.length = 21) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 5
      execution).map (fun final => final.application.playerView bob) =
    (app.environment (tick (tick (tick (tick execution)))).application
      (.expire bobRevealEvent)).map (fun physical => physical.playerView bob) := by
  have next1 : (tick execution).environmentRecall.length = 22 := by
    simpa only [tick, recorded, List.length_append, List.length_singleton] using
      congrArg (fun value => value + 1) cursor
  have next2 : (tick (tick execution)).environmentRecall.length = 23 := by
    simpa only [tick, recorded, List.length_append, List.length_singleton] using
      congrArg (fun value => value + 1) next1
  have next3 : (tick (tick (tick execution))).environmentRecall.length = 24 := by
    simpa only [tick, recorded, List.length_append, List.length_singleton] using
      congrArg (fun value => value + 1) next2
  have next4 : (tick (tick (tick (tick execution)))).environmentRecall.length = 25 := by
    simpa only [tick, recorded, List.length_append, List.length_singleton] using
      congrArg (fun value => value + 1) next3
  change PMF.map _ (PMF.bind
    (app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players execution)
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 4)) = _
  rw [clock_round weight nonnegative players execution 0 cursor, PMF.pure_bind]
  change PMF.map _ (PMF.bind
    (app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players (tick execution))
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 3)) = _
  rw [clock_round weight nonnegative players (tick execution) 1 next1, PMF.pure_bind]
  change PMF.map _ (PMF.bind (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
    players (tick (tick execution)))
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 2)) = _
  rw [clock_round weight nonnegative players (tick (tick execution)) 2 next2, PMF.pure_bind]
  change PMF.map _ (PMF.bind (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
    players (tick (tick (tick execution))))
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 1)) = _
  rw [clock_round weight nonnegative players (tick (tick (tick execution))) 3 next3, PMF.pure_bind]
  simp only [ReactiveApplication.runRounds, PMF.bind_pure]
  rw [expiry_round weight nonnegative players (tick (tick (tick (tick execution)))) next4]
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
  rfl

theorem tail_owner_same_information (first second : app.Execution)
    (firstCursor : first.environmentRecall.length = 21)
    (secondCursor : second.environmentRecall.length = 21)
    (same : first.application.playerView bob = second.application.playerView bob)
    (firstPlayers secondPlayers : Player → app.Policy) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) firstPlayers 5
      first).map (fun final => final.application.playerView bob) =
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) secondPlayers 5
      second).map (fun final => final.application.playerView bob) := by
  rw [tail_owner_law weight nonnegative firstPlayers first firstCursor,
    tail_owner_law weight nonnegative secondPlayers second secondCursor]
  exact LateOpeningRuntimeService.runtime.maintenance_playerView_congr _ _ bob
    (.expire bobRevealEvent) (by intro event; simp)
      (tick_view _ _ (tick_view _ _ (tick_view _ _ (tick_view _ _ same))))

theorem continuation_owner_same_information (first second : app.Execution)
    (firstTrace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨6, some bob, first⟩))
    (secondTrace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨6, some bob, second⟩))
    (sameRecall : first.recall bob = second.recall bob)
    (sameView : first.observe app bob = second.observe app bob)
    (response : app.Action) (firstPlayers secondPlayers : Player → app.Policy) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) firstPlayers 6
      (first.respond app bob response)).map (fun final => final.application.playerView bob) =
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) secondPlayers 6
      (second.respond app bob response)).map (fun final => final.application.playerView bob) := by
  change PMF.map _ (PMF.bind (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
    firstPlayers (first.respond app bob response))
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) firstPlayers 5)) =
    PMF.map _ (PMF.bind (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      secondPlayers (second.respond app bob response))
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) secondPlayers 5))
  rw [serviced_round weight nonnegative 6 first firstTrace response firstPlayers,
    serviced_round weight nonnegative 6 second secondTrace response secondPlayers,
    PMF.pure_bind, PMF.pure_bind]
  apply tail_owner_same_information weight nonnegative _ _
    (serviced_cursor weight nonnegative first firstTrace response)
    (serviced_cursor weight nonnegative second secondTrace response) _ firstPlayers secondPlayers
  rw [serviced_physical weight nonnegative 6 first firstTrace response,
    serviced_physical weight nonnegative 6 second secondTrace response]
  exact LateOpeningRuntimeBobResponseState.responseState_same_view first second
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) firstTrace)
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) secondTrace)
      sameRecall sameView response
end Vegas.Examples.LateOpeningRuntimeBobFinalObservation
