/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingInformation
import Vegas.Pending.ReactiveContinuationObservation
import Interaction.ReactiveOwnerSelection

/-! # A fixed raw response at Bob's first binding

The actual author service immediately consumes every raw submission. Its
application result depends only on Bob's current information and the chosen
response, including the private material he registers and the packets he
already knows. Consequently a fixed response cannot select different bound
answers in hidden histories having the same complete Bob information.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobRawBinding

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeBobBindingService LateOpeningRuntimeBobBindingInformation

/-- The physical result of Bob's immediate author service. -/
def responsePhysical (execution : app.Execution) (response : app.Action) : app.State :=
  match response.transmission with
  | none => execution.application
  | some material =>
      let submitted := app.submit execution.application bob material
      (app.handle submitted ⟨(bob, 0),
        app.packet submitted bob (execution.network.known bob) material⟩).getD submitted

/-- The actual transport state after the first binding response and its
immediate receipt. The pre-inclusion public view is retained in scheduler recall. -/
def serviced (execution : app.Execution) (response : app.Action) : app.Execution :=
  let submitted := execution.respond app bob response
  let command := match response.transmission with
    | none => ReactiveApplication.Command.wait
    | some _ => ReactiveApplication.Command.include (bob, 0)
  let included := match response.transmission with
    | none => submitted
    | some _ => submitted.includePending app (bob, 0)
  { included with environmentRecall := submitted.environmentRecall ++
    [⟨submitted.observeEnvironment app, command⟩] }

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem serviced_round (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩)) (quiet : SilentRecall execution)
    (response : app.Action) (players : Player → app.Policy) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (execution.respond app bob response) = PMF.pure (serviced execution response) := by
  have chosen := protected_response_scheduler weight nonnegative
    ⟨14, some bob, execution⟩ trace bob rfl response (Or.inl rfl)
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      have selected : latestAuthor bob
          ((execution.respond app bob ⟨none⟩).observeEnvironment app) = .wait :=
        latestAuthor_bob_wait_of_active weight nonnegative ⟨14, some bob, execution⟩ trace
          (by simp)
      rw [ReactiveApplication.round, chosen, selected, PMF.pure_bind,
        ReactiveApplication.dispatch]
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
      rfl
  | some material =>
      have serials := app.serialsBeforeNext_history
        (LateOpeningRuntimeService.scheduler weight nonnegative) initial
          LateOpeningRuntimeService.horizon trace
      have selected := latestAuthor_after_submit execution bob material serials
      rw [(silent_resources weight nonnegative _ trace quiet).1] at selected
      rw [ReactiveApplication.round, chosen, selected, PMF.pure_bind,
        ReactiveApplication.dispatch]
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
      rfl

theorem serviced_physical (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩)) (quiet : SilentRecall execution)
    (response : app.Action) :
    (serviced execution response).application = responsePhysical execution response := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      have serials := app.serialsBeforeNext_history
        (LateOpeningRuntimeService.scheduler weight nonnegative) initial
          LateOpeningRuntimeService.horizon trace
      have zero := (silent_resources weight nonnegative _ trace quiet).1
      have found := serials.lookup_submit bob
        (app.packet (app.submit execution.application bob material) bob
          (execution.network.known bob) material)
      rw [zero] at found
      have lookup : (execution.respond app bob ⟨some material⟩).network.lookup (bob, 0) =
          some ⟨(bob, execution.network.nextSerial bob),
            app.packet (app.submit execution.application bob material) bob
              (execution.network.known bob) material⟩ := by
        rw [zero]
        exact found
      change ((execution.respond app bob ⟨some material⟩).includePending app
        (bob, 0)).application = _
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      rw [lookup]
      change (app.handle (app.submit execution.application bob material)
        ⟨(bob, execution.network.nextSerial bob),
          app.packet (app.submit execution.application bob material) bob
            (execution.network.known bob) material⟩).getD _ = _
      rw [zero]
      rfl

theorem serviced_trace (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩)) (quiet : SilentRecall execution)
    (response : app.Action) :
    Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨13, none, serviced execution response⟩)) := by
  obtain ⟨responded⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 execution bob response trace
  apply app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (fun _ => app.silentPolicy)
      13 1 _ _ responded
  simp only [ReactiveApplication.runRounds, PMF.bind_pure,
    serviced_round weight nonnegative execution trace quiet response, PMF.mem_support_pure_iff]

theorem continuation_split (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩)) (quiet : SilentRecall execution)
    (response : app.Action) (players : Player → app.Policy) :
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 14
      (execution.respond app bob response) =
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 13
      (serviced execution response) := by
  change ((app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
    (execution.respond app bob response)).bind
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 13)) = _
  rw [serviced_round weight nonnegative execution trace quiet response players, PMF.pure_bind]

theorem known_same_information (first second : app.Execution)
    (firstValid : first.InputRecall app) (secondValid : second.InputRecall app)
    (sameRecall : first.recall bob = second.recall bob)
    (sameView : first.observe app bob = second.observe app bob) :
    first.network.known bob = second.network.known bob := by
  rw [app.known_from_recall first bob firstValid,
    app.known_from_recall second bob secondValid, sameRecall]
  have networkView := congrArg ReactiveApplication.PlayerView.messages sameView
  have leaked := congrArg MessageNetwork.PlayerView.leaked networkView
  have ledger := congrArg MessageNetwork.PlayerView.ledger networkView
  change first.network.leaked bob = second.network.leaked bob at leaked
  change first.network.ledger = second.network.ledger at ledger
  rw [leaked, ledger]

/-- Private initialization and unobserved foreign traffic cannot change the
bound result of a fixed response at one complete information class. -/
theorem responsePhysical_same_view (first second : app.Execution)
    (firstValid : first.InputRecall app) (secondValid : second.InputRecall app)
    (sameRecall : first.recall bob = second.recall bob)
    (sameView : first.observe app bob = second.observe app bob) (response : app.Action) :
    (responsePhysical first response).playerView bob =
      (responsePhysical second response).playerView bob := by
  have physicalView := congrArg ReactiveApplication.PlayerView.application sameView
  change first.application.playerView bob = second.application.playerView bob at physicalView
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact physicalView
  | some material =>
      have submitted := LateOpeningRuntimeService.runtime.submit_playerView_congr leaks
        first.application second.application bob material physicalView
      have known := known_same_information first second firstValid secondValid sameRecall sameView
      have packets := LateOpeningRuntimeService.runtime.packet_playerView_congr leaks
        first.application second.application bob (first.network.known bob) material physicalView
      have emitted : app.packet (app.submit first.application bob material) bob
          (first.network.known bob) material =
        app.packet (app.submit second.application bob material) bob
          (second.network.known bob) material := by
        rw [← known]
        exact packets
      apply LateOpeningRuntimeService.runtime.reactive_handle_result_playerView_congr leaks
        _ _ bob 0 0 _ _ (congrArg WitnessedPacket.call emitted)
          (congrArg WitnessedPacket.tokenValid emitted) submitted

/-- A response fixes a single typed binding result throughout the actual
failed-publication information class, without fixing Bob's posterior. -/
theorem response_result_same_information
    (first second : DecisionHistory weight nonnegative)
    (sameRecall : first.execution.recall bob = second.execution.recall bob)
    (sameView : first.execution.observe app bob = second.execution.observe app bob)
    (response : app.Action) :
    (serviced first.execution response).application.config.store (.inr bobBindEvent) =
      (serviced second.execution response).application.config.store (.inr bobBindEvent) := by
  rw [serviced_physical weight nonnegative _ first.trace first.quiet,
    serviced_physical weight nonnegative _ second.trace second.quiet]
  have same := responsePhysical_same_view first.execution second.execution
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) first.trace)
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) second.trace)
      sameRecall sameView response
  have stores := congrArg (fun view : PlayerView nativeGraph => view.observation.store) same
  have visible : nativeGraph.fieldVisibleTo bob (.inr bobBindEvent) := by decide
  have stored := congrFun stores (.inr bobBindEvent)
  change nativeGraph.playerStore bob (responsePhysical first.execution response).config.store
      (.inr bobBindEvent) =
    nativeGraph.playerStore bob (responsePhysical second.execution response).config.store
      (.inr bobBindEvent) at stored
  simpa only [nativeGraph.playerStore_of_visible bob _ _ visible] using
    stored

end Vegas.Examples.LateOpeningRuntimeBobRawBinding
