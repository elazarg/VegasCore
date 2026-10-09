/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobRationality
import Vegas.Examples.LateOpeningRuntimeBobRawBinding
import Interaction.ReactiveTrafficIdentity
import Interaction.ReactiveReceiptIdentity

/-! # Hidden-history independence of the final native receiver response

At a clean last disclosure callback, a fixed raw response determines the
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
open LateOpeningRuntimeBobRawBinding (known_same_information)
open LateOpeningRuntimeLatePrefix (recorded recorded_clock)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def responsePhysical (execution : app.Execution) (response : app.Action) : app.State :=
  match response.transmission with
  | none => execution.application
  | some material =>
      let submitted := app.submit execution.application bob material
      (app.handle submitted ⟨(bob, execution.network.nextSerial bob),
        app.packet submitted bob (execution.network.known bob) material⟩).getD submitted

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

theorem latestAuthor_clean (decision : DecisionHistory weight nonnegative) :
    latestAuthor bob (decision.execution.observeEnvironment app) = .wait := by
  let execution := decision.execution
  have retained := app.retained_envelopes_mem_inputs execution
    (app.history_provenance initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace)
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace)
  have receiptIds := app.receipt_identifiers_history initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) _ decision.trace
  have absent : execution.network.pending.reverse.find?
      (fun message : Message Player app.Payload => decide (message.sender = bob ∧
        message.id ∉ execution.network.ledger.map Message.id)) = none := by
    apply List.find?_eq_none.mpr
    intro message member selected
    rw [List.mem_reverse] at member
    obtain ⟨owned, unpublished⟩ := of_decide_eq_true selected
    obtain ⟨_, _, accepted⟩ := decision.clean message (retained.pending message member) owned
    apply unpublished
    rw [← receiptIds]
    exact List.mem_map.mpr ⟨(message.id, true), accepted, rfl⟩
  unfold latestAuthor
  change (match execution.network.pending.reverse.find?
    (fun message : Message Player app.Payload => decide (message.sender = bob ∧
      message.id ∉ execution.network.ledger.map Message.id)) with
    | none => ReactiveApplication.Command.wait
    | some message => ReactiveApplication.Command.include message.id) = _
  rw [absent]

theorem serviced_round (decision : DecisionHistory weight nonnegative)
    (response : app.Action) (players : Player → app.Policy) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (decision.execution.respond app bob response) =
        PMF.pure (serviced decision.execution response) := by
  have chosen := protected_response_scheduler weight nonnegative
    ⟨6, some bob, decision.execution⟩ decision.trace bob rfl response (Or.inl rfl)
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      have selected : latestAuthor bob
          ((decision.execution.respond app bob ⟨none⟩).observeEnvironment app) = .wait :=
        latestAuthor_clean weight nonnegative decision
      rw [ReactiveApplication.round, chosen, selected, PMF.pure_bind,
        ReactiveApplication.dispatch]
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
      rfl
  | some material =>
      have serials := app.serialsBeforeNext_history (LateOpeningRuntimeService.scheduler
        weight nonnegative) initial LateOpeningRuntimeService.horizon decision.trace
      have selected := latestAuthor_after_submit decision.execution bob material serials
      rw [ReactiveApplication.round, chosen, selected, PMF.pure_bind,
        ReactiveApplication.dispatch]
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
      rfl

theorem serviced_physical (decision : DecisionHistory weight nonnegative)
    (response : app.Action) :
    (serviced decision.execution response).application =
      responsePhysical decision.execution response := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      have serials := app.serialsBeforeNext_history (LateOpeningRuntimeService.scheduler
        weight nonnegative) initial LateOpeningRuntimeService.horizon decision.trace
      have found := serials.lookup_submit bob
        (app.packet (app.submit decision.execution.application bob material) bob
          (decision.execution.network.known bob) material)
      have lookup : (decision.execution.respond app bob ⟨some material⟩).network.lookup
          (bob, decision.execution.network.nextSerial bob) =
        some ⟨(bob, decision.execution.network.nextSerial bob),
          app.packet (app.submit decision.execution.application bob material) bob
            (decision.execution.network.known bob) material⟩ := found
      change ((decision.execution.respond app bob ⟨some material⟩).includePending app
        (bob, decision.execution.network.nextSerial bob)).application = _
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      rw [lookup]
      rfl

theorem serviced_cursor (decision : DecisionHistory weight nonnegative)
    (response : app.Action) :
    (serviced decision.execution response).environmentRecall.length = 21 := by
  have cursor := final_cursor weight nonnegative decision.execution decision.trace
  cases response with
  | mk transmission =>
      cases transmission <;>
        simpa only [serviced, ReactiveApplication.Execution.respond,
          ReactiveApplication.Execution.includePending, List.length_append,
          List.length_singleton] using congrArg (fun value => value + 1) cursor

theorem responsePhysical_same_information (first second : app.Execution)
    (firstRecall : first.InputRecall app) (secondRecall : second.InputRecall app)
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
      have known := known_same_information first second firstRecall secondRecall sameRecall sameView
      have packets := LateOpeningRuntimeService.runtime.packet_playerView_congr leaks
        first.application second.application bob (first.network.known bob) material physicalView
      have emitted : app.packet (app.submit first.application bob material) bob
          (first.network.known bob) material =
        app.packet (app.submit second.application bob material) bob
          (second.network.known bob) material := by
        rw [← known]
        exact packets
      apply LateOpeningRuntimeService.runtime.reactive_handle_result_playerView_congr leaks
        _ _ bob (first.network.nextSerial bob) (second.network.nextSerial bob) _ _
          (congrArg WitnessedPacket.call emitted) (congrArg WitnessedPacket.tokenValid emitted)
            submitted

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

theorem continuation_owner_same_information
    (first second : DecisionHistory weight nonnegative)
    (sameRecall : first.execution.recall bob = second.execution.recall bob)
    (sameView : first.execution.observe app bob = second.execution.observe app bob)
    (response : app.Action) (firstPlayers secondPlayers : Player → app.Policy) :
    (continuation weight nonnegative first response firstPlayers).map
      (fun final => final.application.playerView bob) =
    (continuation weight nonnegative second response secondPlayers).map
      (fun final => final.application.playerView bob) := by
  unfold continuation
  change PMF.map _ (PMF.bind (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
    firstPlayers (first.execution.respond app bob response))
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) firstPlayers 5)) =
    PMF.map _ (PMF.bind (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      secondPlayers (second.execution.respond app bob response))
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) secondPlayers 5))
  rw [serviced_round weight nonnegative first response firstPlayers,
    serviced_round weight nonnegative second response secondPlayers,
    PMF.pure_bind, PMF.pure_bind]
  apply tail_owner_same_information weight nonnegative _ _
    (serviced_cursor weight nonnegative first response)
    (serviced_cursor weight nonnegative second response) _ firstPlayers secondPlayers
  rw [serviced_physical weight nonnegative first response,
    serviced_physical weight nonnegative second response]
  exact responsePhysical_same_information first.execution second.execution
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) first.trace)
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) second.trace)
        sameRecall sameView response

end Vegas.Examples.LateOpeningRuntimeBobFinalObservation
