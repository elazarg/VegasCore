/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobFinalFiberRationality
import Interaction.ReactiveEmissionOrder

/-! # Final settled receiver records on a complete information class

The terminal owner observation alone does not determine audit collection.
At the final clean callback, exact own recall also fixes authored envelopes,
their next authenticated identifier, and the new inclusion receipt. The later
clock and expiry commands change neither inputs nor receipts. Consequently
the full-record receiver audit law agrees across all compatible hidden histories.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobFinalAuditObservation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeBobService LateOpeningRuntimeBobAudit LateOpeningRuntimeBobIncentive
  LateOpeningRuntimeBobInformation LateOpeningRuntimeBobFinalObservation
open LateOpeningRuntimeBobRawBinding (known_same_information)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

abbrev AuditKey := PublicView nativeGraph ×
  List (MessageId Player × Bool) × List (Message Player app.Payload)

def auditKey (execution : app.Execution) : AuditKey :=
  ⟨execution.application.publicView, execution.receipts,
    execution.network.inputs.filter (fun message => message.sender = bob)⟩

open Classical in
def keyCharge (key : AuditKey) : ℝ :=
  if key.1.missedBindingBy bob then 1 else
    if ∃ message ∈ key.2.2, (⟨key.1, key.2.1⟩ : SettledRecord nativeGraph).permits message = false
      then 1 else 0

def fullCharge (execution : app.Execution) : ℝ :=
  TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
      (app.finished execution) bob

theorem fullCharge_eq_keyCharge (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control)) :
    fullCharge control.execution = keyCharge (auditKey control.execution) := by
  classical
  have inputs := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change (app.executionTraffic control.execution).map ReactiveApplication.TrafficRecord.envelope =
    control.execution.network.inputs at inputs
  change TerminalAudit.charge _ _ (app.finished control.execution) bob = _
  change TerminalAudit.charge _ _
    (some (show app.Control from ⟨0, none, control.execution⟩)) bob = _
  change TerminalAudit.charge _
    (LateOpeningRuntimeService.runtime.serviceAudit leaks fun record =>
      app.sampledTrafficAudit
        (fun traffic => ((record, traffic.envelope) : SettledEvidence setup .sequential))
        (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
        (fun actual => PMF.pure actual)) _ bob = _
  rw [LateOpeningRuntimeService.runtime.serviceAudit_charge]
  unfold keyCharge auditKey
  split
  · rfl
  · rw [app.sampledTrafficAudit_collection, PMF.toOuterMeasure_pure_apply]
    have violation :
        (∃ evidence ∈ (app.executionTraffic control.execution).map
            (fun traffic => ((LateOpeningRuntimeService.runtime.settledRecord leaks
              control.execution, traffic.envelope) : SettledEvidence setup .sequential)),
          evidence.2.sender = bob ∧ evidence.1.permits evidence.2 = false) ↔
        ∃ message ∈ control.execution.network.inputs.filter
            (fun message => message.sender = bob),
          (⟨control.execution.application.publicView, control.execution.receipts⟩ :
            SettledRecord nativeGraph).permits message = false := by
      constructor
      · rintro ⟨evidence, member, owner, denied⟩
        obtain ⟨traffic, present, rfl⟩ := List.mem_map.mp member
        refine ⟨traffic.envelope, List.mem_filter.mpr ⟨?_, by simpa using owner⟩, denied⟩
        rw [← inputs]
        exact List.mem_map.mpr ⟨traffic, present, rfl⟩
      · rintro ⟨message, member, denied⟩
        obtain ⟨present, owner⟩ := List.mem_filter.mp member
        rw [← inputs, List.mem_map] at present
        obtain ⟨traffic, present, rfl⟩ := present
        exact ⟨_, List.mem_map.mpr ⟨traffic, present, rfl⟩, by simpa using owner, denied⟩
    simp only [Set.mem_ofPred_eq, violation]
    split <;> norm_num

private theorem serial_same_recall (first second : DecisionHistory weight nonnegative)
    (sameRecall : first.execution.recall bob = second.execution.recall bob) :
    first.execution.network.nextSerial bob = second.execution.network.nextSerial bob := by
  have firstOrder := app.emissionOrder_history
    (LateOpeningRuntimeService.scheduler weight nonnegative) initial
      LateOpeningRuntimeService.horizon first.trace
  have secondOrder := app.emissionOrder_history
    (LateOpeningRuntimeService.scheduler weight nonnegative) initial
      LateOpeningRuntimeService.horizon second.trace
  change first.execution.EmissionOrder app at firstOrder
  change second.execution.EmissionOrder app at secondOrder
  have lengths := congrArg List.length ((firstOrder bob).symm.trans
    ((congrArg (fun past => (app.outputs past).map Message.id) sameRecall).trans (secondOrder bob)))
  simpa only [List.length_map, List.length_range] using lengths

private theorem emitted_same_information (first second : DecisionHistory weight nonnegative)
    (sameRecall : first.execution.recall bob = second.execution.recall bob)
    (sameView : first.execution.observe app bob = second.execution.observe app bob)
    (material : app.Submission) :
    app.packet (app.submit first.execution.application bob material) bob
      (first.execution.network.known bob) material =
    app.packet (app.submit second.execution.application bob material) bob
      (second.execution.network.known bob) material := by
  have physicalView : first.execution.application.playerView bob =
      second.execution.application.playerView bob :=
    congrArg ReactiveApplication.PlayerView.application sameView
  have known := known_same_information first.execution second.execution
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) first.trace)
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) second.trace) sameRecall sameView
  rw [← known]
  exact LateOpeningRuntimeService.runtime.packet_playerView_congr leaks _ _ bob _ material
    physicalView

private theorem handle_acceptance_same_information
    (first second : DecisionHistory weight nonnegative)
    (sameRecall : first.execution.recall bob = second.execution.recall bob)
    (sameView : first.execution.observe app bob = second.execution.observe app bob)
    (material : app.Submission) :
    (app.handle (app.submit first.execution.application bob material)
      ⟨(bob, first.execution.network.nextSerial bob),
        app.packet (app.submit first.execution.application bob material) bob
          (first.execution.network.known bob) material⟩).isSome =
    (app.handle (app.submit second.execution.application bob material)
      ⟨(bob, second.execution.network.nextSerial bob),
        app.packet (app.submit second.execution.application bob material) bob
          (second.execution.network.known bob) material⟩).isSome := by
  have emitted := emitted_same_information weight nonnegative first second sameRecall sameView
    material
  have serial := serial_same_recall weight nonnegative first second sameRecall
  have physicalView : first.execution.application.playerView bob =
      second.execution.application.playerView bob :=
    congrArg ReactiveApplication.PlayerView.application sameView
  have submitted := LateOpeningRuntimeService.runtime.submit_playerView_congr leaks _ _ bob
    material physicalView
  rw [← emitted, ← serial]
  simp only [EventGraphRuntime.reactiveApplication_handle]
  split
  · have same := LateOpeningRuntimeService.runtime.handle_playerView_congr_of_sender _ _ bob
      ⟨(bob, first.execution.network.nextSerial bob),
        (app.packet (app.submit first.execution.application bob material) bob
          (first.execution.network.known bob) material).call⟩ submitted rfl
    simpa only [Option.isSome_map] using congrArg Option.isSome same
  · rfl

theorem serviced_receipts_same_information (first second : DecisionHistory weight nonnegative)
    (sameRecall : first.execution.recall bob = second.execution.recall bob)
    (sameView : first.execution.observe app bob = second.execution.observe app bob)
    (response : app.Action) :
    (serviced first.execution response).receipts =
      (serviced second.execution response).receipts := by
  have old := congrArg ReactiveApplication.PlayerView.receipts sameView
  change first.execution.receipts = second.execution.receipts at old
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact old
  | some material =>
      have firstSerials := app.serialsBeforeNext_history
        (LateOpeningRuntimeService.scheduler weight nonnegative) initial
          LateOpeningRuntimeService.horizon first.trace
      have secondSerials := app.serialsBeforeNext_history
        (LateOpeningRuntimeService.scheduler weight nonnegative) initial
          LateOpeningRuntimeService.horizon second.trace
      have accepted := handle_acceptance_same_information weight nonnegative first second
        sameRecall sameView material
      have serial := serial_same_recall weight nonnegative first second sameRecall
      have firstFound : (first.execution.respond app bob ⟨some material⟩).network.lookup
          (bob, first.execution.network.nextSerial bob) = some
          ⟨(bob, first.execution.network.nextSerial bob),
            app.packet (app.submit first.execution.application bob material) bob
              (first.execution.network.known bob) material⟩ := firstSerials.lookup_submit bob _
      have secondFound : (second.execution.respond app bob ⟨some material⟩).network.lookup
          (bob, second.execution.network.nextSerial bob) = some
          ⟨(bob, second.execution.network.nextSerial bob),
            app.packet (app.submit second.execution.application bob material) bob
              (second.execution.network.known bob) material⟩ := secondSerials.lookup_submit bob _
      unfold serviced
      change ((first.execution.respond app bob ⟨some material⟩).includePending app
          (bob, first.execution.network.nextSerial bob)).receipts =
        ((second.execution.respond app bob ⟨some material⟩).includePending app
          (bob, second.execution.network.nextSerial bob)).receipts
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      rw [firstFound, secondFound]
      change first.execution.receipts ++
          [((bob, first.execution.network.nextSerial bob),
            (app.handle (app.submit first.execution.application bob material) _).isSome)] =
        second.execution.receipts ++
          [((bob, second.execution.network.nextSerial bob),
            (app.handle (app.submit second.execution.application bob material) _).isSome)]
      rw [old, accepted, serial]

private theorem tail_commands (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (later : 21 ≤ past.length) (command : app.Command)
    (selected : command ∈
      (LateOpeningRuntimeService.scheduler weight nonnegative past view).support) :
    command = .wait ∨ ∃ maintenance, command = .application maintenance := by
  change command ∈ (stageChoice weight nonnegative past.length view).support at selected
  generalize located : past.length = position at later selected
  by_cases inside : position < 26
  · interval_cases position
    all_goals simp only [stageChoice, PMF.mem_support_pure_iff] at selected
    all_goals subst command; exact Or.inr ⟨_, rfl⟩
  · have idle : stageChoice weight nonnegative position view = PMF.pure .wait := by
      unfold stageChoice
      split <;> first | omega | rfl
    rw [idle, PMF.mem_support_pure_iff] at selected
    exact Or.inl selected

theorem tail_preserves_receipts (players : Player → app.Policy) (count : Nat)
    (execution final : app.Execution) (later : 21 ≤ execution.environmentRecall.length)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players count execution).support) : final.receipts = execution.receipts := by
  induction count generalizing execution with
  | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; rfl
  | succ count ih =>
      obtain ⟨next, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have length := app.round_environmentRecall_length
        (LateOpeningRuntimeService.scheduler weight nonnegative) players execution next moved
      have retained := ih next (by omega) continued
      change next ∈ (app.round _ players execution).support at moved
      rw [ReactiveApplication.round] at moved
      obtain ⟨command, selected, dispatched⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      rcases tail_commands weight nonnegative _ _ later command selected with rfl |
        ⟨maintenance, rfl⟩
      · change next ∈ ((execution.environmentStep app .wait).bind PMF.pure).support at dispatched
        rw [PMF.bind_pure] at dispatched
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
          PMF.mem_support_pure_iff] at dispatched
        subst next
        exact retained
      · change next ∈ ((execution.environmentStep app (.application maintenance)).bind
          PMF.pure).support at dispatched
        rw [PMF.bind_pure] at dispatched
        obtain ⟨updated, observed, rfl⟩ := PMF.support_map .. ▸ dispatched
        obtain ⟨physical, physicalReached, rfl⟩ := PMF.support_map .. ▸ observed
        exact retained

private theorem serviced_inputs_same_information (first second : DecisionHistory weight nonnegative)
    (sameRecall : first.execution.recall bob = second.execution.recall bob)
    (sameView : first.execution.observe app bob = second.execution.observe app bob)
    (response : app.Action) :
    (serviced first.execution response).network.inputs.filter
        (fun message => message.sender = bob) =
    (serviced second.execution response).network.inputs.filter (fun message => message.sender = bob)
      := by
  have firstRecall := app.history_inputRecall initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) first.trace
  have secondRecall := app.history_inputRecall initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) second.trace
  change first.execution.InputRecall app at firstRecall
  change second.execution.InputRecall app at secondRecall
  have old := (firstRecall bob).trans
    ((congrArg (app.outputs) sameRecall).trans (secondRecall bob).symm)
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact old
  | some material =>
      have emitted := emitted_same_information weight nonnegative first second sameRecall sameView
        material
      have serial := serial_same_recall weight nonnegative first second sameRecall
      change ((first.execution.respond app bob ⟨some material⟩).includePending app
          (bob, first.execution.network.nextSerial bob)).network.inputs.filter _ =
        ((second.execution.respond app bob ⟨some material⟩).includePending app
          (bob, second.execution.network.nextSerial bob)).network.inputs.filter _
      rw [app.includePending_network, app.includePending_network]
      have retained (network : MessageNetwork Player app.Payload) (identifier : MessageId Player) :
          (network.includePending identifier).2.inputs = network.inputs := by
        unfold MessageNetwork.includePending
        split <;> rfl
      rw [retained, retained]
      change (first.execution.network.inputs ++
          [(⟨(bob, first.execution.network.nextSerial bob),
            app.packet (app.submit first.execution.application bob material) bob
              (first.execution.network.known bob) material⟩ : Message Player app.Payload)]).filter _
          =
        (second.execution.network.inputs ++
          [(⟨(bob, second.execution.network.nextSerial bob),
            app.packet (app.submit second.execution.application bob material) bob
              (second.execution.network.known bob) material⟩ : Message Player app.Payload)]).filter
          _
      rw [List.filter_append, List.filter_append, old, serial, emitted]

theorem continuation_auditKey_law (decision : DecisionHistory weight nonnegative)
    (response : app.Action) (players : Player → app.Policy) :
    (continuation weight nonnegative decision response players).map auditKey =
      ((continuation weight nonnegative decision response players).map
        (fun final => final.application.playerView bob)).map (fun view =>
          (view.publicView, (serviced decision.execution response).receipts,
            (serviced decision.execution response).network.inputs.filter
              (fun message => message.sender = bob))) := by
  rw [PMF.map_comp]
  apply map_congr_on_support _
  intro final reached
  have suffix := reached
  change final ∈ ((app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
    (decision.execution.respond app bob response)).bind
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 5)).support
    at suffix
  rw [serviced_round weight nonnegative 6 decision.execution decision.trace response players,
    PMF.pure_bind] at suffix
  have receipts := tail_preserves_receipts weight nonnegative players 5 _ final
    (by rw [serviced_cursor weight nonnegative decision.execution decision.trace response]) suffix
  have inputs := final_preserves_inputs weight nonnegative players 5 _ final
    (by
      rw [serviced_cursor weight nonnegative decision.execution decision.trace response]
      omega) suffix
  unfold auditKey
  rw [receipts, inputs]
  rfl

theorem continuation_auditKey_same_information (first second : DecisionHistory weight nonnegative)
    (sameRecall : first.execution.recall bob = second.execution.recall bob)
    (sameView : first.execution.observe app bob = second.execution.observe app bob)
    (response : app.Action) (firstPlayers secondPlayers : Player → app.Policy) :
    (continuation weight nonnegative first response firstPlayers).map auditKey =
      (continuation weight nonnegative second response secondPlayers).map auditKey := by
  rw [continuation_auditKey_law weight nonnegative first response firstPlayers,
    continuation_auditKey_law weight nonnegative second response secondPlayers,
    serviced_receipts_same_information weight nonnegative first second sameRecall sameView response,
    serviced_inputs_same_information weight nonnegative first second sameRecall sameView response]
  unfold continuation
  rw [continuation_owner_same_information weight nonnegative
    first.execution second.execution first.trace second.trace sameRecall sameView response
    firstPlayers secondPlayers]

theorem continuation_charge_same_information (first second : DecisionHistory weight nonnegative)
    (sameRecall : first.execution.recall bob = second.execution.recall bob)
    (sameView : first.execution.observe app bob = second.execution.observe app bob)
    (response : app.Action) (firstPlayers secondPlayers : Player → app.Policy) :
    (continuation weight nonnegative first response firstPlayers).map fullCharge =
      (continuation weight nonnegative second response secondPlayers).map fullCharge := by
  have left : (continuation weight nonnegative first response firstPlayers).map fullCharge =
      ((continuation weight nonnegative first response firstPlayers).map auditKey).map
        keyCharge := by
    rw [PMF.map_comp]
    apply map_congr_on_support _
    intro final reached
    obtain ⟨trace⟩ := continuation_trace weight nonnegative first response firstPlayers final
      reached
    exact fullCharge_eq_keyCharge weight nonnegative ⟨0, none, final⟩ trace
  have right : (continuation weight nonnegative second response secondPlayers).map fullCharge =
      ((continuation weight nonnegative second response secondPlayers).map auditKey).map
        keyCharge :=
    by
      rw [PMF.map_comp]
      apply map_congr_on_support _
      intro final reached
      obtain ⟨trace⟩ := continuation_trace weight nonnegative second response secondPlayers final
        reached
      exact fullCharge_eq_keyCharge weight nonnegative ⟨0, none, final⟩ trace
  rw [left, right, continuation_auditKey_same_information weight nonnegative first second sameRecall
    sameView response firstPlayers secondPlayers]

end Vegas.Examples.LateOpeningRuntimeBobFinalAuditObservation
