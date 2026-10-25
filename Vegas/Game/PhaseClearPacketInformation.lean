/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhasePacketAddress
import Vegas.Pending.PhaseInputNamespace
import Vegas.Pending.PhaseClearMetadata
import Interaction.ReactiveTrafficIdentity
import Interaction.MessageNetworkMap

/-! # Physical packet tags reconstructed from clear counted histories

Every admitted packet names its original static phase. Before public exclusion
its generation is zero, so erasing and statically restamping every retained
packet recovers its exact authored payload. Observation rules remain arbitrary.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
private theorem eventPhase_of_mem (plan : RuntimePhasePlan graph)
    (phase : RuntimePhase graph) (member : phase ∈ plan.phases)
    (event : graph.EventId) (inside : event ∈ phase.events) :
    plan.eventPhase event = phase.low := by
  classical
  unfold RuntimePhasePlan.eventPhase
  cases found : plan.phases.find? (fun selected => event ∈ selected.events) with
  | none =>
      have absent := List.find?_eq_none.mp found phase member
      exact (absent (by simpa only [decide_eq_true_eq] using inside)).elim
  | some selected =>
      have selectedMember := List.mem_of_find?_eq_some found
      have selectedInside : event ∈ selected.events := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      have same := RuntimePhasePlan.containing_unique plan.phases plan.adjacent event
        selected phase selectedMember member selectedInside inside
      simp only [Option.map_some, Option.getD_some, same]

variable [Fintype Player] (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph) (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks

/-- Every actual input before exclusion has its exact static no-retry tag. -/
theorem clear_input_restamp_history (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (message : Message Player (CommitAttemptPacket graph))
    (present : message ∈ control.execution.network.inputs) :
    plan.stampPacket message.payload.packet = message.payload := by
  let rawTrace := (onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  have namespaces := inputNamespaces_history runtime leaks
    (inputs.map (PhaseRuntimeState.initial plan))
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_ordered plan draw) horizon scheduler rawTrace
  have zero := (phaseClearMetadata_history runtime leaks plan inputs horizon scheduler
    rawTrace clear).1
  have generationBound := (namespaces.bounded message present).1
  change message.payload.attempt.generation ≤ control.execution.application.generation
    at generationBound
  have generation : message.payload.attempt.generation = 0 := by omega
  obtain ⟨phase, member, event, named, inside, address⟩ :=
    packetPhaseOrigins_history runtime leaks plan bounds inputs horizon scheduler trace
      message present
  have tag : message.payload.attempt = ⟨phase.low, 0⟩ := by
    cases existing : message.payload.attempt with
    | mk source retry =>
        have sourceEq : source = phase.low := by simpa only [existing] using address
        have retryEq : retry = 0 := by simpa only [existing] using generation
        exact congrArg₂ CommitAttemptId.mk sourceEq retryEq
  calc
    plan.stampPacket message.payload.packet = ⟨⟨phase.low, 0⟩, message.payload.packet⟩ := by
      simp only [RuntimePhasePlan.stampPacket, named, Option.map_some, Option.getD_some,
        eventPhase_of_mem plan phase member event inside]
    _ = message.payload := by rw [← tag]

/-- The exact tag reconstruction holds for every retained packet, including leaked
and ledger envelopes, rather than only packets visible to one selected observer. -/
theorem clear_network_packets_history (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) :
    control.execution.network.Satisfies (fun message =>
      plan.stampPacket message.payload.packet = message.payload) := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let rawTrace := (onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler trace
  have retained := (app).retained_envelopes_mem_inputs control.execution
    ((app).history_provenance initial horizon scheduler rawTrace)
    ((app).history_inputRecall initial horizon scheduler rawTrace)
  exact retained.mono fun message present =>
    clear_input_restamp_history runtime leaks plan bounds inputs horizon scheduler trace clear
      message present

end Vegas.EventGraphRuntime.PhaseCount
