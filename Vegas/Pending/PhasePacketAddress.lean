/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseClearHistory
import Vegas.Pending.PhasePlanSuffix
import Vegas.Pending.PhaseCountMenu
import Vegas.Pending.PhaseInputNamespace
import Vegas.Pending.PhaseOwnCommitments
import Interaction.ReactiveTrafficIdentity

/-! # Static packet addresses on clear counted phase histories -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RuntimePhasePlan

omit [DecidableEq Player] in
private theorem low_le_of_mem (phases : List (RuntimePhase graph))
    (ordered : phases.IsChain fun before after => before.high = after.low)
    (first : RuntimePhase graph) (head : phases.head? = some first)
    (other : RuntimePhase graph) (member : other ∈ phases) : first.low ≤ other.low := by
  induction phases generalizing first other with
  | nil => cases head
  | cons phase rest ih =>
      have same : phase = first := Option.some.inj head
      subst phase
      rcases List.mem_cons.mp member with same | later
      · subst other; exact le_rfl
      · cases rest with
        | nil => cases later
        | cons next tail =>
            have adjacent := (List.isChain_cons_cons.mp ordered).1
            exact first.nonempty.le.trans (adjacent.le.trans
              (ih ordered.tail next rfl other later))

omit [DecidableEq Player] in
theorem high_le_of_mem_tail (first : RuntimePhase graph) (rest : List (RuntimePhase graph))
    (ordered : (first :: rest).IsChain fun before after => before.high = after.low)
    (other : RuntimePhase graph) (member : other ∈ rest) : first.high ≤ other.low := by
  cases rest with
  | nil => cases member
  | cons next tail =>
      exact (List.isChain_cons_cons.mp ordered).1.le.trans
        (low_le_of_mem (next :: tail) ordered.tail next rfl other member)

omit [DecidableEq Player] in
theorem containing_unique (phases : List (RuntimePhase graph))
    (ordered : phases.IsChain fun before after => before.high = after.low)
    (event : graph.EventId) (first second : RuntimePhase graph)
    (firstMember : first ∈ phases) (secondMember : second ∈ phases)
    (firstContains : event ∈ first.events) (secondContains : event ∈ second.events) :
    first = second := by
  induction phases generalizing first second with
  | nil => cases firstMember
  | cons phase rest ih =>
      rcases List.mem_cons.mp firstMember with firstEq | firstLater
      · subst first
        rcases List.mem_cons.mp secondMember with secondEq | secondLater
        · exact secondEq.symm
        · have separated := high_le_of_mem_tail phase rest ordered second secondLater
          have left := (phase.mem_events event).mp firstContains
          have right := (second.mem_events event).mp secondContains
          omega
      · rcases List.mem_cons.mp secondMember with secondEq | secondLater
        · subst second
          have separated := high_le_of_mem_tail phase rest ordered first firstLater
          have left := (first.mem_events event).mp firstContains
          have right := (phase.mem_events event).mp secondContains
          omega
        · exact ih ordered.tail first second firstLater secondLater firstContains secondContains

/-- The static source phase containing an event, independent of physical time. -/
def eventPhase (plan : RuntimePhasePlan graph) (event : graph.EventId) : Nat :=
  ((plan.phases.find? fun phase => event ∈ phase.events).map RuntimePhase.low).getD
    graph.order.eventCount

omit [DecidableEq Player] in
theorem eventPhase_of_mem (plan : RuntimePhasePlan graph) (phase : RuntimePhase graph)
    (member : phase ∈ plan.phases) (event : graph.EventId) (inside : event ∈ phase.events) :
    plan.eventPhase event = phase.low := by
  classical
  cases found : plan.phases.find? (fun current => event ∈ current.events) with
  | none =>
      have absent := (List.find?_eq_none.mp found) phase member
      exact (absent (decide_eq_true inside)).elim
  | some selected =>
      have selectedMember := List.mem_of_find?_eq_some found
      have selectedInside : event ∈ selected.events :=
        of_decide_eq_true (List.find?_some
          (p := fun current : RuntimePhase graph => decide (event ∈ current.events)) found)
      have same := containing_unique plan.phases plan.adjacent event selected phase
        selectedMember member selectedInside inside
      simp only [eventPhase, found, Option.map_some, Option.getD_some, same]

/-- Retag a native packet with its unique no-reset physical source address. -/
def stampPacket (plan : RuntimePhasePlan graph) (packet : WitnessedPacket graph) :
    CommitAttemptPacket graph :=
  ⟨⟨((packet.call.event? graph).map plan.eventPhase).getD graph.order.eventCount, 0⟩, packet⟩

end RuntimePhasePlan

namespace PhaseCount

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "app" => phaseApplication runtime leaks

/-- Each authored call identifies its static phase, even after that phase retires. -/
def PacketPhaseOrigins (execution : (app).Execution) : Prop :=
  ∀ message ∈ execution.network.inputs, ∃ phase ∈ plan.phases, ∃ event,
    message.payload.packet.call.event? graph = some event ∧ event ∈ phase.events ∧
      message.payload.attempt.phase = phase.low

private theorem emitted_phase (state : PhaseRuntimeState graph) (who : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (material : WitnessedSubmission graph)
    (authorized : ((state.submit who material).emit who known material).packet.tokenValid = true) :
    ∃ phase ∈ state.phases.head?, ∃ event,
      material.call.packet.event? graph = some event ∧ event ∈ phase.events ∧
        state.attempt.phase = phase.low := by
  rw [emit_after_submit] at authorized
  unfold maskPacket at authorized
  cases head : state.phases.head? with
  | none =>
      simp only [allows, PhaseRuntimeState.publicView, head, Option.map_none] at authorized
      simp only [Bool.false_eq_true, ↓reduceIte, WitnessedPacket.tokenValid_none] at authorized
  | some phase =>
      cases named : material.call.packet.event? graph with
      | none =>
          simp only [allows, PhaseRuntimeState.publicView, head, Option.map_some, named]
            at authorized
          simp only [Bool.false_eq_true, ↓reduceIte, WitnessedPacket.tokenValid_none] at authorized
      | some event =>
          have allowed : event ∈ phase.events := by
            by_contra missing
            have outside : ¬ (phase.low ≤ event.val ∧ event.val < phase.high) :=
              fun inside => missing ((phase.mem_events event).mpr inside)
            simp only [allows, PhaseRuntimeState.publicView, head, Option.map_some, named,
              outside, decide_false, Bool.false_eq_true, ↓reduceIte,
              WitnessedPacket.tokenValid_none] at authorized
          exact ⟨phase, by simp, event, rfl, allowed, by
            simp only [PhaseRuntimeState.attempt, head, Option.map_some, Option.getD_some]⟩

private theorem origins_respond [Fintype Player] (bounds : MessageBounds graph)
    (execution : (app).Execution) (suffix : execution.application.phases <:+ plan.phases)
    (origins : PacketPhaseOrigins runtime leaks plan execution)
    (clean : CountClean runtime leaks execution) (who : Player) (action : (app).Action)
    (allowed : action ∈ onePacketActions runtime leaks bounds who (execution.recall who)
      (execution.observe app who)) :
    PacketPhaseOrigins runtime leaks plan (execution.respond app who action) := by
  have nextClean := countClean_respond runtime leaks execution clean who action
    ((mem_onePacketActions runtime leaks bounds who _ _ action).mp allowed).2
  cases action with
  | mk transmission =>
      cases transmission with
      | none => exact origins
      | some material =>
          let message : Message Player (CommitAttemptPacket graph) :=
            ⟨(who, execution.network.nextSerial who),
              (execution.application.submit who material).emit who
                (execution.network.known who) material⟩
          have inputs : (execution.respond app who ⟨some material⟩).network.inputs =
              List.append (α := Message Player (CommitAttemptPacket graph))
                execution.network.inputs [message] := rfl
          intro envelope present
          rw [inputs] at present
          rcases List.mem_append.mp present with prior | fresh
          · exact origins envelope prior
          · have same : envelope = message := List.mem_singleton.mp fresh
            subst envelope
            have admitted := (permits_eq_true_iff _ _).mp
              (nextClean.2 message (by rw [inputs]; exact List.mem_append_right _ (by simp)))
            obtain ⟨phase, head, event, named, inside, addressEq⟩ :=
              emitted_phase execution.application who (execution.network.known who)
                material admitted.1
            refine ⟨phase, suffix.subset (List.mem_of_mem_head? head), event, ?_, inside,
              addressEq⟩
            exact (congrArg (Payload.event? graph)
              (phase_emit_call (execution.application.submit who material) who
                (execution.network.known who) material)).trans named

/-- Genuine counted traffic fixes every authored static phase address. -/
theorem packetPhaseOrigins_history [Fintype Player] (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    PacketPhaseOrigins runtime leaks plan control.execution := by
  let invariant : (onePacketMenu runtime leaks bounds).ServiceInvariant scheduler
      (fun execution => execution.application.phases <:+ plan.phases ∧
        CountClean runtime leaks execution ∧ PacketPhaseOrigins runtime leaks plan execution) :=
    ⟨fun execution who action valid allowed =>
      ⟨(phaseApplication_planSuffix runtime leaks plan).respond execution who action valid.1,
        countClean_respond runtime leaks execution valid.2.1 who action
        ((mem_onePacketActions runtime leaks bounds who _ _ action).mp allowed).2,
        origins_respond runtime leaks plan bounds execution valid.1 valid.2.2 valid.2.1 who
          action allowed⟩,
      fun execution next command valid _chosen reached =>
        ⟨(phaseApplication_planSuffix runtime leaks plan).environmentStep execution next command
          valid.1 reached,
          countClean_environment runtime leaks execution next command valid.2.1 reached, by
            intro message present
            rw [(app).environmentStep_inputs execution next command reached] at present
            exact valid.2.2 message present⟩⟩
  have actual := invariant.history _ horizon (fun state member => by
    obtain ⟨input, _support, rfl⟩ := PMF.support_map .. ▸ member
    exact ⟨PhaseRuntimeState.settle_suffix _ _ _ _ _, countClean_initial runtime leaks _,
      fun _ impossible => (List.not_mem_nil impossible).elim⟩) trace
  exact actual.2.2

/-- On a clear actual counted history, the erased packet reconstructs its exact
original tag; there are no hidden retired generations left to guess. -/
theorem stamp_nativeMessage_of_clear [Fintype Player] (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (message : Message Player (CommitAttemptPacket graph))
    (authentic : message ∈ control.execution.network.inputs) :
    plan.stampPacket message.payload.packet = message.payload := by
  have raw := (onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  have generation := (phase_clear_history runtime leaks plan inputs horizon scheduler control
    raw clear).1
  have namespaces := inputNamespaces_history runtime leaks _
    (fun state supported => by
      obtain ⟨input, _support, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_ordered plan input) horizon scheduler raw
  have bounded := (namespaces.bounded message authentic).1
  change message.payload.attempt.generation ≤ control.execution.application.generation at bounded
  rw [generation] at bounded
  have zero := Nat.eq_zero_of_le_zero bounded
  obtain ⟨phase, member, event, named, inside, same⟩ :=
    packetPhaseOrigins_history runtime leaks plan bounds inputs horizon scheduler trace message
      authentic
  have static := plan.eventPhase_of_mem phase member event inside
  cases message with
  | mk id packet =>
      cases packet with
      | mk attempt packet =>
          cases attempt with
          | mk address retry =>
              change retry = 0 at zero
              change address = phase.low at same
              simp only [RuntimePhasePlan.stampPacket, named, Option.map_some,
                Option.getD_some, static, same, zero]

end PhaseCount
end Vegas.EventGraphRuntime
