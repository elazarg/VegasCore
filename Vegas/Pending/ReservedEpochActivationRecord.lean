/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochGeometry
import Vegas.Pending.PhaseRequestOrigin

/-! # Actual owner offers during surviving readiness episodes -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [DecidableEq Player] in
theorem cycle_le_of_offer_before (packetBudget cursor cycle : Nat)
    (position : Fin (Fintype.card Player))
    (earlier : cycle * cycleWidth (graph := graph) packetBudget +
      (packetBudget + position.val) < cursor + 1) :
    cycle ≤ cursor / cycleWidth (graph := graph) packetBudget := by
  apply (Nat.le_div_iff_mul_le (cycleWidth_pos packetBudget)).mpr
  omega

def RecordedOffers {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (execution : (app).Execution) : Prop :=
  ∀ owner coordinate entered cycle (position : Fin (Fintype.card Player)),
    execution.application.SeedRequest owner coordinate →
    execution.application.current.native.activatedAt coordinate.event = some entered →
    entered < cycle → tape.owner cycle position = owner → tape.activates cycle owner = true →
    cycle * cycleWidth (graph := graph) packetBudget + (packetBudget + position.val) <
      execution.environmentRecall.length →
    ∃ entry ∈ execution.environmentRecall, entry.command = .activate owner ∧
      PhaseRuntimeState.requests entry.beforeView.application owner coordinate ∧
      entry.beforeView.application.native.EventReady coordinate.event ∧
      entry.beforeView.application.native.activatedAt coordinate.event = some entered ∧
      entry.beforeView.application.native.clock = cycle

structure ActivationState {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (inputs : graph.Inputs) (execution : (app).Execution) : Prop where
  geometry : ProgressGeometry inputs execution.application
  clock : ClockAligned runtime leaks packetBudget inputs 0 execution
  recorded : RecordedOffers runtime leaks packetBudget tape execution

theorem activation_state_invariant {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (ordered : graph.RevealRelaxedOrdered) (inputs : graph.Inputs) :
    (app).ServiceInvariant (family runtime leaks packetBudget tape)
      (ActivationState runtime leaks packetBudget tape inputs) where
  respond execution actor action state := by
    refine ⟨(progress_geometry_invariant runtime leaks ordered inputs).respond
      execution actor action state.geometry,
      (clock_aligned_invariant runtime leaks packetBudget tape inputs 0).respond
        execution actor action state.clock, ?_⟩
    intro owner coordinate entered cycle position request activated older atOwner offered earlier
    rw [(app).respond_environmentRecall] at earlier ⊢
    have beforeCycle : cycle ≤ execution.application.current.native.clock := by
      rw [state.clock.2, Nat.zero_add]
      exact cycle_le_of_offer_before packetBudget execution.environmentRecall.length cycle position
        (by omega)
    rcases PhaseSeedScheduler.respond_request_origin runtime leaks execution actor action ordered
      state.geometry.valid.1 state.geometry.frontier state.geometry.live state.geometry.maximal
        state.geometry.quiescent owner coordinate entered request activated with
      ⟨priorRequest, priorStamp⟩ | fresh
    · exact state.recorded owner coordinate entered cycle position priorRequest priorStamp older
        atOwner offered earlier
    · omega
  environment execution next selected state supported reached := by
    refine ⟨(progress_geometry_invariant runtime leaks ordered inputs).environmentStep
      execution next selected state.geometry reached,
      (clock_aligned_invariant runtime leaks packetBudget tape inputs 0).environment
        execution next selected state.clock supported reached, ?_⟩
    intro owner coordinate entered cycle position request activated older atOwner offered earlier
    have recallEq := (app).environmentStep_environmentRecall execution next selected reached
    have lengthEq : next.environmentRecall.length = execution.environmentRecall.length + 1 := by
      rw [recallEq, List.length_append, List.length_singleton]
    have beforeCycle : cycle ≤ execution.application.current.native.clock := by
      rw [state.clock.2, Nat.zero_add]
      apply cycle_le_of_offer_before packetBudget execution.environmentRecall.length cycle position
      omega
    have origin := PhaseSeedScheduler.environmentStep_request_origin runtime leaks execution next
      selected ordered state.geometry.valid.1 state.geometry.frontier state.geometry.live
        state.geometry.maximal state.geometry.quiescent reached owner coordinate entered
          request activated
    have prior : execution.application.SeedRequest owner coordinate ∧
        execution.application.current.native.activatedAt coordinate.event = some entered := by
      rcases origin with inherited | fresh
      · exact inherited
      · omega
    by_cases old : cycle * cycleWidth (graph := graph) packetBudget +
        (packetBudget + position.val) < execution.environmentRecall.length
    · obtain ⟨entry, member, command, requestView, ready, stamp, clock⟩ := state.recorded owner
        coordinate entered cycle position prior.1 prior.2 older atOwner offered old
      refine ⟨entry, ?_, command, requestView, ready, stamp, clock⟩
      rw [recallEq]
      exact List.mem_append_left _ member
    · have current : execution.environmentRecall.length =
          cycle * cycleWidth (graph := graph) packetBudget + (packetBudget + position.val) := by
        omega
      have commandEq := (family_support runtime leaks packetBudget tape execution.environmentRecall
        (execution.observeEnvironment app) selected).mp supported
      rw [current] at commandEq
      have activatedOwner := activation_at runtime leaks packetBudget tape cycle position
        (execution.observeEnvironment app) (by simpa only [atOwner] using offered)
      rw [atOwner] at activatedOwner
      have actual : selected = .activate owner := commandEq.trans activatedOwner
      refine ⟨⟨execution.observeEnvironment app, selected⟩, ?_, actual, ?_, ?_, ?_, ?_⟩
      · rw [recallEq]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact (execution.application.requests_publicView state.geometry.valid.1 owner
          coordinate).mpr prior.1
      · exact (execution.application.current.native.publicView_eventReady coordinate.event).mpr
          prior.1.2.2.1
      · exact prior.2
      · change execution.application.current.native.clock = cycle
        rw [state.clock.2, current, Nat.zero_add]
        apply cursor_div packetBudget cycle (packetBudget + position.val)
        unfold cycleWidth
        omega

end Vegas.EventGraphRuntime.ReservedEpoch
