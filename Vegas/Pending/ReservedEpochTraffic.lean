/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochCapacity
import Interaction.ReactiveTrafficState
import Interaction.ReactiveRawRoundTrace

/-! # All-raw submission bounds from exogenous owner slots -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
theorem process_actor (view : (app).EnvironmentView) :
    (process runtime leaks view).actor? app = none := by
  unfold process
  cases view.network.pending.head? <;> rfl

omit [Fintype Player] in
theorem sample_actor (view : (app).EnvironmentView) :
    (sample runtime leaks view).actor? app = none := by
  unfold sample
  split
  · split <;> rfl
  · rfl

theorem command_no_actor_outside {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (cursor : Nat) (view : (app).EnvironmentView)
    (outside : ¬ ownerSlot (graph := graph) packetBudget cursor) :
    (command runtime leaks packetBudget tape cursor view).actor? app = none := by
  unfold command
  dsimp
  split
  · split
    · exact process_actor runtime leaks view
    · rfl
  · rename_i notProcessing
    split
    · rename_i inOwners
      exfalso
      apply outside
      exact ⟨by omega, by omega⟩
    · split
      · exact sample_actor runtime leaks view
      · split <;> rfl

theorem command_activation_capacity {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (cursor : Nat) (view : (app).EnvironmentView) :
    activationCapacity (graph := graph) packetBudget cursor +
        (if (command runtime leaks packetBudget tape cursor view).actor? app |>.isSome
          then 1 else 0) ≤
      activationCapacity (graph := graph) packetBudget (cursor + 1) := by
  rw [activationCapacity_step]
  by_cases owned : ownerSlot (graph := graph) packetBudget cursor
  · simp only [owned, ↓reduceIte]
    split <;> omega
  · rw [command_no_actor_outside runtime leaks packetBudget tape cursor view owned]
    simp [owned]

/-- The active response reserves its possible packet before it occurs. -/
def TrafficCapacity (packetBudget : Nat) (control : (app).Control) : Prop :=
  control.execution.network.inputs.length + (if control.actor.isSome then 1 else 0) ≤
    activationCapacity (graph := graph) packetBudget control.execution.environmentRecall.length

omit [Fintype Player] in
theorem respond_input_length (execution : (app).Execution) (owner : Player)
    (response : (app).Action) :
    (execution.respond app owner response).network.inputs.length ≤
      execution.network.inputs.length + 1 := by
  rcases response with ⟨transmission⟩
  cases transmission <;>
    simp [ReactiveApplication.Execution.respond, MessageNetwork.submit]

theorem traffic_capacity_history {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (initial : PMF (app).State) (horizon : Nat)
    (control : (app).Control)
    (trace : ((app).protocol initial horizon (family runtime leaks packetBudget tape)).Trace
      (some control)) : TrafficCapacity runtime leaks packetBudget control := by
  have bounded : ∀ {state}
      (_trace : ((app).protocol initial horizon
        (family runtime leaks packetBudget tape)).Trace state),
      state.elim True (TrafficCapacity runtime leaks packetBudget) := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint legal reached ih =>
        change target ∈ ((app).transition initial horizon
          (family runtime leaks packetBudget tape) source joint).support at reached
        cases source with
        | none =>
            obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
            simp [TrafficCapacity, ReactiveApplication.Execution.initial, activationCapacity,
              MessageNetwork.empty]
        | some current =>
            rcases current with ⟨remaining, actor, execution⟩
            cases actor with
            | some who =>
                cases (PMF.mem_support_pure_iff _ _).mp reached
                change execution.network.inputs.length + 1 ≤ _ at ih
                change (execution.respond app who _).network.inputs.length + 0 ≤ _
                rw [(app).respond_environmentRecall]
                exact (Nat.add_zero _).trans_le
                  ((respond_input_length runtime leaks execution who _).trans ih)
            | none =>
                cases remaining with
                | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
                | succ remaining =>
                    obtain ⟨selected, supported, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, observed, rfl⟩ := PMF.support_map .. ▸ moved
                    have selectedEq := (family_support runtime leaks packetBudget tape
                      execution.environmentRecall (execution.observeEnvironment app) selected).mp
                        supported
                    have inputsEq := (app).environmentStep_inputs execution next selected observed
                    have recallEq : next.environmentRecall = execution.environmentRecall ++
                        [⟨execution.observeEnvironment app, selected⟩] := by
                      unfold ReactiveApplication.Execution.environmentStep at observed
                      obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ observed
                      rfl
                    change execution.network.inputs.length + 0 ≤ _ at ih
                    change next.network.inputs.length +
                      (if (selected.actor? app).isSome then 1 else 0) ≤ _
                    rw [inputsEq, recallEq, List.length_append, List.length_singleton, selectedEq]
                    exact (Nat.add_le_add_right (by simpa using ih) _).trans
                      (command_activation_capacity runtime leaks packetBudget tape
                        execution.environmentRecall.length (execution.observeEnvironment app))
  exact bounded trace

theorem inputs_le_cycles {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (initial : PMF (app).State) (cycles : Nat) (control : (app).Control)
    (trace : ((app).protocol initial
      (cycles * cycleWidth (graph := graph) packetBudget)
      (family runtime leaks packetBudget tape)).Trace (some control)) :
    control.execution.network.inputs.length ≤ cycles * Fintype.card Player := by
  have budget := traffic_capacity_history runtime leaks packetBudget tape initial _ control trace
  have clock := (app).raw_trace_horizon initial _ (family runtime leaks packetBudget tape) trace
  have cursorBound : control.execution.environmentRecall.length ≤
      cycles * cycleWidth (graph := graph) packetBudget := by omega
  have capacity := activationCapacity_mono (graph := graph) packetBudget cursorBound
  rw [activationCapacity_cycles] at capacity
  exact (Nat.le_add_right _ _).trans (budget.trans capacity)

end Vegas.EventGraphRuntime.ReservedEpoch
