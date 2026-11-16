module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.PeriodicService
public import Interaction.ReactiveTrafficState
public import Interaction.ReactivePublication
public import Interaction.ReactiveResponseAccounting

@[expose] public section

/-! # Raw traffic capacity of the periodic physical service -/

noncomputable section

namespace Vegas.EventGraphRuntime.PeriodicService

open EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable {graph : EventGraph Player L} {roster : Bool ≃ Player}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {inputLaw : PMF graph.Inputs}

local notation "app" => (reactiveApplication (timeouts graph)) leaks
local notation "deadlines" => timeouts graph
local notation "startLaw" => initial graph leaks inputLaw
local notation "schedule" => scheduler graph roster leaks
local notation "selectedCommand" => command graph roster leaks

def activationCapacity (cursor : Nat) : Nat :=
  2 * (cursor / width) + min (cursor % width - packetBudget) 2

theorem activationCapacity_step (cursor : Nat) :
    activationCapacity (cursor + 1) = activationCapacity cursor +
      if packetBudget ≤ cursor % width ∧ cursor % width < packetBudget + 2 then 1 else 0 := by
  dsimp only [activationCapacity, width, packetBudget, cycles]
  split_ifs <;> omega

theorem activationCapacity_mono : Monotone activationCapacity := by
  apply monotone_nat_of_le_succ
  intro cursor
  rw [activationCapacity_step]
  omega

private theorem pending_head_no_actor (view : (app).EnvironmentView) :
    ((app).pendingHeadCommand view).actor? app = none := by
  unfold ReactiveApplication.pendingHeadCommand
  split <;> rfl

theorem command_no_actor_outside (cursor : Nat) (view : (app).EnvironmentView)
    (outside : ¬ (packetBudget ≤ cursor % width ∧ cursor % width < packetBudget + 2)) :
    (selectedCommand cursor view).actor? app = none := by
  dsimp only [command]
  split_ifs
  all_goals try exact pending_head_no_actor view
  all_goals try rfl
  all_goals exfalso; apply outside; constructor <;> omega

theorem command_activation_capacity (cursor : Nat) (view : (app).EnvironmentView) :
    activationCapacity cursor + (if (selectedCommand cursor view).actor? app |>.isSome then 1
      else 0) ≤
      activationCapacity (cursor + 1) := by
  rw [activationCapacity_step]
  by_cases owned : packetBudget ≤ cursor % width ∧ cursor % width < packetBudget + 2
  · simp only [owned]
    have one : (if (selectedCommand cursor view).actor? app |>.isSome then 1 else 0) ≤ 1 := by
      split_ifs <;> omega
    exact Nat.add_le_add_left one _
  · rw [command_no_actor_outside cursor view owned]
    simp [owned]

def TrafficCapacity (control : (app).Control) : Prop :=
  control.execution.network.inputs.length + (if control.actor.isSome then 1 else 0) ≤
    activationCapacity control.execution.environmentRecall.length

private theorem respond_input_length (execution : (app).Execution) (owner : Player)
    (response : (app).Action) :
    (execution.respond app owner response).network.inputs.length ≤
      execution.network.inputs.length + 1 := by
  rcases response with ⟨transmission⟩
  cases transmission <;> simp [ReactiveApplication.Execution.respond, MessageNetwork.submit]

theorem traffic_capacity_history (control : (app).Control)
    (trace : ((app).protocol startLaw horizon schedule).Trace (some control)) :
    TrafficCapacity control := by
  have bounded : ∀ {state} (_trace : ((app).protocol startLaw horizon schedule).Trace state),
      state.elim True TrafficCapacity := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint legal reached ih =>
        change target ∈
          ((app).transition startLaw horizon schedule source joint).support at reached
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
                exact (Nat.add_zero _).trans_le ((respond_input_length execution who _).trans ih)
            | none =>
                cases remaining with
                | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
                | succ remaining =>
                    obtain ⟨selected, supported, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, observed, rfl⟩ := PMF.support_map .. ▸ moved
                    have selectedEq : selected = selectedCommand execution.environmentRecall.length
                        (execution.observeEnvironment app) :=
                      (PMF.mem_support_pure_iff _ _).mp supported
                    have inputsEq := (app).environmentStep_inputs execution next selected observed
                    have recallEq := (app).environmentStep_environmentRecall execution next
                      selected
                      observed
                    change execution.network.inputs.length + 0 ≤ _ at ih
                    change next.network.inputs.length +
                      (if (selected.actor? app).isSome then 1 else 0) ≤ _
                    rw [inputsEq, recallEq, List.length_append, List.length_singleton, selectedEq]
                    exact (Nat.add_le_add_right (by simpa using ih) _).trans
                      (command_activation_capacity execution.environmentRecall.length
                        (execution.observeEnvironment app))
  exact bounded trace

theorem inputs_le_budget (control : (app).Control)
    (trace : ((app).protocol startLaw horizon schedule).Trace (some control)) :
    control.execution.network.inputs.length ≤ packetBudget := by
  have budget := traffic_capacity_history control trace
  have accounted := (app).raw_trace_horizon startLaw horizon schedule trace
  have cursorBound : control.execution.environmentRecall.length ≤ horizon := by omega
  have capacity := activationCapacity_mono cursorBound
  have total : activationCapacity horizon = packetBudget := by decide
  rw [total] at capacity
  exact (Nat.le_add_right _ _).trans (budget.trans capacity)

private theorem include_pending_length_le (execution : (app).Execution)
    (identifier : MessageId Player) :
    (execution.includePending app identifier).network.pending.length ≤
      execution.network.pending.length := by
  rw [(app).includePending_network]
  unfold MessageNetwork.includePending
  split
  · exact le_rfl
  · rename_i message found
    have removed := MessagePool.removeFirst_length_of_find identifier execution.network.pending
      message found
    dsimp
    omega

theorem pending_bound_invariant : (app).ServiceInvariant schedule (fun execution =>
    execution.network.pending.length ≤ execution.network.inputs.length) where
  respond execution owner response before := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact before
    | some material =>
        change (execution.network.pending ++ [_]).length ≤ (execution.network.inputs ++ [_]).length
        simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right before 1
  environment execution next selected before _ reached := by
    rw [(app).environmentStep_inputs execution next selected reached]
    apply LE.le.trans (c := execution.network.inputs.length) _ before
    cases selected with
    | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact le_rfl
    | activate owner =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at reached
        obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ reached
        exact le_rfl
    | application native =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at reached
        obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
        exact le_rfl
    | «include» identifier =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact include_pending_length_le execution identifier

theorem pending_le_budget (control : (app).Control)
    (trace : ((app).protocol startLaw horizon schedule).Trace (some control)) :
    control.execution.network.pending.length ≤ packetBudget :=
  (pending_bound_invariant.history startLaw horizon (fun _ _ => le_rfl) trace).trans
    (inputs_le_budget control trace)



end Vegas.EventGraphRuntime.PeriodicService
