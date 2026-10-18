/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochTraffic
import Interaction.ReactivePublication

/-! # Raw pending traffic fits the independently derived submission reserve -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem include_pending_length_le (execution : (app).Execution) (identifier : MessageId Player) :
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

theorem pending_bound_invariant (scheduler : (app).Scheduler) :
    (app).ServiceInvariant scheduler (fun execution =>
      execution.network.pending.length ≤ execution.network.inputs.length) where
  respond execution owner response before := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact before
    | some material =>
        change (execution.network.pending ++ [_]).length ≤
          (execution.network.inputs ++ [_]).length
        simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right before 1
  environment execution next selected before _ reached := by
    have inputsEq := (app).environmentStep_inputs execution next selected reached
    rw [inputsEq]
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
    | application command =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at reached
        obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
        exact le_rfl
    | «include» identifier =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact include_pending_length_le runtime leaks execution identifier

theorem pending_le_inputs_history (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some control)) :
    control.execution.network.pending.length ≤ control.execution.network.inputs.length :=
  (pending_bound_invariant runtime leaks scheduler).history initial horizon
    (fun _ _ => le_rfl) trace

theorem pending_le_cycles [Fintype Player] {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (initial : PMF (app).State) (cycles : Nat)
    (control : (app).Control)
    (trace : ((app).protocol initial
      (cycles * cycleWidth (graph := graph) packetBudget)
      (family runtime leaks packetBudget tape)).Trace (some control)) :
    control.execution.network.pending.length ≤ cycles * Fintype.card Player :=
  (pending_le_inputs_history runtime leaks initial _ _ control trace).trans
    (inputs_le_cycles runtime leaks packetBudget tape initial cycles control trace)

end Vegas.EventGraphRuntime.ReservedEpoch
