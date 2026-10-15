/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeCursor
import Interaction.ReactiveResponseAccounting

/-! # The same adaptive scheduler on reconstructed native observations -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- The environment command vocabulary is unchanged by phase erasure. -/
def liftCommand : (N).Command → (P).Command
  | .activate who => .activate who
  | .include id => .include id
  | .application command => .application command
  | .wait => .wait

omit [Fintype Player] in
theorem liftCommand_command (chosen : (P).Command) :
    liftCommand runtime leaks plan (command runtime leaks plan chosen) = chosen := by
  cases chosen <;> rfl

def liftEnvironmentEntry (entry : (N).EnvironmentEntry) : (P).EnvironmentEntry :=
  ⟨liftEnvironmentView runtime leaks plan entry.beforeView,
    liftCommand runtime leaks plan entry.command⟩

private def ClearEnvironmentRecall (state : (P).ProtocolState) : Prop :=
  match state with
  | none => True
  | some current => current.execution.application.current.excluded = ∅ →
      ((execution runtime leaks plan current.execution).environmentRecall.map
        (liftEnvironmentEntry runtime leaks plan)) = current.execution.environmentRecall

private theorem clearEnvironmentRecall_history (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) :
    ∀ {state} (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace state),
      ClearEnvironmentRecall runtime leaks plan state
  | _, .start => trivial
  | _, @Trace.extend _ _ source target before joint legal realized => by
      have inherited := clearEnvironmentRecall_history bounds inputs horizon scheduler before
      have reached : target ∈ ((P).transition
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler source joint).support :=
        realized
      cases source with
      | none =>
          obtain ⟨initial, _supported, rfl⟩ := PMF.support_map .. ▸ reached
          intro _clear
          rfl
      | some current =>
          rcases current with ⟨remaining, actor, current⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              intro clear
              have monotone := (phaseApplication_exclusion_monotone runtime leaks).respond current
                who ((joint who).getD ⟨none⟩)
              have previous := inherited (Finset.subset_empty.mp (clear ▸ monotone))
              simpa only [execution, (P).respond_environmentRecall] using previous
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨chosen, _selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro clear
                  have monotone :=
                    (phaseApplication_exclusion_monotone runtime leaks).environmentStep
                      current next chosen supported
                  have previousClear : current.application.current.excluded = ∅ :=
                    Finset.subset_empty.mp (clear ▸ monotone)
                  have previous := inherited previousClear
                  have visible := liftEnvironmentView_of_clear runtime leaks plan bounds inputs
                    horizon scheduler before previousClear
                  have entry : liftEnvironmentEntry runtime leaks plan
                      (environmentEntry runtime leaks plan
                        ⟨current.observeEnvironment P, chosen⟩) =
                        ⟨current.observeEnvironment P, chosen⟩ := by
                    simp only [liftEnvironmentEntry, environmentEntry, visible,
                      liftCommand_command]
                  have appended :=
                    ReactiveApplication.environmentStep_environmentRecall P current next
                      chosen supported
                  change (next.environmentRecall.map (environmentEntry runtime leaks plan)).map
                    (liftEnvironmentEntry runtime leaks plan) = next.environmentRecall
                  rw [appended, List.map_append, List.map_append, List.map_cons, List.map_cons,
                    List.map_nil, List.map_nil, entry]
                  exact congrArg
                    (fun past => past ++ [⟨current.observeEnvironment P, chosen⟩]) previous

/-- Every recorded scheduler input, including packet tags and old phase cursors,
is recovered from the same actual clear native history. -/
theorem environmentRecall_lift_of_clear (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) :
    ((execution runtime leaks plan current.execution).environmentRecall.map
      (liftEnvironmentEntry runtime leaks plan)) = current.execution.environmentRecall :=
  clearEnvironmentRecall_history runtime leaks plan bounds inputs horizon scheduler trace clear

/-- Run the original adaptive scheduler on the uniquely reconstructed full input. -/
def nativeScheduler (scheduler : (P).Scheduler) : (N).Scheduler := fun past view =>
  (scheduler (past.map (liftEnvironmentEntry runtime leaks plan))
    (liftEnvironmentView runtime leaks plan view)).map (command runtime leaks plan)

/-- At actual clear histories the complete command distribution is preserved,
with no restriction on the scheduler's dependence on its retained observations. -/
theorem nativeScheduler_at_clear (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) :
    nativeScheduler runtime leaks plan scheduler
        (execution runtime leaks plan current.execution).environmentRecall
        ((execution runtime leaks plan current.execution).observeEnvironment N) =
      (scheduler current.execution.environmentRecall
        (current.execution.observeEnvironment P)).map (command runtime leaks plan) := by
  unfold nativeScheduler
  rw [environmentRecall_lift_of_clear runtime leaks plan bounds inputs horizon scheduler
    trace clear]
  rw [observeEnvironment, liftEnvironmentView_of_clear runtime leaks plan bounds inputs horizon
    scheduler trace clear]

end Vegas.EventGraphRuntime.PhaseNativeProjection
