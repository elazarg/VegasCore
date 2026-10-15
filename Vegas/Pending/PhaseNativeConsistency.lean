/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecovery
import Vegas.Pending.PhaseNativePlayerInput

/-! # Consistent owner recall under physical address erasure -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

omit [Fintype Player] in
/-- Restoring the full recorded input transports every supported past response,
including the response chosen at each earlier recall prefix. -/
theorem nativePolicy_consistent_of_retraction (policy : (P).Policy)
    (past : List (P).PlayerEntry) (consistent : policy.Consistent past)
    (retracted : (past.map (playerEntry runtime leaks plan)).map
      (liftPlayerEntry runtime leaks plan) = past) :
    (nativePolicy runtime leaks plan policy).Consistent
      (past.map (playerEntry runtime leaks plan)) := by
  induction consistent with
  | nil => exact .nil
  | @snoc history entry prior supported ih =>
      simp only [List.map_append, List.map_cons, List.map_nil] at retracted ⊢
      obtain ⟨before, last⟩ := List.append_inj retracted (by simp)
      have entryRestored := List.singleton_inj.mp last
      have viewRestored := congrArg (fun item : (P).PlayerEntry => item.beforeView) entryRestored
      refine .snoc (playerEntry runtime leaks plan entry) (ih before) ?_
      change action runtime leaks plan entry.action ∈
        ((policy ((history.map (playerEntry runtime leaks plan)).map
          (liftPlayerEntry runtime leaks plan))
          (liftPlayerView runtime leaks plan
            (playerView runtime leaks plan entry.beforeView))).map
          (action runtime leaks plan)).support
      change liftPlayerView runtime leaks plan
        (playerView runtime leaks plan entry.beforeView) = entry.beforeView at viewRestored
      rw [before, viewRestored]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨entry.action, supported, rfl⟩

/-- On an actual clear counted history the projected complete recall is
consistent with the policy evaluated on its reconstructed physical input. -/
theorem nativePolicy_consistent_of_clear (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) (who : Player)
    (policy : (P).Policy)
    (consistent : policy.Consistent (current.execution.recall who)) :
    (nativePolicy runtime leaks plan policy).Consistent
      ((execution runtime leaks plan current.execution).recall who) :=
  nativePolicy_consistent_of_retraction runtime leaks plan policy _ consistent
    (playerRecall_lift_of_clear runtime leaks plan bounds inputs horizon scheduler trace clear who)

end Vegas.EventGraphRuntime.PhaseNativeProjection
