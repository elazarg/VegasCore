/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseRecoveryInformation
import Vegas.Game.PhaseClearPacketInformation
import Vegas.Pending.PhaseNativeProjection
import Interaction.MessageNetworkMapLearn

/-! # Actual private pending-message sampling through the recovery projection

Static packet reconstruction restores the original phase leak law before
sampling physical message identities. Learning the sampled identities and
recording the builder's activation then commute with complete execution erasure.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRecoveryProjection

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "P" => phaseApplication runtime leaks
local notation "R" => recoveryApplication runtime recoveryLeaks

/-- Static tags on pending traffic recover the exact original sampling law. -/
theorem pending_observation_projected (current : (P).Execution)
    (packets : ∀ message ∈ current.network.pending,
      plan.stampPacket message.payload.packet = message.payload) (who : Player) :
    recoveryLeaks who ((execution runtime leaks recoveryLeaks current).network.pending) =
      leaks who current.network.pending := by
  unfold PhaseNativeProjection.nativeLeaks execution
  change leaks who (((current.network.pending.map
    (Message.mapPayload CommitAttemptPacket.packet)).map
      (Message.mapPayload plan.stampPacket))) = _
  congr 1
  rw [List.map_map]
  calc
    _ = current.network.pending.map id := List.map_congr_left fun message present => by
      cases message with
      | mk identity packet => exact congrArg (Message.mk identity) (packets _ present)
    _ = current.network.pending := List.map_id _

/-- Activation preserves the exact private sample and full projected builder recall. -/
theorem activate_projected_of_static (current : (P).Execution)
    (packets : ∀ message ∈ current.network.pending,
      plan.stampPacket message.payload.packet = message.payload) (who : Player) :
    (current.environmentStep (P) (.activate who)).map (execution runtime leaks recoveryLeaks) =
      (execution runtime leaks recoveryLeaks current).environmentStep (R) (.activate who) := by
  have sample := pending_observation_projected runtime leaks plan current packets who
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
  change (leaks who current.network.pending).map _ =
    (recoveryLeaks who (execution runtime leaks recoveryLeaks current).network.pending).map _
  rw [sample]
  congr 1
  funext selected
  simp only [Function.comp_apply, execution, MessageNetwork.mapPayload_learn,
    List.map_append, List.map_cons, List.map_nil]
  rfl

variable [Fintype Player] (bounds : MessageBounds graph)

/-- Every actual clear counted prefix supplies the static pending-packet guard. -/
theorem activate_projected_history (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) {control : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) (who : Player) :
    (control.execution.environmentStep (P) (.activate who)).map
        (execution runtime leaks recoveryLeaks) =
      (execution runtime leaks recoveryLeaks control.execution).environmentStep
        (R) (.activate who) :=
  activate_projected_of_static runtime leaks plan control.execution
    (PhaseCount.clear_network_packets_history runtime leaks plan bounds inputs horizon scheduler
      trace clear).pending who

end Vegas.EventGraphRuntime.PhaseRecoveryProjection
