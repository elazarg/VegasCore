/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseRecoveryInformation
import Vegas.Pending.PhaseCountProjection

/-! # Exact admitted response transitions through the recovery projection

The complete execution, physical network and own response entry project
exactly. Only phase admission of the current call is required; exclusions,
private preparations, evidence requests and recalls remain arbitrary.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRecoveryProjection

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (recoveryLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "P" => phaseApplication runtime leaks
local notation "R" => runtime.recoveryApplication recoveryLeaks

/-- Phase admission removes the additional token mask after arbitrary preparation. -/
theorem packet_after_submit_projected (state : PhaseRuntimeState graph) (who : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (material : WitnessedSubmission graph) (allowed : state.allows material.call.packet = true) :
    ((state.submit who material).emit who known material).packet =
      (state.current.submit who material).emit who
        (known.map (Message.mapPayload CommitAttemptPacket.packet)) material := by
  let packet := (state.current.submit who material).emit who
    (known.map (Message.mapPayload CommitAttemptPacket.packet)) material
  change (if state.allows packet.call then packet else { packet with token := none }) = packet
  have call : packet.call = material.call.packet := by
    simp only [packet, RecoveryState.emit]
    split_ifs <;> rfl
  rw [call, allowed]
  rfl
/-- Every admitted response projects its complete physical execution and own recall. -/
theorem respond_of_allows (current : (P).Execution) (who : Player) (response : (P).Action)
    (allowed : ∀ material, response.transmission = some material →
      current.application.allows material.call.packet = true) :
    execution runtime leaks recoveryLeaks (current.respond (P) who response) =
      (execution runtime leaks recoveryLeaks current).respond (R) who
        (action runtime leaks recoveryLeaks response) := by
  cases response with
  | mk transmission =>
      cases transmission with
      | none =>
          simp only [ReactiveApplication.Execution.respond, execution, action]
          congr 1
          funext observer
          split <;> simp_all only [List.map_append, List.map_cons, List.map_nil]
          rfl
      | some material =>
          have packet := packet_after_submit_projected
            current.application who (current.network.known who) material (allowed material rfl)
          change ((P).packet ((P).submit current.application who material) who
              (current.network.known who) material).packet =
            (R).packet ((R).submit current.application.current who material) who
              ((current.network.known who).map (Message.mapPayload CommitAttemptPacket.packet))
                material at packet
          simp only [ReactiveApplication.Execution.respond, execution, action]
          rw [MessageNetwork.mapPayload_known]
          simp only [MessageNetwork.submit, MessageNetwork.mapPayload, List.map_append,
            List.map_cons, List.map_nil, Message.mapPayload]
          rw [packet]
          congr 1
          funext observer
          split <;> simp_all only [List.map_append, List.map_cons, List.map_nil]
          simp only [playerEntry, Option.map_some, Message.mapPayload, packet]
          rfl

end Vegas.EventGraphRuntime.PhaseRecoveryProjection
