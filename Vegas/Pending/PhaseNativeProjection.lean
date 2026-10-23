/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetworkMap
import Vegas.Pending.PhasePacketAddress

/-! # Physical phase traffic projected to the original native application -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

/-- Reconstruct the static no-reset tag before applying the original observation rule. -/
def nativeLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
  fun who pending => leaks who (pending.map (Message.mapPayload plan.stampPacket))

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- Native and phased strategies transmit the same authenticated submission material. -/
def action (response : (P).Action) : (N).Action := ⟨response.transmission⟩

def playerView (view : (P).PlayerView) : (N).PlayerView :=
  ⟨view.messages.mapPayload CommitAttemptPacket.packet, view.application.1, view.receipts⟩

def playerEntry (entry : (P).PlayerEntry) : (N).PlayerEntry :=
  ⟨playerView runtime leaks plan entry.beforeView, action runtime leaks plan entry.action,
    entry.emitted.map (Message.mapPayload CommitAttemptPacket.packet)⟩

def environmentView (view : (P).EnvironmentView) : (N).EnvironmentView :=
  ⟨view.network.mapPayload CommitAttemptPacket.packet, view.application.native, view.receipts⟩

def command : (P).Command → (N).Command
  | .activate who => .activate who
  | .include id => .include id
  | .application command => .application command
  | .wait => .wait

def environmentEntry (entry : (P).EnvironmentEntry) : (N).EnvironmentEntry :=
  ⟨environmentView runtime leaks plan entry.beforeView, command runtime leaks plan entry.command⟩

/-- Project the actual physical state and every retained interaction record. -/
def execution (current : (P).Execution) : (N).Execution :=
  ⟨current.application.current.native, current.network.mapPayload CommitAttemptPacket.packet,
    current.receipts, fun who => (current.recall who).map (playerEntry runtime leaks plan),
    current.environmentRecall.map (environmentEntry runtime leaks plan)⟩

def control (current : (P).Control) : (N).Control :=
  ⟨current.remaining, current.actor, execution runtime leaks plan current.execution⟩

theorem observe (current : (P).Execution) (who : Player) :
    (execution runtime leaks plan current).observe (N) who =
      playerView runtime leaks plan (current.observe (P) who) := rfl

theorem observeEnvironment (current : (P).Execution) :
    (execution runtime leaks plan current).observeEnvironment (N) =
      environmentView runtime leaks plan (current.observeEnvironment (P)) := rfl

theorem outputs (past : List (P).PlayerEntry) :
    (N).outputs (past.map (playerEntry runtime leaks plan)) =
      ((P).outputs past).map (Message.mapPayload CommitAttemptPacket.packet) := by
  simp only [ReactiveApplication.outputs, List.filterMap_map, playerEntry,
    List.map_filterMap, Function.comp_def]

theorem known (current : (P).Execution) (who : Player) :
    (execution runtime leaks plan current).network.known who =
      (current.network.known who).map (Message.mapPayload CommitAttemptPacket.packet) :=
  MessageNetwork.mapPayload_known _ _ _

end Vegas.EventGraphRuntime.PhaseNativeProjection
