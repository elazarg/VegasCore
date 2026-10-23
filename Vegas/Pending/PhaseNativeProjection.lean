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

/-- Count authorization rules out either public token mask at actual emission. -/
theorem maskPacket_eq_of_authorized (view : PhasePublicView graph)
    (packet : WitnessedPacket graph)
    (authorized : (PhaseCount.maskPacket view packet).tokenValid = true) :
    PhaseCount.maskPacket view packet = packet := by
  unfold PhaseCount.maskPacket at authorized ⊢
  cases excluded : PhaseCount.excludedCall view packet.call <;>
    cases allowed : PhaseCount.allows view packet.call <;>
      simp_all only [Bool.false_eq_true, ↓reduceIte, WitnessedPacket.tokenValid_none]

/-- Erasing an authorized actual emission yields exactly the native emission. -/
theorem emit_of_authorized (state : PhaseRuntimeState graph) (who : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (material : WitnessedSubmission graph)
    (authorized : ((state.submit who material).emit who known material).packet.tokenValid = true) :
    ((state.submit who material).emit who known material).packet =
      material.emit ((N).submit state.current.native who material) who
        (known.map (Message.mapPayload CommitAttemptPacket.packet)) := by
  rw [PhaseCount.emit_after_submit] at authorized ⊢
  have unmasked := maskPacket_eq_of_authorized state.publicView _ authorized
  rw [unmasked]
  have candidates : (fun slot => ((N).submit state.current.native who material).candidates.lookup
      (who, slot)) = material.call.candidateAfter who
        (state.current.native.playerView who).candidates :=
    funext fun slot => material.call.candidateAfter_eq who state.current.native slot
  rw [WitnessedSubmission.emit_eq_resolve, candidates, reactiveApplication_submit_publicView]
  rfl

end Vegas.EventGraphRuntime.PhaseNativeProjection
