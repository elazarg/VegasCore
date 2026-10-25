/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseApplication
import Vegas.Pending.ExclusionApplication
import Interaction.MessageNetworkMap
import Interaction.ReactiveResponseNormalization
import Interaction.ReactiveSubmissionSerial

/-! # Player-local information projected from phase execution to exclusion recovery

The projection forgets attempt addresses and retired snapshots while retaining
actual packet identities, permanent exclusions, receipts and each player's own
recall. It is defined directly on player information; no builder history is used.
It supplies no inverse information map or equilibrium assertion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRecoveryProjection

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (recoveryLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "P" => phaseApplication runtime leaks
local notation "R" => runtime.recoveryApplication recoveryLeaks

/-- Forget phase metadata without changing authenticated submission material. -/
def action (response : (P).Action) : (R).Action := ⟨response.transmission⟩

def playerView (view : (P).PlayerView) : (R).PlayerView :=
  ⟨view.messages.mapPayload CommitAttemptPacket.packet,
    (view.application.1, view.application.2.excluded), view.receipts⟩

def playerEntry (entry : (P).PlayerEntry) : (R).PlayerEntry :=
  ⟨playerView runtime leaks recoveryLeaks entry.beforeView, action runtime leaks recoveryLeaks
    entry.action,
    entry.emitted.map (Message.mapPayload CommitAttemptPacket.packet)⟩

def environmentView (view : (P).EnvironmentView) : (R).EnvironmentView :=
  ⟨view.network.mapPayload CommitAttemptPacket.packet,
    (view.application.native, view.application.excluded), view.receipts⟩

def command : (P).Command → (R).Command
  | .activate who => .activate who
  | .include id => .include id
  | .application command => .application command
  | .wait => .wait

def environmentEntry (entry : (P).EnvironmentEntry) : (R).EnvironmentEntry :=
  ⟨environmentView runtime leaks recoveryLeaks entry.beforeView, command runtime leaks
    recoveryLeaks entry.command⟩

/-- Project the actual physical state and every retained interaction record. -/
def execution (current : (P).Execution) : (R).Execution :=
  ⟨current.application.current, current.network.mapPayload CommitAttemptPacket.packet,
    current.receipts, fun who => (current.recall who).map (playerEntry runtime leaks recoveryLeaks),
    current.environmentRecall.map (environmentEntry runtime leaks recoveryLeaks)⟩

def control (current : (P).Control) : (R).Control :=
  ⟨current.remaining, current.actor, execution runtime leaks recoveryLeaks current.execution⟩

theorem observe (current : (P).Execution) (who : Player) :
    (execution runtime leaks recoveryLeaks current).observe (R) who =
      playerView runtime leaks recoveryLeaks (current.observe (P) who) := rfl

theorem observeEnvironment (current : (P).Execution) :
    (execution runtime leaks recoveryLeaks current).observeEnvironment (R) =
      environmentView runtime leaks recoveryLeaks (current.observeEnvironment (P)) := rfl

theorem outputs (past : List (P).PlayerEntry) :
    (R).outputs (past.map (playerEntry runtime leaks recoveryLeaks)) =
      ((P).outputs past).map (Message.mapPayload CommitAttemptPacket.packet) := by
  simp only [ReactiveApplication.outputs, List.filterMap_map, playerEntry,
    List.map_filterMap, Function.comp_def]

theorem known (current : (P).Execution) (who : Player) :
    (execution runtime leaks recoveryLeaks current).network.known who =
      (current.network.known who).map (Message.mapPayload CommitAttemptPacket.packet) :=
  MessageNetwork.mapPayload_known _ _ _

/-- Own response counts are retained by the physical-information projection. -/
theorem submissionCount (past : List (P).PlayerEntry) :
    (R).submissionCount (past.map (playerEntry runtime leaks recoveryLeaks)) =
      (P).submissionCount past := by
  simp only [ReactiveApplication.submissionCount, List.countP_map, Function.comp_def,
    playerEntry, action, ReactiveApplication.Action.isSubmission]
  congr 1
  funext entry
  cases entry.action.transmission <;> rfl

/-- The projection uses only the player's actual remembered and observed packets. -/
theorem knownPackets (past : List (P).PlayerEntry) (view : (P).PlayerView) :
    ReactiveApplication.ResponseMenu.knownPackets
        (past.map (playerEntry runtime leaks recoveryLeaks))
        (playerView runtime leaks recoveryLeaks view) =
      (ReactiveApplication.ResponseMenu.knownPackets past view).map
        (Message.mapPayload CommitAttemptPacket.packet) := by
  simp only [ReactiveApplication.ResponseMenu.knownPackets, outputs, playerView,
    MessageNetwork.PlayerView.mapPayload, List.map_append]

/-- Project exactly the information available at a player decision. -/
def information (info : (P).Info) : (R).Info :=
  info.map fun pair =>
    (pair.1.map (playerEntry runtime leaks recoveryLeaks),
      playerView runtime leaks recoveryLeaks pair.2)

/-- Observation projection does not inspect the builder's hidden command history. -/
theorem observe_state (who : Player) (state : (P).ProtocolState) :
    (R).observe who (state.map (control runtime leaks recoveryLeaks)) =
      information runtime leaks recoveryLeaks ((P).observe who state) := by
  cases state with
  | none => rfl
  | some current =>
      by_cases active : current.actor = some who <;>
        simp only [Option.map_some, ReactiveApplication.observe, control, active,
          ↓reduceIte, information, Option.map_none, Option.map_some, observe]
      rfl

/-- Reinterpret an untagged response as the same phase submission. -/
def phaseAction (response : (R).Action) : (P).Action := ⟨response.transmission⟩

@[simp] theorem action_phaseAction (response : (R).Action) :
    action runtime leaks recoveryLeaks (phaseAction runtime leaks recoveryLeaks response) =
      response := by cases response; rfl

@[simp] theorem phaseAction_action (response : (P).Action) :
    phaseAction runtime leaks recoveryLeaks (action runtime leaks recoveryLeaks response) =
      response := by cases response; rfl

/-- An arbitrary old policy can ignore the additional phase observation fields.
This is a strategy definition, not a menu or sequential-equilibrium transport claim. -/
def liftPolicy (policy : (R).Policy) : (P).Policy := fun past view =>
  (policy (past.map (playerEntry runtime leaks recoveryLeaks))
    (playerView runtime leaks recoveryLeaks view)).map (phaseAction runtime leaks recoveryLeaks)

end Vegas.EventGraphRuntime.PhaseRecoveryProjection
