/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveRuntime
import Interaction.ReactiveSubmissionSerial
import Interaction.ReactiveResponseNormalization

/-! # Forgetting permanent exclusion in native views and recall

The projection retains every actual envelope and recalled response. Responses
commute with it while the exclusion set is empty; after exclusion the recovery
contract deliberately suppresses tokens that the default contract could issue.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

def action (response : (runtime.recoveryApplication leaks).Action) :
    (runtime.reactiveApplication leaks).Action := ⟨response.transmission⟩

def playerView (view : (runtime.recoveryApplication leaks).PlayerView) :
    (runtime.reactiveApplication leaks).PlayerView :=
  ⟨view.messages, view.application.1, view.receipts⟩

def playerEntry (entry : (runtime.recoveryApplication leaks).PlayerEntry) :
    (runtime.reactiveApplication leaks).PlayerEntry :=
  ⟨playerView runtime leaks entry.beforeView, action runtime leaks entry.action, entry.emitted⟩

def environmentView (view : (runtime.recoveryApplication leaks).EnvironmentView) :
    (runtime.reactiveApplication leaks).EnvironmentView :=
  ⟨view.network, view.application.1, view.receipts⟩

def command : (runtime.recoveryApplication leaks).Command →
    (runtime.reactiveApplication leaks).Command
  | .activate who => .activate who
  | .include id => .include id
  | .application command => .application command
  | .wait => .wait

def environmentEntry (entry : (runtime.recoveryApplication leaks).EnvironmentEntry) :
    (runtime.reactiveApplication leaks).EnvironmentEntry :=
  ⟨environmentView runtime leaks entry.beforeView, command runtime leaks entry.command⟩

def execution (current : (runtime.recoveryApplication leaks).Execution) :
    (runtime.reactiveApplication leaks).Execution :=
  ⟨current.application.native, current.network, current.receipts,
    fun who => (current.recall who).map (playerEntry runtime leaks),
    current.environmentRecall.map (environmentEntry runtime leaks)⟩

def control (current : (runtime.recoveryApplication leaks).Control) :
    (runtime.reactiveApplication leaks).Control :=
  ⟨current.remaining, current.actor, execution runtime leaks current.execution⟩

theorem observe (current : (runtime.recoveryApplication leaks).Execution) (who : Player) :
    (execution runtime leaks current).observe (runtime.reactiveApplication leaks) who =
      playerView runtime leaks (current.observe (runtime.recoveryApplication leaks) who) := rfl

theorem observeEnvironment (current : (runtime.recoveryApplication leaks).Execution) :
    (execution runtime leaks current).observeEnvironment (runtime.reactiveApplication leaks) =
      environmentView runtime leaks
        (current.observeEnvironment (runtime.recoveryApplication leaks)) := rfl

theorem outputs (past : List (runtime.recoveryApplication leaks).PlayerEntry) :
    (runtime.reactiveApplication leaks).outputs (past.map (playerEntry runtime leaks)) =
      (runtime.recoveryApplication leaks).outputs past := by
  simp only [ReactiveApplication.outputs, List.filterMap_map, Function.comp_def, playerEntry]

theorem submissionCount (past : List (runtime.recoveryApplication leaks).PlayerEntry) :
    (runtime.reactiveApplication leaks).submissionCount (past.map (playerEntry runtime leaks)) =
      (runtime.recoveryApplication leaks).submissionCount past := by
  simp only [ReactiveApplication.submissionCount, List.countP_map, Function.comp_def,
    playerEntry, action,
    ReactiveApplication.Action.isSubmission]
  congr 1
  funext entry
  cases entry.action.transmission <;> rfl

theorem knownPackets (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView) :
    ReactiveApplication.ResponseMenu.knownPackets
        (past.map (playerEntry runtime leaks)) (playerView runtime leaks view) =
      ReactiveApplication.ResponseMenu.knownPackets past view := by
  simp only [ReactiveApplication.ResponseMenu.knownPackets, outputs, playerView]

theorem inputRecall (current : (runtime.recoveryApplication leaks).Execution)
    (recalled : current.InputRecall (runtime.recoveryApplication leaks)) :
    (execution runtime leaks current).InputRecall (runtime.reactiveApplication leaks) := by
  intro who
  exact (recalled who).trans (outputs runtime leaks (current.recall who)).symm

theorem serialRecall (current : (runtime.recoveryApplication leaks).Execution)
    (recalled : current.SerialRecall (runtime.recoveryApplication leaks)) :
    (execution runtime leaks current).SerialRecall (runtime.reactiveApplication leaks) := by
  intro who
  exact (recalled who).trans (submissionCount runtime leaks (current.recall who)).symm

theorem initial (state : RecoveryState graph) :
    execution runtime leaks
        (ReactiveApplication.Execution.initial (runtime.recoveryApplication leaks) state) =
      ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state.native := rfl

/-- Clear recovery responses have the same native state, traffic, and full
projected private recall as default-runtime responses. -/
theorem respond_of_empty (current : (runtime.recoveryApplication leaks).Execution)
    (empty : current.application.excluded = ∅) (who : Player)
    (response : (runtime.recoveryApplication leaks).Action) :
    execution runtime leaks (current.respond (runtime.recoveryApplication leaks) who response) =
      (execution runtime leaks current).respond (runtime.reactiveApplication leaks) who
        (action runtime leaks response) := by
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
          have submitted :
              ((runtime.recoveryApplication leaks).submit current.application who
                material).excluded = ∅ := empty
          have packet :
              (runtime.recoveryApplication leaks).packet
                  ((runtime.recoveryApplication leaks).submit current.application who material)
                  who (current.network.known who) material =
                (runtime.reactiveApplication leaks).packet
                  ((runtime.reactiveApplication leaks).submit current.application.native who
                    material) who (current.network.known who) material :=
            RecoveryState.emit_of_empty
            ((runtime.recoveryApplication leaks).submit current.application who material)
            submitted who (current.network.known who) material
          simp only [ReactiveApplication.Execution.respond, execution, action]
          rw [packet]
          congr 1
          funext observer
          split <;> simp_all only [List.map_append, List.map_cons, List.map_nil]
          rfl

end Vegas.EventGraphRuntime.RecoveryProjection
