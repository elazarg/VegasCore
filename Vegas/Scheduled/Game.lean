/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Game
import Vegas.Scheduled.Compiled

/-!
# Games implemented by the serialized graph runtime

This file closes the construction gap between `Machine.Program.game` and the
actual scheduled execution protocol. The target game uses the serializer's
states, public order log, player-local menus, and transition law directly.

The scheduler remains an execution coordinate. Its utility is supplied only so
the generic `UtilityGame` carrier is well typed; player-equilibrium claims do
not quantify over scheduler deviations. Every original player's utility reads
only the settled graph configuration and is definitionally blind to the order
log.
-/

noncomputable section

namespace Vegas

open GameTheory
open GameTheory.Protocol
open GameTheory.Languages

namespace Machine.Program

variable {Player : Type} [DecidableEq Player] [Fintype Player]
variable {L : IExpr}

/-- The permissive serialized state machine generated from a compiled machine
program. -/
@[reducible] def serializedSystem (program : Program Player L) :
    ScheduledSystem Player :=
  Compiled.serializedSystem program.graph program.graphWF program.guardLive

/-- The informed game arena of the actual serializer. The published order is
retained in each participant's information state, together with perfect recall
of that participant's own decisions. -/
def serializedArena (program : Program Player L) :
    FOSG.Game (Participant Player) where
  execution := program.serializedSystem.toExecutionProtocol
  information := program.serializedSystem.revealingInformation

/-- Erase runtime order observations from one original player's serialized
information while retaining the current source observation and every earlier
decision by that player. -/
def eraseSerializedPlayerInformation (program : Program Player L)
    (who : Player)
    (info : program.serializedSystem.RevealingInfo (.player who)) :
    EventGraph.PlayerInformation program.graph who where
  current := info.current
  own := info.own.map fun remembered =>
    (remembered.1.1, remembered.2)

/-- Erasure changes information, not the action menu. Both semantics totalize
unreachable observations with the idle choice, so this equality also holds at
counterfactual information values that no execution reaches. -/
theorem serializedPlayerMenu_eq (program : Program Player L) (who : Player)
    (info : program.serializedSystem.RevealingInfo (.player who)) :
    program.serializedArena.information.menu (.player who) info =
      program.information.menu who
        (program.eraseSerializedPlayerInformation who info) := by
  change program.serializedSystem.menuAt who info.current =
    EventGraph.localMenu program.graph program.graphWF program.guardLive who
      { current := info.current,
        own := info.own.map fun remembered =>
          (remembered.1.1, remembered.2) }
  exact Vegas.Compiled.serializedSystem_playerMenu_eq_localMenu
    program.graph program.graphWF program.guardLive who info.current _

/-- Source and serialized choices are equivalent at corresponding player
information. Only their menu certificates differ. -/
def serializedPlayerChoiceEquiv (program : Program Player L) (who : Player)
    (info : program.serializedSystem.RevealingInfo (.player who)) :
    program.information.Choice who
        (program.eraseSerializedPlayerInformation who info) ≃
      program.serializedArena.information.Choice (.player who) info where
  toFun choice := ⟨choice.1, by
    rw [program.serializedPlayerMenu_eq who info]
    exact choice.2⟩
  invFun choice := ⟨choice.1, by
    rw [← program.serializedPlayerMenu_eq who info]
    exact choice.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Compile a source behavioral policy to the real serialized information
model. The compiled policy ignores order history; target deviations need not. -/
def compileSerializedBehavioralPolicy (program : Program Player L)
    (who : Player) (policy : program.information.BehavioralPolicy who) :
    program.serializedArena.information.BehavioralPolicy (.player who) :=
  fun info =>
    (policy (program.eraseSerializedPlayerInformation who info)).map
      (program.serializedPlayerChoiceEquiv who info)

/-- The serialized information held initially by an original player. -/
def serializedInitialPlayerInformation (program : Program Player L)
    (who : Player) :
    program.serializedSystem.RevealingInfo (.player who) where
  current :=
    (EventGraph.publicObserve program.graph (EventGraph.Config.initial _),
      EventGraph.observe program.graph (EventGraph.Config.initial _) who)
  past := []
  own := []

@[simp] theorem eraseSerializedInitialPlayerInformation
    (program : Program Player L) (who : Player) :
    program.eraseSerializedPlayerInformation who
        (program.serializedInitialPlayerInformation who) =
      { current :=
          (EventGraph.publicObserve program.graph (EventGraph.Config.initial _),
            EventGraph.observe program.graph (EventGraph.Config.initial _) who),
        own := [] } := by
  rfl

@[simp] theorem serializedInfoOf_start_player
    (program : Program Player L) (who : Player) :
    program.serializedArena.information.infoOf (.player who)
        (ExecutionProtocol.Trace.start :
          program.serializedArena.execution.Trace
            program.serializedArena.execution.init) =
      program.serializedInitialPlayerInformation who := by
  rfl

@[simp] theorem sourceInfoOf_start_eq_erasedSerialized
    (program : Program Player L) (who : Player) :
    program.information.infoOf who
        (ExecutionProtocol.Trace.start :
          program.execution.Trace program.execution.init) =
      program.eraseSerializedPlayerInformation who
        (program.serializedInitialPlayerInformation who) := by
  rfl

/-- At the first strategic frontier, the real serialized policy draws exactly
the compiled source choice law. The current scheduler order is selected
simultaneously and is not present in this information state. -/
theorem compileSerializedBehavioralPolicy_initial
    (program : Program Player L) (who : Player)
    (policy : program.information.BehavioralPolicy who) :
    program.compileSerializedBehavioralPolicy who policy
        (program.serializedInitialPlayerInformation who) =
      (policy (program.information.infoOf who
        (ExecutionProtocol.Trace.start :
          program.execution.Trace program.execution.init))).map
        (program.serializedPlayerChoiceEquiv who
          (program.serializedInitialPlayerInformation who)) := by
  rfl

/-- Player utility for a serialized history. The scheduler utility is allowed
to inspect the complete target history; an original player's utility is the
compiled source payoff of the settled graph state and ignores the order log. -/
def settledPlayerUtility (program : Program Player L)
    (state : program.State) (who : Player) : ℝ := by
  classical
  exact
    if program.terminal state then
      match EventGraph.evalPayoffs? program.payoffs state.1.store with
      | some outcome => (outcome who : ℝ)
      | none => 0
    else
      0

def serializedUtility (program : Program Player L)
    (schedulerUtility : program.serializedArena.History → ℝ) :
    program.serializedArena.History → Participant Player → ℝ
  | history, .scheduler => schedulerUtility history
  | history, .player who =>
      program.settledPlayerUtility history.state.base who

@[simp] theorem serializedUtility_player
    (program : Program Player L)
    (schedulerUtility : program.serializedArena.History → ℝ)
    (history : program.serializedArena.History) (who : Player) :
    program.serializedUtility schedulerUtility history (.player who) =
      program.settledPlayerUtility history.state.base who := by
  rfl

/-- Original-player utility cannot distinguish order logs, trace witnesses, or
the scheduler's utility when the settled graph state is the same. -/
theorem serializedUtility_player_eq_of_base_eq
    (program : Program Player L)
    (schedulerUtility : program.serializedArena.History → ℝ)
    (left right : program.serializedArena.History) (who : Player)
    (hbase : left.state.base = right.state.base) :
    program.serializedUtility schedulerUtility left (.player who) =
      program.serializedUtility schedulerUtility right (.player who) := by
  simp only [serializedUtility_player]
  rw [hbase]

/-- The serializer is a finite Vegas game with the same graph-node horizon as
the canonical atomic game. -/
def serializedGame (program : Program Player L)
    (schedulerUtility : program.serializedArena.History → ℝ) :
    Game (Participant Player) where
  arena := program.serializedArena
  utility := program.serializedUtility schedulerUtility
  horizon := program.graph.nodeCount
  bounded := Vegas.Compiled.serializedSystem_boundedHorizon
    program.graph program.graphWF program.guardLive

/-- The actual serialized arena has perfect recall, including for policies
that condition on earlier public orders. -/
theorem serializedPerfectRecall (program : Program Player L) :
    program.serializedArena.information.PerfectRecall :=
  program.serializedSystem.revealingInformation_perfectRecall

/-- At every actual runtime history, each original player's information
determines the scheduler's complete information.  The scheduler may use all
public data and prior orders, but has no additional state signal. -/
theorem serializedSchedulerInfo_eq_fromPlayer
    (program : Program Player L) (who : Player)
    {state : program.serializedArena.execution.State}
    (trace : ExecutionProtocol.Trace program.serializedArena.execution state) :
    program.serializedSystem.schedulerInfoFromPlayer
        (fun seen : EventGraph.PublicObservation program.graph ×
          EventGraph.Observation program.graph who => seen.1)
        (program.serializedSystem.revealingSignals.infoOf
          (.player who) trace) =
      program.serializedSystem.revealingSignals.infoOf
        (.scheduler : Participant Player) trace :=
  Compiled.serializedSystem_schedulerInfo_eq_fromPlayer
    program.graph program.graphWF program.guardLive who trace

/-- The actual serialized game is bounded independently of the scheduler
strategy and of every player strategy. -/
theorem serializedBoundedHorizon (program : Program Player L)
    (schedulerUtility : program.serializedArena.History → ℝ) :
    (program.serializedGame schedulerUtility).arena.execution.BoundedHorizon
      program.graph.nodeCount :=
  (program.serializedGame schedulerUtility).bounded

end Machine.Program

end Vegas
