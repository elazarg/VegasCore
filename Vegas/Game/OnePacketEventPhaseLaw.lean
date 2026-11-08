/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound
import Vegas.Game.OnePacketCompletion
import Vegas.Pending.ReactiveGraphSteps

/-! # Completion phases before the first public default -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

local notation "menu" => bounds.onePacketMenu timeouts leaks
local notation "N" => ReactiveApplication.ResponseMenu.information
  (MessageBounds.onePacketMenu timeouts leaks bounds) (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup timeouts leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

/-- From a clear sequential prefix, adding a public-default stop preserves the
entire current-event completion law, including automatic completion. -/
theorem pending_until_eq_clearUntil
    (certificate : (E).WellFoundedHistories) (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup timeouts leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : control.execution.application.config.defaulted = ∅)
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event) :
    (N).runBehavioralUntil certificate players
        (LateStopped setup timeouts leaks bounds horizon scheduler rank) start =
      (N).runBehavioralUntil certificate players
        (fun final => LateStopped setup timeouts leaks bounds horizon scheduler rank final ∨
          ¬ Clear final.state) start := by
  classical
  let late := LateStopped setup timeouts leaks bounds horizon scheduler rank
  let early := fun final : (E).History => late final ∨ ¬ Clear final.state
  have lower : rank ≤ event.val := Nat.le_of_not_gt fun earlier =>
    ready.1 ((ordered.2 event).mpr earlier)
  have within : rank < (graph setup).order.eventCount := lt_of_le_of_lt lower event.isLt
  have eventRank : event.val = rank := congrArg Fin.val
    (setup.eventGraph.sequentialize_ready_unique _ ready (ordered.ready within))
  suffices agree : ∀ history,
      (late history ∨ ∃ before : (application setup timeouts leaks).Control,
        history.state = some before ∧
          before.execution.application.config = control.execution.application.config) →
      (N).runBehavioralUntil certificate players late history =
        (N).runBehavioralUntil certificate players early history from
    agree start (Or.inr ⟨control, current, rfl⟩)
  intro history
  induction history using certificate.induction with
  | _ history ih =>
  intro inside
  by_cases halted : late history
  · rw [(N).runBehavioralUntil_of_stopped certificate players halted,
      (N).runBehavioralUntil_of_stopped certificate players (Or.inl halted : early history)]
  obtain ⟨before, state, configEq⟩ := inside.resolve_left halted
  have clearNow : Clear history.state := by
    rw [state]
    change before.execution.application.config.defaulted = ∅
    rw [configEq]
    exact clear
  have going : ¬ early history := fun stopped => stopped.elim halted (fun failed => failed clearNow)
  by_cases terminal : (E).terminal history.state
  · rw [(N).runBehavioralUntil_of_terminal certificate players terminal,
      (N).runBehavioralUntil_of_terminal certificate players terminal]
  rw [(N).runBehavioralUntil_of_running certificate players halted terminal,
    (N).runBehavioralUntil_of_running certificate players going terminal]
  apply bind_congr_on_support
  intro next member
  have extension := (N).mem_support_runBehavioralFrom_one players terminal member
  obtain ⟨joint, _, realized⟩ := extension.1
  change next.state ∈ ((application setup timeouts leaks).transition (initialLaw setup)
    horizon scheduler history.state joint).support at realized
  rw [state] at realized
  obtain ⟨after, afterState, _⟩ := (application setup timeouts leaks).transition_recall_prefix
    (initialLaw setup) horizon scheduler before next.state joint realized
  apply ih next extension.1
  by_cases done : event ∈ after.execution.application.config.cut.completed
  · exact Or.inl ⟨after, afterState, event, done, eventRank⟩
  · have beforeReady : before.execution.application.config.cut.Ready event := configEq.symm ▸ ready
    have path := reactive_protocol_graph_steps timeouts leaks (initialLaw setup) horizon scheduler
      before after joint (afterState ▸ realized)
    exact Or.inr ⟨after, afterState,
      (EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
        (fun other otherReady =>
          setup.eventGraph.sequentialize_ready_unique _ otherReady beforeReady) done path).trans
        configEq⟩

end Vegas
