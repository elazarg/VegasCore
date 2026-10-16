/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseClearInterval
import Vegas.Pending.PhaseClearHistory
import Vegas.Pending.PhaseCountMenu
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryAtom

/-! # Genuine first full-information hits within a clear attempt -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (initial : PMF (phaseApplication runtime leaks).State)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- At an actual clear ready information history in the original installed
interval, first exclusion, attempt exit and this full information site have
not occurred at any earlier continuation prefix. Therefore the ORIGINAL
stopped atom equals its exact-depth continuation atom for every profile. -/
theorem phase_current_attempt_until_atom
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (initialized : initial = inputs.map (PhaseRuntimeState.initial plan))
    (certificate : (E).WellFoundedHistories)
    (entry final : (app).Control)
    (entryTrace : (E).Trace (some entry)) (finalTrace : (E).Trace (some final))
    (isPrefix : TracePrefix entryTrace finalTrace)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : entry.execution.application.phases = phase :: remaining)
    (event : graph.EventId) (inside : event ∈ phase.events)
    (clear : final.execution.application.current.excluded = ∅)
    (ready : final.execution.application.current.native.config.cut.Ready event)
    (who : Player) (site : (N).InformationSite who)
    (atSite : (N).infoOf who finalTrace = site.1)
    (profile : ∀ owner, (N).BehavioralPolicy owner) :
    let stopped := fun history : (E).History => match history.state with
      | none => False
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.attempt ≠ final.execution.application.attempt ∨
          (N).infoOf who history.trace = site.1
    (N).runBehavioralUntil certificate profile stopped ⟨some entry, entryTrace⟩
        ⟨some final, finalTrace⟩ =
      (N).runBehavioralFrom profile (finalTrace.length - entryTrace.length)
        ⟨some entry, entryTrace⟩ ⟨some final, finalTrace⟩ := by
  classical
  intro stopped
  apply (N).runBehavioralUntil_apply_of_first_hit certificate profile stopped
    ⟨some entry, entryTrace⟩ ⟨some final, finalTrace⟩ isPrefix
      (Or.inl (Or.inr (Or.inr atSite)))
  intro middle earlier later shorter
  rcases middle with ⟨state, middleTrace⟩
  cases state with
  | none => exact not_false
  | some current =>
      have interval := phase_interval_of_between_clear_ready runtime leaks menu initial horizon
        scheduler entry final entryTrace finalTrace phase remaining installed event inside clear
          ready current middleTrace earlier later
      have finalInterval := phase_phases_eq_of_clear_unfinished_prefix runtime leaks menu initial
        horizon scheduler entry final entryTrace finalTrace isPrefix phase remaining installed
          event inside clear ready.1
      have middleGeneration : current.execution.application.generation = 0 := by
        subst initial
        exact (phase_clear_history runtime leaks plan inputs horizon scheduler current
          ((menu).toRawTrace _ horizon scheduler middleTrace) interval.1).1
      have finalGeneration : final.execution.application.generation = 0 := by
        subst initial
        exact (phase_clear_history runtime leaks plan inputs horizon scheduler final
          ((menu).toRawTrace _ horizon scheduler finalTrace) clear).1
      have sameAttempt : current.execution.application.attempt =
          final.execution.application.attempt := by
        simp only [PhaseRuntimeState.attempt, interval.2, finalInterval.trans installed,
          middleGeneration, finalGeneration]
      have differentInfo : (N).infoOf who middleTrace ≠ site.1 := by
        intro same
        have antichain := (menu).decisionInformationAntichain initial horizon scheduler who site
        have identical := site.eq_of_common_descendant (N) antichain
          ⟨⟨some current, middleTrace⟩, same⟩ ⟨⟨some final, finalTrace⟩, atSite⟩
            ⟨some final, finalTrace⟩ later.reachesWithin (ReachesWithin.refl 0 _)
        have lengths := congrArg
          (fun history : (N).InformationHistory who site.1 => history.1.trace.length) identical
        change middleTrace.length = finalTrace.length at lengths
        change middleTrace.length < finalTrace.length at shorter
        omega
      exact fun excluded => excluded.elim (fun failed => failed interval.1)
        (fun other => other.elim (fun changed => changed sameAttempt) differentInfo)

end Vegas.EventGraphRuntime
