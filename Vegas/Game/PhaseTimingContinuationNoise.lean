/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseClearInterval
import Vegas.Game.PhaseTimingValueNoise
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay

/-! # Original full-entry continuation atoms inside an opaque commitment interval -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {graph : EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (initial : PMF (phaseApplication runtime leaks).State)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- At a genuine clear ready commitment endpoint, every NEW own response has
its actual clear commitment callback and counted menu. The existing runner's
exact path atom is a profile-independent transition factor times these new
response factors. The original full entry history and old recall are retained. -/
theorem phase_timing_continuation_callback_factor
    (entry final : (app).Control)
    (entryTrace : (E).Trace (some entry)) (finalTrace : (E).Trace (some final))
    (isPrefix : TracePrefix entryTrace finalTrace)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : entry.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (event : graph.EventId) (inside : event ∈ phase.events)
    (clear : final.execution.application.current.excluded = ∅)
    (ready : final.execution.application.current.native.config.cut.Ready event) :
    ∃ records : ∀ who, List ((N).InfoState who × (E).Action who),
      (∀ who, (N).ownPlay who finalTrace = records who ++ (N).ownPlay who entryTrace) ∧
      (∀ who record, record ∈ records who →
        ∃ (current : (app).Control) (trace : (E).Trace (some current)),
          TracePrefix entryTrace trace ∧ TracePrefix trace finalTrace ∧
          current.actor = some who ∧
          record.1 = some (current.execution.recall who, current.execution.observe app who) ∧
          record.2 ∈ PhaseCount.onePacketActions runtime leaks bounds who
            (current.execution.recall who) (current.execution.observe app who) ∧
          current.execution.application.phases = phase :: remaining ∧ phase.kind = .commitment ∧
          current.execution.application.current.excluded = ∅) ∧
      ∃ chance : ℝ, 0 ≤ chance ∧
        ∀ profile : ∀ who, (N).BehavioralPolicy who,
          (((N).runBehavioralFrom profile (finalTrace.length - entryTrace.length)
            ⟨some entry, entryTrace⟩) ⟨some final, finalTrace⟩).toReal =
            chance * ∏ who, (N).ownPlayReachProbability (profile who) (records who) := by
  obtain ⟨records, recordEq, provenance, chance, nonnegative, _natureMass, factor⟩ :=
    (N).exists_continuation_ownPlay_factor entryTrace finalTrace isPrefix
  refine ⟨records, recordEq, ?_, chance, nonnegative, factor⟩
  intro who record member
  obtain ⟨before, joint, legal, next, realized, earlier, later, observed, selected⟩ :=
    provenance who record member
  have legalOption := (E).legalOption_of_legal legal who
  rw [selected] at legalOption
  change (app).actor before.state = some who ∧ _ at legalOption
  obtain ⟨active, offered⟩ := legalOption
  rcases before with ⟨state, beforeTrace⟩
  cases state with
  | none =>
      change (none : Option Player) = some who at active
      cases active
  | some current =>
      have acting : current.actor = some who := active
      have retained : TracePrefix beforeTrace finalTrace :=
        (TracePrefix.extend TracePrefix.refl joint legal realized).trans later
      have interval := phase_interval_of_between_clear_ready runtime leaks menu initial horizon
        scheduler entry final entryTrace finalTrace phase remaining installed event inside clear
          ready current beforeTrace earlier retained
      have input : (N).infoOf who beforeTrace =
          some (current.execution.recall who, current.execution.observe app who) :=
        ((menu).info initial horizon scheduler who beforeTrace).trans (by
          simp only [ReactiveApplication.observe, acting, ite_true])
      change record.2 ∈ PhaseCount.onePacketActions runtime leaks bounds who
        (current.execution.recall who) (current.execution.observe app who) at offered
      exact ⟨current, beforeTrace, earlier, retained, acting, observed.symm.trans input, offered,
        interval.2, committing, interval.1⟩

end Vegas
