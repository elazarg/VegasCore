/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseAttemptControls
import Vegas.Pending.PhaseAttemptCheckpoint
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryAtom

/-! # Actual prefix metadata before the first physical-attempt exit -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "E" => menu.protocol initial horizon scheduler
local notation "N" => menu.information initial horizon scheduler

/-- Every proper prefix of an attempt-stopped continuation remains initialized
and ordered, with its original namespace, installed phases and saved entry. -/
theorem phase_attempt_stopped_prefix_metadata
    (profile : ∀ who, (N).BehavioralPolicy who)
    (start : (app).Control) (trace : (E).Trace (some start)) :
    let stopped := fun history : (E).History => match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ start.execution.application.attempt
    ∀ final ∈ ((N).runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
        ⟨some start, trace⟩).support,
      ∀ {target} {prefixTrace : (E).Trace target}, TracePrefix trace prefixTrace →
        TracePrefix prefixTrace final.trace → prefixTrace.length < final.trace.length →
        ∃ current : (app).Control, target = some current ∧
          current.execution.application.Ordered ∧
          current.execution.application.attempt = start.execution.application.attempt ∧
          current.execution.application.phases = start.execution.application.phases ∧
          current.execution.application.entry = start.execution.application.entry := by
  classical
  intro stopped final supported target prefixTrace kept
  have initialized : ∀ state : PhaseRuntimeState graph,
      state ∈ (inputs.map (PhaseRuntimeState.initial plan)).support → state.Ordered := by
    intro state member
    obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered plan draw
  have startOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized (menu.toRawTrace initial horizon scheduler trace)
  have first := (N).runBehavioralUntil_support_first
    ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
      ⟨some start, trace⟩ final supported
  induction kept with
  | refl =>
      intro _beforeFinal _proper
      exact ⟨start, rfl, startOrdered, rfl, rfl, rfl⟩
  | @extend source target earlier kept joint legal realized ih =>
      intro beforeFinal proper
      have earlierFinal := (TracePrefix.extend .refl joint legal realized).trans beforeFinal
      have shorter : earlier.length < final.trace.length := by
        have upper := beforeFinal.length_le
        simp only [Trace.length] at upper
        omega
      obtain ⟨middle, rfl, middleOrdered, same, phases, entry⟩ := ih earlierFinal shorter
      have moved : target ∈ ((app).transition initial horizon scheduler
          (some middle) joint).support := realized
      obtain ⟨next, rfl, _recall⟩ := (app).transition_recall_prefix initial horizon scheduler
        middle target joint moved
      have nextOrdered := (phaseApplication_seedOrder runtime leaks).transition initial horizon
        scheduler initialized (some middle) (some next) joint middleOrdered moved
      have sameNext : next.execution.application.attempt =
          start.execution.application.attempt := by
        by_contra different
        exact first ⟨some next, earlier.extend joint legal realized⟩
          (.extend kept joint legal realized) beforeFinal proper different
      have stepSame := same.trans sameNext.symm
      exact ⟨next, rfl, nextOrdered, sameNext,
        ((phaseApplication_sameAttempt_controls runtime leaks).transition initial horizon
          scheduler middle next joint moved middleOrdered stepSame).1.trans phases,
        ((phaseApplication_sameAttempt_entry runtime leaks).transition initial horizon
          scheduler middle next joint moved middleOrdered stepSame).trans entry⟩

end Vegas.EventGraphRuntime
