/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseAttemptControls
import Vegas.Pending.PhaseServiceContract
import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseArchivedBindings
import Vegas.Pending.PhaseReadyRequests
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryAtom
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhaseRetiredCompletion
import Vegas.Pending.ReactiveBindingFrameStep

/-! # Actual phase results at the first namespace exit -/

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

omit [Fintype Player] in
private theorem settle_closed_record
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (active : current.FailureCoverage)
    (closed : (PhaseRuntimeState.settle (phase :: remaining) generation entry current
      retired).attempt ≠ ⟨phase.low, generation⟩)
    (trigger : (PhaseRuntimeState.settle (phase :: remaining) generation entry current
      retired).generation ≠ generation ∨ phase.kind = .commitment ∧
        ((((PhaseRuntimeState.settle (phase :: remaining) generation entry current
          retired).current.excluded) \ entry.excluded) ∩ phase.owners).Nonempty) :
    ∃ record ∈ (PhaseRuntimeState.settle (phase :: remaining) generation entry current
      retired).retired, record.attempt = ⟨phase.low, generation⟩ ∧
        phase.events ⊆ record.state.config.cut.completed ∧ record.state.ReceiptsComplete ∧
        ∀ event owner, graph.actor? event = some owner → record.state.PublicFailure event →
          owner ∈ (PhaseRuntimeState.settle (phase :: remaining) generation entry current
            retired).current.excluded := by
  classical
  let record : RetiredCommitAttempt graph := ⟨⟨phase.low, generation⟩, (phase.drain current).native⟩
  by_cases finished : phase.Finished (phase.drain current)
  · by_cases failed : phase.kind = .commitment ∧
        (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty
    · have archived : record ∈ (PhaseRuntimeState.settle (phase :: remaining) generation entry
          current retired).retired := by
        by_cases survives : (phase.owners \ (phase.drain current).excluded).Nonempty
        · rw [PhaseRuntimeState.settle_retry phase remaining generation entry current retired
            finished failed.1 failed.2 survives]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · rw [PhaseRuntimeState.settle_exhausted phase remaining generation entry current retired
            finished failed.1 failed.2 survives]
          exact (PhaseRuntimeState.settle_archive _ _ _ _ _).subset
            (List.mem_append_right _ (List.mem_singleton_self _))
      refine ⟨record, archived, rfl, finished, (active.drain phase).receipts, ?_⟩
      intro event owner acting failure
      have covered := (active.drain phase).covered event owner acting failure
      rw [(PhaseRuntimeState.settle_physical (phase :: remaining) generation entry current
        retired).1]
      simpa only [RuntimePhase.drain_excluded] using covered
    · rcases trigger with changed | failure
      · rw [PhaseRuntimeState.settle_clean phase remaining generation entry current retired
          finished failed] at changed
        exact (changed (PhaseRuntimeState.settle_generation_archive_of_same_excluded remaining
          generation (phase.drain current) (phase.drain current) retired rfl).1).elim
      · apply (failed ?_).elim
        rw [(PhaseRuntimeState.settle_physical (phase :: remaining) generation entry current
          retired).1] at failure
        simpa only [RuntimePhase.drain_excluded] using failure
  · simp only [PhaseRuntimeState.settle, finished, ↓reduceIte, PhaseRuntimeState.attempt,
      List.head?_cons, Option.map_some, Option.getD_some] at closed
    exact (closed rfl).elim

omit [Fintype Player] in
private theorem normalize_closed_record (state : PhaseRuntimeState graph)
    (active : state.current.FailureCoverage) (phase : RuntimePhase graph)
    (installed : phase ∈ state.phases.head?)
    (closed : state.normalize.attempt ≠ state.attempt)
    (trigger : state.normalize.generation ≠ state.generation ∨ phase.kind = .commitment ∧
      ((state.normalize.current.excluded \ state.entry.excluded) ∩ phase.owners).Nonempty) :
    ∃ record ∈ state.normalize.retired, record.attempt = state.attempt ∧
      phase.events ⊆ record.state.config.cut.completed ∧ record.state.ReceiptsComplete ∧
      ∀ event owner, graph.actor? event = some owner → record.state.PublicFailure event →
        owner ∈ state.normalize.current.excluded := by
  obtain ⟨remaining, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
  have result := settle_closed_record phase remaining state.generation state.entry state.current
    state.retired active (by
      simpa only [PhaseRuntimeState.normalize, phases, PhaseRuntimeState.attempt, List.head?_cons,
        Option.map_some, Option.getD_some] using closed)
      (by simpa only [PhaseRuntimeState.normalize, phases] using trigger)
  simpa only [PhaseRuntimeState.normalize, phases, PhaseRuntimeState.attempt, List.head?_cons,
    Option.map_some, Option.getD_some] using result

omit [Fintype Player] in
private theorem closed_attempt_step : (app).StepRelation (fun before after =>
    before.current.FailureCoverage → ∀ phase ∈ before.phases.head?,
      after.attempt ≠ before.attempt →
      (after.generation ≠ before.generation ∨ phase.kind = .commitment ∧
        ((after.current.excluded \ before.entry.excluded) ∩ phase.owners).Nonempty) →
        ∃ record ∈ after.retired, record.attempt = before.attempt ∧
          phase.events ⊆ record.state.config.cut.completed ∧ record.state.ReceiptsComplete ∧
          ∀ event owner, graph.actor? event = some owner → record.state.PublicFailure event →
            owner ∈ after.current.excluded) where
  refl _ _ _ _ closed := (closed rfl).elim
  submit _ _ _ _ _ _ closed := (closed rfl).elim
  handle state message next accepted active phase installed closed trigger := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact normalize_closed_record
        {state with current := state.current.inclusionResult message.payload.packet.call native}
        (active.inclusionResult runtime _ native handled) phase installed closed trigger
    · cases accepted
  environment state command next reached active phase installed closed trigger := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact normalize_closed_record
        {state with current := state.current.environmentResult command native}
        (active.environmentResult runtime command native supported) phase installed closed trigger
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact (closed rfl).elim

/-- The original completion contract forces the actual stopped continuation to
leave its full attempt namespace. Native completion membership is retained on
same-generation advancement; original binding failures are also retained in
their exact archive, including exhausted restores without a generation change. -/
theorem phase_attempt_stopped_results
    (delay bound : graph.EventId → Nat)
    (contract : PhaseService.AsyncContract runtime leaks initial horizon scheduler delay bound)
    (profile : ∀ who, (N).BehavioralPolicy who)
    (start : (app).Control) (trace : (E).Trace (some start))
    (phase : RuntimePhase graph)
    (installed : phase ∈ start.execution.application.phases.head?) :
    let stopped := fun history : (E).History => match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ start.execution.application.attempt
    ∀ final ∈ ((N).runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories
        profile stopped ⟨some start, trace⟩).support,
      ∃ ending : (app).Control, final.state = some ending ∧ TracePrefix trace final.trace ∧
        ending.execution.application.attempt ≠ start.execution.application.attempt ∧
        (ending.execution.application.generation = start.execution.application.generation →
          phase.events ⊆ ending.execution.application.current.native.config.cut.completed) ∧
        (ending.execution.application.generation ≠ start.execution.application.generation →
          ∃ record ∈ ending.execution.application.retired,
            record.attempt = start.execution.application.attempt ∧
              phase.events ⊆ record.state.config.cut.completed ∧ record.state.ReceiptsComplete ∧
              record.state.BindingInvariant ∧ (∃ draw, record.state.Invariant draw) ∧
              KeepsFixedCandidates record.state ending.execution.application.current.native ∧
              ∀ event owner, graph.actor? event = some owner → record.state.PublicFailure event →
                owner ∈ ending.execution.application.current.excluded) ∧
        (phase.kind = .commitment ∧
          ((ending.execution.application.current.excluded \
            start.execution.application.entry.excluded) ∩ phase.owners).Nonempty →
          ∃ record ∈ ending.execution.application.retired,
            record.attempt = start.execution.application.attempt ∧
              phase.events ⊆ record.state.config.cut.completed ∧ record.state.ReceiptsComplete ∧
              record.state.BindingInvariant ∧ (∃ draw, record.state.Invariant draw) ∧
              KeepsFixedCandidates record.state ending.execution.application.current.native ∧
              ∀ event owner, graph.actor? event = some owner → record.state.PublicFailure event →
                owner ∈ ending.execution.application.current.excluded) := by
  classical
  intro stopped
  let property : (app).ProtocolState → Prop := fun state =>
    ∃ current : (app).Control, state = some current ∧
      current.execution.application.phases <:+ start.execution.application.phases ∧
      (current.execution.application.attempt = start.execution.application.attempt →
        current.execution.application.phases = start.execution.application.phases) ∧
      (current.execution.application.attempt = start.execution.application.attempt →
        current.execution.application.entry = start.execution.application.entry) ∧
      (current.execution.application.attempt ≠ start.execution.application.attempt →
        (current.execution.application.generation ≠ start.execution.application.generation ∨
          phase.kind = .commitment ∧
            ((current.execution.application.current.excluded \
              start.execution.application.entry.excluded) ∩ phase.owners).Nonempty) →
        ∃ record ∈ current.execution.application.retired,
          record.attempt = start.execution.application.attempt ∧
            phase.events ⊆ record.state.config.cut.completed ∧ record.state.ReceiptsComplete ∧
            ∀ event owner, graph.actor? event = some owner → record.state.PublicFailure event →
              owner ∈ current.execution.application.current.excluded)
  have holds : property (some start) := by
    refine ⟨start, rfl, ⟨[], rfl⟩, fun _ => rfl, fun _ => rfl, ?_⟩
    intro closed
    exact (closed rfl).elim
  have preserved : ∀ history : (E).History, ¬ stopped history → ¬ (E).terminal history.state →
      ∀ joint (legal : (E).Legal history.state joint) target, property history.state →
        target ∈ ((E).step history.state ⟨joint, legal⟩).support → property target := by
    intro history running _notTerminal joint _legal target valid moved
    obtain ⟨current, stateEq, suffix, phasesKept, entryKept, _previous⟩ := valid
    have raw := (menu).toRawTrace initial horizon scheduler (stateEq ▸ history.trace)
    have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
      (fun state member => by
        obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        exact PhaseRuntimeState.initial_ordered plan draw) raw
    have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler raw
    have same : current.execution.application.attempt = start.execution.application.attempt := by
      by_contra different
      exact running (by simpa only [stopped, stateEq] using different)
    have realized : target ∈ ((app).transition initial horizon scheduler (some current)
        joint).support := by
      change target ∈ ((app).transition initial horizon scheduler history.state joint).support
        at moved
      simpa only [stateEq] using moved
    obtain ⟨next, rfl, _recall⟩ := (app).transition_recall_prefix initial horizon scheduler current
      target joint realized
    refine ⟨next, rfl, ?_, ?_, ?_, ?_⟩
    · exact ((phaseApplication_phaseSuffix runtime leaks).transition initial horizon scheduler
        current next joint realized).trans suffix
    · intro sameNext
      exact ((phaseApplication_sameAttempt_controls runtime leaks).transition initial horizon
        scheduler current next joint realized ordered (same.trans sameNext.symm)).1.trans
          (phasesKept same)
    · intro sameNext
      exact ((phaseApplication_sameAttempt_entry runtime leaks).transition initial horizon
        scheduler current next joint realized ordered (same.trans sameNext.symm)).trans
          (entryKept same)
    · intro closed trigger
      have installedNow : phase ∈ current.execution.application.phases.head? := by
        simpa only [phasesKept same] using installed
      have result := (closed_attempt_step runtime leaks).transition initial horizon
        scheduler current next joint realized coverage.active phase installedNow
      have closing : next.execution.application.attempt ≠
          current.execution.application.attempt := fun equal => closed (equal.trans same)
      have triggering : next.execution.application.generation ≠
          current.execution.application.generation ∨ phase.kind = .commitment ∧
            ((next.execution.application.current.excluded \
              current.execution.application.entry.excluded) ∩ phase.owners).Nonempty := by
        rcases trigger with changed | failed
        · exact Or.inl (fun equal => changed (equal.trans
            (congrArg CommitAttemptId.generation same)))
        · exact Or.inr (by simpa only [entryKept same] using failed)
      obtain ⟨record, member, address, completed, receipts, covered⟩ := result closing triggering
      exact ⟨record, member, address.trans same, completed, receipts, covered⟩
  intro final supported
  obtain ⟨ending, stateEq, suffix, samePhases, _sameEntry, archived⟩ :=
    (N).runBehavioralUntil_support_closed_of_going
      ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped property
        preserved ⟨some start, trace⟩ holds final supported
  have finalRaw := (menu).toRawTrace initial horizon scheduler (stateEq ▸ final.trace)
  have live := (phaseApplication_live runtime leaks).history initial horizon scheduler
    (fun state member => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact ⟨PhaseRuntimeState.initial_frontier plan draw,
        PhaseRuntimeState.initial_live plan draw⟩) finalRaw
  have changed : ending.execution.application.attempt ≠ start.execution.application.attempt := by
    rcases (N).mem_support_runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
        ⟨some start, trace⟩ final supported with halted | terminal
    · simpa only [stopped, stateEq] using halted
    · intro same
      have completed := contract.completes ending finalRaw (stateEq ▸ terminal)
      have installedNow : phase ∈ ending.execution.application.phases.head? := by
        simpa only [samePhases same] using installed
      exact live.2 phase installedNow (fun event _inside => completed.symm ▸ Finset.mem_univ event)
  have archive (trigger : ending.execution.application.generation ≠
      start.execution.application.generation ∨ phase.kind = .commitment ∧
        ((ending.execution.application.current.excluded \
          start.execution.application.entry.excluded) ∩ phase.owners).Nonempty) :
      ∃ record ∈ ending.execution.application.retired,
        record.attempt = start.execution.application.attempt ∧
          phase.events ⊆ record.state.config.cut.completed ∧ record.state.ReceiptsComplete ∧
          record.state.BindingInvariant ∧ (∃ draw, record.state.Invariant draw) ∧
          KeepsFixedCandidates record.state ending.execution.application.current.native ∧
          ∀ event owner, graph.actor? event = some owner → record.state.PublicFailure event →
            owner ∈ ending.execution.application.current.excluded := by
    obtain ⟨record, member, address, completed, receipts, covered⟩ := archived changed trigger
    obtain ⟨binding, native, fixed⟩ :=
      phaseRetiredBindings_history runtime leaks plan inputs horizon scheduler finalRaw
        record member
    exact ⟨record, member, address, completed, receipts, binding, native, fixed, covered⟩
  refine ⟨ending, stateEq, (N).runBehavioralUntil_support_prefix
    ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
      ⟨some start, trace⟩ final supported, changed, ?_, ?_, ?_⟩
  · intro generation event inside
    have phaseDifferent : start.execution.application.attempt.phase ≠
        ending.execution.application.attempt.phase := by
      intro same
      apply changed
      have generationEq : ending.execution.application.attempt.generation =
          start.execution.application.attempt.generation := generation
      have equal (first second : CommitAttemptId) (phases : first.phase = second.phase)
          (generations : first.generation = second.generation) : first = second := by
        cases first
        cases second
        cases phases
        cases generations
        rfl
      exact equal _ _ same.symm generationEq
    have startRaw := (menu).toRawTrace initial horizon scheduler trace
    have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
      (fun state member => by
        obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        exact PhaseRuntimeState.initial_ordered plan draw) startRaw
    have earlier := PhaseRuntimeState.event_before_later_phase start.execution.application
      ending.execution.application ordered suffix phaseDifferent event ⟨phase, installed, inside⟩
    cases phases : ending.execution.application.phases with
    | nil => exact live.1.terminal phases ▸ Finset.mem_univ event
    | cons next rest =>
      have positioned := live.1.positioned
      rw [phases] at positioned
      exact positioned.2.1 event (by
        simpa only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
          Option.getD_some] using earlier)
  · intro generation
    exact archive (Or.inl generation)
  · intro failed
    exact archive (Or.inr failed)

end Vegas.EventGraphRuntime
