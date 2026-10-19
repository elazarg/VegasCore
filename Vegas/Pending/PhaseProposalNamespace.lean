/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseAttemptControls
import Vegas.Pending.PhaseProposalOrigin
import Vegas.Pending.PhaseRetryCompletion

/-! # A publication phase cannot acquire a retry generation -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Normalizing a public phase either consumes its descriptor or leaves the
entire attempt unchanged; only commitment phases can retry. -/
theorem public_settle_same_phase
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (ordered : (phase :: remaining).IsChain fun left right => left.high = right.low)
    (publicPhase : phase.kind ≠ .commitment)
    (same : (PhaseRuntimeState.settle (phase :: remaining) generation
      entry current retired).attempt.phase = phase.low) :
    (PhaseRuntimeState.settle (phase :: remaining) generation entry current retired).attempt =
      (⟨phase.low, generation⟩ : CommitAttemptId) := by
  by_cases finished : phase.Finished (phase.drain current)
  · have later := PhaseRuntimeState.phaseLow_lt_tail phase remaining ordered
    have advanced := (PhaseRuntimeState.settle_namespace remaining generation
      (phase.drain current) (phase.drain current) retired ordered.tail).2
    rw [PhaseRuntimeState.settle_clean phase remaining generation entry current retired finished
      (fun fault => publicPhase fault.1)] at same
    omega
  · simp only [PhaseRuntimeState.settle, finished, ite_false, PhaseRuntimeState.attempt,
      List.head?_cons, Option.map_some, Option.getD_some]

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A single physical transition cannot retry a public phase while retaining
its source phase address. -/
theorem public_same_phase_step :
    (app).StepRelation (fun before after => before.Ordered →
      (∃ phase ∈ before.phases.head?, phase.kind ≠ .commitment) →
      before.attempt.phase = after.attempt.phase → before.attempt = after.attempt) where
  refl _ _ _ _ := rfl
  submit _ _ _ _ _ _ := rfl
  handle state message next accepted ordered publicPhase same := by
    obtain ⟨phase, installed, publicPhase⟩ := publicPhase
    obtain ⟨remaining, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, _handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have result := public_settle_same_phase phase remaining state.generation state.entry
        (state.current.inclusionResult message.payload.packet.call native) state.retired
        (phases ▸ ordered) publicPhase (by
          simpa only [PhaseRuntimeState.normalize, phases, PhaseRuntimeState.attempt,
            List.head?_cons, Option.map_some, Option.getD_some] using same.symm)
      simpa only [PhaseRuntimeState.normalize, phases, PhaseRuntimeState.attempt,
        List.head?_cons, Option.map_some, Option.getD_some] using result.symm
    · cases accepted
  environment state command next reached ordered publicPhase same := by
    obtain ⟨phase, installed, publicPhase⟩ := publicPhase
    obtain ⟨remaining, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, _supported, rfl⟩ := PMF.support_map .. ▸ reached
      have result := public_settle_same_phase phase remaining state.generation state.entry
        (state.current.environmentResult command native) state.retired
        (phases ▸ ordered) publicPhase (by
          simpa only [PhaseRuntimeState.normalize, phases, PhaseRuntimeState.attempt,
            List.head?_cons, Option.map_some, Option.getD_some] using same.symm)
      simpa only [PhaseRuntimeState.normalize, phases, PhaseRuntimeState.attempt,
        List.head?_cons, Option.map_some, Option.getD_some] using result.symm
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl

/-- Namespace monotonicity and the absence of public-phase rollback make an
equal publication phase address sufficient for equality of the full attempt. -/
theorem public_prefix_same_attempt
    (menu : (app).ResponseMenu) (initial : PMF (app).State)
    (initialized : ∀ state ∈ initial.support, state.Ordered) (horizon : Nat)
    (scheduler : (app).Scheduler) (before after : (app).Control)
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (trace : (menu.protocol initial horizon scheduler).Trace (some after))
    (retained : TracePrefix prior trace)
    (publicPhase : ∃ phase ∈ before.execution.application.phases.head?, phase.kind ≠ .commitment)
    (same : before.execution.application.attempt.phase =
      after.execution.application.attempt.phase) :
    before.execution.application.attempt = after.execution.application.attempt := by
  have firstOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler initialized (menu.toRawTrace initial horizon scheduler prior)
  have along : ∀ {target} {targetTrace : (menu.protocol initial horizon scheduler).Trace target},
      TracePrefix prior targetTrace → ∃ next : (app).Control, target = some next ∧
        (before.execution.application.attempt.phase = next.execution.application.attempt.phase →
          before.execution.application.attempt = next.execution.application.attempt ∧
            next.execution.application.phases = before.execution.application.phases) := by
    intro target targetTrace kept
    induction kept with
    | refl => exact ⟨before, rfl, fun _ => ⟨rfl, rfl⟩⟩
    | @extend source target earlier kept joint legal reached ih =>
        obtain ⟨middle, rfl, previous⟩ := ih
        have realized : target ∈ ((app).transition initial horizon scheduler (some middle)
            joint).support := reached
        obtain ⟨next, rfl, _⟩ := (app).transition_recall_prefix initial horizon scheduler
          middle target joint realized
        have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon
          scheduler initialized (menu.toRawTrace initial horizon scheduler earlier)
        have lower := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
          horizon scheduler before middle prior earlier kept firstOrdered
        have progress := (phaseApplication_namespace_progress runtime leaks).transition initial
          horizon scheduler middle next joint realized ordered
        refine ⟨next, rfl, ?_⟩
        intro finalSame
        have middlePhase : before.execution.application.attempt.phase =
            middle.execution.application.attempt.phase := by omega
        obtain ⟨middleSame, middlePhases⟩ := previous middlePhase
        have finalStep := (public_same_phase_step runtime leaks).transition initial horizon
          scheduler middle next joint realized ordered (middlePhases.symm ▸ publicPhase)
            (middlePhase.symm.trans finalSame)
        exact ⟨middleSame.trans finalStep,
          ((phaseApplication_sameAttempt_controls runtime leaks).transition initial horizon
            scheduler middle next joint realized ordered finalStep).1.trans middlePhases⟩
  obtain ⟨next, equality, result⟩ := along retained
  cases Option.some.inj equality
  exact (result same).1

/-- A counted opening submitted in the currently installed publication block
has that block's actual generation, even after its sender was excluded. -/
theorem submitted_publication_current_attempt [Fintype Player]
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (message : Message Player (CommitAttemptPacket graph))
    (submitted : message ∈ current.execution.network.inputs)
    (coordinate : CommitAttemptEvent graph) (raw : Raw L)
    (proposed : packetProposal? message.payload = some (coordinate, raw))
    (samePhase : coordinate.attempt.phase = current.execution.application.attempt.phase) :
    coordinate.attempt = current.execution.application.attempt := by
  obtain ⟨before, prior, _material, _candidate, retained, _acting, request,
    _opening, _offered, _stamp⟩ :=
    submitted_proposal_callback runtime leaks bounds plan ordered inputs horizon scheduler current
      trace message submitted coordinate raw proposed
  have archived : (coordinate, raw) ∈ archive current.execution.network.inputs :=
    (mem_archive _ _).mpr ⟨message, submitted, proposed⟩
  obtain ⟨payload, _value, publication, _typed⟩ := archive_publication_typed runtime leaks bounds
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler current trace coordinate raw
      archived
  obtain ⟨phase, installed, inside⟩ := request.2.1
  have interval := (phase.mem_events coordinate.event).mp inside
  have publicPhase : phase.kind ≠ .commitment := by
    intro commitment
    have fields := phase.fields coordinate.event interval.1 interval.2
    rw [commitment] at fields
    obtain ⟨owner, actualPayload, binding⟩ := fields
    cases publication.symm.trans binding
  have same := public_prefix_same_attempt runtime leaks
    (PhaseCount.onePacketMenu runtime leaks bounds)
    (inputs.map (PhaseRuntimeState.initial plan))
    (by
      intro state supported
      obtain ⟨input, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_ordered plan input)
    horizon scheduler before current prior trace retained ⟨phase, installed, publicPhase⟩
    ((congrArg CommitAttemptId.phase request.1).symm.trans samePhase)
  exact request.1.trans same

end Vegas.EventGraphRuntime.PhaseProposal
