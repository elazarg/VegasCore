/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalMeaning
import Vegas.Pending.PhaseSemanticProgress

/-! # Immutable proposal meanings along actual same-attempt prefixes -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A realized prefix retains every immutable native field when its physical
attempt is still current. Intermediate retries are ruled out by namespace
monotonicity, rather than by a cleanliness or strategy-consistency premise. -/
theorem same_attempt_prefix_keeps_store
    (menu : (app).ResponseMenu) (initial : PMF (app).State)
    (initialized : ∀ state ∈ initial.support, state.Ordered) (horizon : Nat)
    (scheduler : (app).Scheduler) (before after : (app).Control)
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (trace : (menu.protocol initial horizon scheduler).Trace (some after))
    (retained : TracePrefix prior trace)
    (same : before.execution.application.attempt = after.execution.application.attempt) :
    KeepsStore before.execution.application.current.native
      after.execution.application.current.native := by
  have firstOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler initialized (menu.toRawTrace initial horizon scheduler prior)
  have along : ∀ {target} {targetTrace : (menu.protocol initial horizon scheduler).Trace target},
      TracePrefix prior targetTrace → ∃ next : (app).Control, target = some next ∧
        (before.execution.application.attempt = next.execution.application.attempt →
          KeepsStore before.execution.application.current.native
            next.execution.application.current.native) := by
    intro target targetTrace kept
    induction kept with
    | refl => exact ⟨before, rfl, fun _ _ _ stored => stored⟩
    | @extend source target earlier kept joint legal reached ih =>
        obtain ⟨middle, rfl, previous⟩ := ih
        have realized : target ∈ ((app).transition initial horizon scheduler (some middle)
            joint).support := reached
        obtain ⟨next, rfl, _⟩ := (app).transition_recall_prefix initial horizon scheduler
          middle target joint realized
        have middleOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
          scheduler initialized (menu.toRawTrace initial horizon scheduler earlier)
        have lower := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
          horizon scheduler before middle prior earlier kept firstOrdered
        have progress := (phaseApplication_namespace_progress runtime leaks).transition initial
          horizon scheduler middle next joint realized middleOrdered
        refine ⟨next, rfl, ?_⟩
        intro finalSame
        have intermediate : before.execution.application.attempt =
            middle.execution.application.attempt := by
          have generation := congrArg CommitAttemptId.generation finalSame
          have phase := congrArg CommitAttemptId.phase finalSame
          cases first : before.execution.application.attempt with
          | mk firstPhase firstGeneration =>
              cases second : middle.execution.application.attempt with
              | mk secondPhase secondGeneration =>
                  simp only [first, second] at lower progress generation phase ⊢
                  congr 1 <;> omega
        have last := ((PhaseRuntimeState.semantic_extension runtime leaks).transition initial
          horizon scheduler middle next joint realized middleOrdered
            (intermediate.symm.trans finalSame)).1
        exact fun field value stored => last field value
          (previous intermediate field value stored)
  obtain ⟨next, equality, result⟩ := along retained
  cases Option.some.inj equality
  exact result same

omit [DecidableEq Player] in
/-- Immutable field retention also preserves the value read through its typed
reference, including binding successes retained at source replay boundaries. -/
theorem kept_reference {before after : EventGraphRuntime.State graph}
    (kept : KeepsStore before after) {kind : EventField Player L}
    (reference : FieldRef graph.layout kind) (value : kind.Value)
    (stored : reference.get? before.config.store = some value) :
    reference.get? after.config.store = some value := by
  rcases reference with ⟨field, typed⟩
  cases typed
  exact kept field value stored

/-- Before its publication attempt is consumed, a submitted counted proposal
still reads its original successful binding through the event's resolve node.
The publication itself may already have failed or been rejected. -/
theorem submitted_proposal_current_binding_meaning [Fintype Player]
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (message : Message Player (CommitAttemptPacket graph))
    (submitted : message ∈ current.execution.network.inputs)
    (coordinate : CommitAttemptEvent graph) (raw : Raw L)
    (proposed : packetProposal? message.payload = some (coordinate, raw))
    (sameAttempt : coordinate.attempt = current.execution.application.attempt)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout coordinate.event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes coordinate.event) =
      .resolve owner payload binding checks) :
    ∃ value : L.Val payload, raw = ⟨payload, value⟩ ∧
      binding.get? current.execution.application.current.native.config.store =
        some (.success value) := by
  obtain ⟨before, prior, actualOwner, actualPayload, actualBinding, actualChecks,
    actualOutput, actualCode, value, retained, _sender, _acting, request,
    _node, typed, stored⟩ :=
    submitted_proposal_binding_meaning runtime leaks bounds plan ordered inputs horizon scheduler
      current trace message submitted coordinate raw proposed
  have samePayload := EventField.publication.inj (actualOutput.symm.trans outputEq)
  subst actualPayload
  cases actualCode.symm.trans codeEq
  have kept := same_attempt_prefix_keeps_store runtime leaks
    (PhaseCount.onePacketMenu runtime leaks bounds)
    (inputs.map (PhaseRuntimeState.initial plan))
    (by
      intro state supported
      obtain ⟨input, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_ordered plan input)
    horizon scheduler before current prior trace retained (request.1.symm.trans sameAttempt)
  exact ⟨value, typed, kept_reference kept binding (.success value) stored⟩

end Vegas.EventGraphRuntime.PhaseProposal
