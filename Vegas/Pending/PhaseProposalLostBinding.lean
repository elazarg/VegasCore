/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSavedExclusionReadback
import Vegas.Pending.PhaseRetiredCompletion
import Vegas.Pending.PhaseReadyBindingDeclaration
import Vegas.Pending.PhaseAcceptedProgress

/-! # Omitted bindings at genuine finished attempts

An absent accepted handle is a physical omission. Accepted unusable private
preparations remain distinct. No clear-attempt restriction is used.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

namespace RecoveryState

omit [DecidableEq Player] in
/-- A finished omitted binding has permanently excluded its owner, independent
of the private typed meaning of any unaccepted prepared candidate. -/
theorem excluded_of_finished_unaccepted_binding
    (state : RecoveryState graph) (phase : RuntimePhase graph)
    (finished : phase.Finished state) (coverage : state.FailureCoverage)
    (event : graph.EventId) (inside : event ∈ phase.events)
    (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (unaccepted : state.native.accepted (.inr event) = none) : owner ∈ state.excluded := by
  have failed := (state.native.publicFailure_iff_accepted_none event owner payload binding
    (finished inside)).mpr unaccepted
  exact coverage.covered event owner (actor?_of_outputLayout_binding graph binding) failed

end RecoveryState

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every original archived attempt classifies all its omitted binding fields
as permanently foreign to any current surviving observer. This consumes an
actual initialized history and retains the full original record. -/
theorem phase_retired_unaccepted_bindings_foreign
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control))
    (record : RetiredCommitAttempt graph)
    (retired : record ∈ control.execution.application.retired) :
    ∃ phase ∈ plan.phases,
      record.attempt.phase = phase.low ∧ phase.kind = .commitment ∧
        ∀ event ∈ phase.events, ∀ owner payload,
          graph.outputLayout event = .binding owner payload →
          record.state.accepted (.inr event) = none →
          owner ∈ control.execution.application.current.excluded ∧
            ∀ observer, observer ∉ control.execution.application.current.excluded →
              owner ≠ observer := by
  obtain ⟨phase, member, low, kind, completed, _receipts, covered⟩ :=
    (phaseRetiredCompletion_history runtime leaks plan inputs horizon scheduler trace).archives
      record retired
  refine ⟨phase, member, low, kind, ?_⟩
  intro event inside owner payload binding absent
  have failed := (record.state.publicFailure_iff_accepted_none event owner payload binding
    (completed inside)).mpr absent
  have excluded := covered event owner (actor?_of_outputLayout_binding graph binding) failed
  refine ⟨excluded, ?_⟩
  intro observer survives same
  exact survives (same ▸ excluded)

section Counted

variable [Fintype Player] (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- An owned binding that is still unaccepted at a genuine retained endpoint
cannot have had a later owned ready callback in this attempt. It applies with
arbitrary inherited exclusions and literal original counted histories. -/
theorem phase_unaccepted_no_later_owned_request
    (scheduler : (app).Scheduler)
    (ordered : graph.RevealRelaxedOrdered)
    (before after : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some after))
    (kept : TracePrefix prior trace)
    (same : before.execution.application.attempt = after.execution.application.attempt)
    (phase : RuntimePhase graph)
    (installed : before.execution.application.phases.head? = some phase)
    (owner : Player) (earlier event : graph.EventId) (priorPayload payload : L.Ty)
    (priorBinding : graph.outputLayout earlier = .binding owner priorPayload)
    (binding : graph.outputLayout event = .binding owner payload)
    (inside : earlier ∈ phase.events)
    (unaccepted : after.execution.application.current.native.accepted (.inr earlier) = none)
    (request : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, event⟩) : ¬ earlier.val < event.val := by
  intro earlierRank
  obtain ⟨candidate, _owned, accepted, _read⟩ := phase_ready_earlier_binding_read runtime leaks
    bounds plan inputs horizon scheduler prior ordered phase installed owner event payload binding
      request.2.2.1 request.2.2.2.2 earlier priorPayload priorBinding inside earlierRank
  have raw := (menu).toRawTrace initial horizon scheduler prior
  have nativeOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler (by
      intro state member
      obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ member
      exact PhaseRuntimeState.initial_ordered plan draw) raw
  have retained := phase_prefix_accepted runtime leaks menu initial horizon scheduler before
    after prior trace kept nativeOrdered same (.inr earlier) candidate accepted
  rw [unaccepted] at retained
  cases retained

/-- The current surviving observer cannot be the owner of an omitted archived
binding. The survival fact is read from its actual request, not assumed from
an independent source witness. -/
theorem phase_retired_unaccepted_binding_ne_of_request
    (scheduler : (app).Scheduler)
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (record : RetiredCommitAttempt graph)
    (retired : record ∈ control.execution.application.retired)
    (observer : Player) (coordinate : CommitAttemptEvent graph)
    (request : control.execution.application.SeedRequest observer coordinate) :
    ∃ phase ∈ plan.phases,
      record.attempt.phase = phase.low ∧ phase.kind = .commitment ∧
        ∀ event ∈ phase.events, ∀ owner payload,
          graph.outputLayout event = .binding owner payload →
          record.state.accepted (.inr event) = none → owner ≠ observer := by
  have raw := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨phase, member, low, kind, foreign⟩ := phase_retired_unaccepted_bindings_foreign runtime
    leaks plan inputs horizon scheduler raw record retired
  refine ⟨phase, member, low, kind, ?_⟩
  intro event inside owner payload binding absent
  exact (foreign event inside owner payload binding absent).2 observer request.2.2.2.2

end Counted

end Vegas.EventGraphRuntime
