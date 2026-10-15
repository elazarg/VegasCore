/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseFrontier
import Vegas.Pending.PhaseInputNamespace
import Vegas.Pending.PhaseCountProjection
import Vegas.Pending.PhaseServiceProgress

/-! # Authentic current-attempt tokens retain their prerequisites -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseCount

private theorem maskPacket_token_some (view : PhasePublicView graph)
    (packet : WitnessedPacket graph) (event : graph.EventId)
    (attached : (maskPacket view packet).token = some ⟨event⟩) :
    packet.token = some ⟨event⟩ := by
  by_cases excluded : excludedCall view packet.call = true
  · simp [maskPacket, excluded] at attached
  · by_cases allowed : allows view packet.call = true
    · simpa [maskPacket, excluded, allowed] using attached
    · simp [maskPacket, excluded, allowed] at attached

omit [DecidableEq Player] in
private theorem tokenFor_prerequisites (state : State graph) (call : Payload graph)
    (event : graph.EventId) (attached : state.publicView.tokenFor call = some ⟨event⟩) :
    ∀ predecessor ∈ graph.order.predecessors event,
      predecessor ∈ state.config.cut.completed := by
  unfold PublicView.tokenFor at attached
  cases addressed : call.event? graph with
  | none => simp only [addressed, Option.bind_none, reduceCtorEq] at attached
  | some named =>
      rw [addressed, Option.bind_some] at attached
      have issued := (state.publicView.readinessToken?_eq_some_iff named ⟨event⟩).mp attached
      have same : event = named := congrArg ReadinessToken.event issued.1
      subst event
      intro predecessor required
      exact (state.config.history_exact predecessor).mp (issued.2 predecessor required)

/-- Neither masking layer invents authorization: a genuinely emitted token
certifies the native prerequisites at the actual emission configuration. -/
theorem emitted_token_prerequisites (state : PhaseRuntimeState graph) (who : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (material : WitnessedSubmission graph)
    (event : graph.EventId)
    (attached : ((state.submit who material).emit who known material).packet.token = some ⟨event⟩) :
    ∀ predecessor ∈ graph.order.predecessors event,
      predecessor ∈ state.current.native.config.cut.completed := by
  rw [emit_after_submit] at attached
  have original := maskPacket_token_some _ _ _ attached
  exact tokenFor_prerequisites state.current.native material.call.packet event original

end PhaseCount

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- An authentic packet still in the current namespace was already in that
namespace before the genuine environment operation. -/
theorem InputNamespaces.current_before {execution next : (app).Execution}
    (namespaces : InputNamespaces runtime leaks execution) (command : (app).Command)
    (reached : next ∈ (execution.environmentStep app command).support)
    (message : Message Player (CommitAttemptPacket graph))
    (authentic : message ∈ execution.network.inputs)
    (current : message.payload.attempt = next.application.attempt) :
    execution.application.attempt = next.application.attempt := by
  have bounded := namespaces.bounded message authentic
  rw [current] at bounded
  have progress := (phaseApplication_namespace_progress runtime leaks).environmentStep
    execution next command reached namespaces.ordered
  have phase := Nat.le_antisymm progress.2 bounded.2
  have generation := Nat.le_antisymm progress.1 bounded.1
  change (⟨execution.application.attempt.phase,
    execution.application.attempt.generation⟩ : CommitAttemptId) =
      ⟨next.application.attempt.phase, next.application.attempt.generation⟩
  rw [phase, generation]

/-- Prerequisite evidence is scoped to the immutable physical attempt in which
the token was emitted. Retired attempts impose no false rollback monotonicity. -/
def CurrentTokenPrerequisites (execution : (app).Execution) : Prop :=
  ∀ message ∈ execution.network.inputs,
    message.payload.attempt = execution.application.attempt → ∀ event,
      message.payload.packet.token = some ⟨event⟩ →
        ∀ predecessor ∈ graph.order.predecessors event,
          predecessor ∈ execution.application.current.native.config.cut.completed

namespace CurrentTokenPrerequisites

variable {runtime leaks}

private theorem respond {inputs : graph.Inputs} (execution : (app).Execution)
    (valid : execution.application.Invariant inputs)
    (tokens : CurrentTokenPrerequisites runtime leaks execution)
    (who : Player) (action : (app).Action) :
    CurrentTokenPrerequisites runtime leaks (execution.respond app who action) := by
  obtain ⟨transmission⟩ := action
  cases transmission with
  | none => exact tokens
  | some material =>
      let emitted : Message Player (CommitAttemptPacket graph) :=
        ⟨(who, execution.network.nextSerial who), (app).packet
          ((app).submit execution.application who material) who
          (execution.network.known who) material⟩
      have inputsEq : (execution.respond app who ⟨some material⟩).network.inputs =
          List.append execution.network.inputs [emitted] := rfl
      have progress := execution.application.submit_progress who material valid.active
      intro message member current event attached predecessor required
      rw [inputsEq] at member
      rcases List.mem_append.mp member with previous | latest
      · exact progress.completed
          (tokens message previous current event attached predecessor required)
      · have same : message = emitted := List.mem_singleton.mp latest
        subst message
        exact progress.completed (PhaseCount.emitted_token_prerequisites execution.application who
          (execution.network.known who) material event attached predecessor required)

private theorem environment {inputs : graph.Inputs} (execution next : (app).Execution)
    (valid : execution.application.Invariant inputs)
    (namespaces : InputNamespaces runtime leaks execution)
    (tokens : CurrentTokenPrerequisites runtime leaks execution)
    (command : (app).Command) (reached : next ∈ (execution.environmentStep app command).support) :
    CurrentTokenPrerequisites runtime leaks next := by
  intro message member current event attached predecessor required
  have authentic : message ∈ execution.network.inputs := by
    rwa [(app).environmentStep_inputs execution next command reached] at member
  have same := InputNamespaces.current_before runtime leaks namespaces command reached message
    authentic current
  obtain ⟨ticks, progress⟩ := (phaseApplication_serviceProgress runtime leaks).environmentStep
    execution next command reached inputs valid namespaces.ordered same
  exact progress.completed (tokens message authentic (current.trans same.symm) event attached
    predecessor required)

end CurrentTokenPrerequisites

/-- All genuine initialized raw histories supply immutable token provenance,
without a count-cleanliness, ordering, completion or scheduling assumption. -/
theorem currentTokenPrerequisites_history (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    {control : (app).Control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) :
    ∃ input, control.execution.application.Invariant input ∧
      InputNamespaces runtime leaks control.execution ∧
        CurrentTokenPrerequisites runtime leaks control.execution := by
  let predicate := fun execution : (app).Execution => ∃ input,
    execution.application.Invariant input ∧ InputNamespaces runtime leaks execution ∧
      CurrentTokenPrerequisites runtime leaks execution
  have invariant : (app).ServiceInvariant scheduler predicate := by
    constructor
    · intro execution who action before
      obtain ⟨input, valid, namespaces, tokens⟩ := before
      exact ⟨input, (phaseApplication_invariant runtime leaks input).respond execution who action
        valid, namespaces.respond who action,
        CurrentTokenPrerequisites.respond execution valid tokens who action⟩
    · intro execution next command before _ reached
      obtain ⟨input, valid, namespaces, tokens⟩ := before
      exact ⟨input, (phaseApplication_invariant runtime leaks input).environmentStep execution next
        command valid reached, namespaces.environment command reached,
        CurrentTokenPrerequisites.environment execution next valid namespaces tokens command
          reached⟩
  have actual := invariant.history (inputs.map (PhaseRuntimeState.initial plan)) horizon
    (fun state member => by
      obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ member
      refine ⟨input, (PhaseRuntimeState.initial_invariant plan input).1,
        InputNamespaces.initial _ (PhaseRuntimeState.initial_ordered plan input), ?_⟩
      intro message impossible
      exact (List.not_mem_nil impossible).elim) trace
  exact actual

/-- A current authentic authorized packet names a ready event until that event
completes in the same physical attempt. -/
theorem ready_of_current_authentic_token (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    {control : (app).Control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) (message : Message Player (CommitAttemptPacket graph))
    (authentic : message ∈ control.execution.network.inputs)
    (current : message.payload.attempt = control.execution.application.attempt)
    (authorized : message.payload.packet.tokenValid = true) (event : graph.EventId)
    (named : message.payload.packet.call.event? graph = some event)
    (unfinished : event ∉ control.execution.application.current.native.config.cut.completed) :
    control.execution.application.current.native.config.cut.Ready event := by
  obtain ⟨actual, called, attached⟩ := (WitnessedPacket.tokenValid_iff _).mp authorized
  have same : actual = event := Option.some.inj (called.symm.trans named)
  subst actual
  obtain ⟨_, _, _, tokens⟩ :=
    currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler trace
  exact ⟨unfinished, tokens message authentic current event attached⟩

end Vegas.EventGraphRuntime
