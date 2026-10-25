/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseServiceProjection
import Vegas.Pending.PhaseClearMetadata
import Vegas.Pending.PhaseFrontier
import Vegas.Pending.PhaseInputNamespace

/-! # Protected inclusion on actual clear singleton counted prefixes

Signed phase origins, namespace bounds and the semantic frontier identify the
current attempt of every unfinished input. The original native sole-packet
guarantee then follows from the existing physical service condition.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph) (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks

/-- Every still-unfinished signed input has the current attempt at an actual
clear singleton counted prefix; arbitrary observation rules are allowed. -/
theorem clear_unfinished_input_attempt (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (singleton : ∀ phase ∈ plan.phases, phase.high = phase.low + 1)
    (clear : control.execution.application.current.excluded = ∅)
    (message : Message Player (CommitAttemptPacket graph))
    (present : message ∈ control.execution.network.inputs)
    (event : graph.EventId) (named : message.payload.packet.call.event? graph = some event)
    (unfinished : event ∉ control.execution.application.current.native.config.cut.completed) :
    message.payload.attempt = control.execution.application.attempt := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let rawTrace := (onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler trace
  have namespaces := inputNamespaces_history runtime leaks initial
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_ordered plan draw) horizon scheduler rawTrace
  have frontier := (phaseApplication_frontier runtime leaks).history initial horizon scheduler
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_frontier plan draw) rawTrace
  have zero := (phaseClearMetadata_history runtime leaks plan inputs horizon scheduler
    rawTrace clear).1
  obtain ⟨phase, member, actual, addressed, inside, phaseAddress⟩ :=
    packetPhaseOrigins_history runtime leaks plan bounds inputs horizon scheduler trace
      message present
  have same : actual = event := Option.some.inj (addressed.symm.trans named)
  subst actual
  have packetRank : message.payload.attempt.phase = event.val := by
    have width := singleton phase member
    have interval := (phase.mem_events event).mp inside
    omega
  have upper : control.execution.application.attempt.phase ≤ event.val := by
    cases phases : control.execution.application.phases with
    | nil =>
        have terminal := frontier.terminal phases
        exact (unfinished ((Finset.eq_univ_iff_forall.mp terminal) event)).elim
    | cons current remaining =>
        have positioned := frontier.positioned
        rw [phases] at positioned
        have lower : current.low ≤ event.val := by
          by_contra before
          exact unfinished (positioned.2.1 event (by omega))
        simpa only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
          Option.getD_some] using lower
  have phaseEq : message.payload.attempt.phase = control.execution.application.attempt.phase :=
    le_antisymm (namespaces.bounded message present).2 (by omega)
  have generationEq : message.payload.attempt.generation =
      control.execution.application.attempt.generation := by
    have lower := (namespaces.bounded message present).1
    change message.payload.attempt.generation ≤ control.execution.application.generation at lower
    change message.payload.attempt.generation = control.execution.application.generation
    omega
  exact congrArg₂ CommitAttemptId.mk phaseEq generationEq

end Vegas.EventGraphRuntime.PhaseCount

namespace Vegas.EventGraphRuntime.PhaseService

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph) (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks

/-- The actual all-history phase inclusion contract supplies the native fixed
execution condition at every clear singleton counted prefix. This is not a
claim that projected executions exhaust all legal native histories. -/
theorem ProtectedInclusion.clear_native_onePacket
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (bound : graph.EventId → Nat)
    (inclusion : ProtectedInclusion runtime leaks
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler bound)
    (singleton : ∀ phase ∈ plan.phases, phase.high = phase.low + 1)
    {control : (app).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) :
    Vegas.EventGraphRuntime.ProtectedInclusionAt runtime
      (PhaseNativeProjection.nativeLeaks leaks plan)
      (PhaseNativeProjection.execution runtime leaks plan control.execution) bound := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler trace
  apply ProtectedInclusionAt.nativeProjection runtime leaks plan control.execution bound
    (inclusion control rawTrace)
  intro event owner _acting earlier later entry message recalled sent _sender named _ready
    unfinished
  have inputRecall := (app).history_inputRecall initial horizon scheduler rawTrace
  have output : message ∈ (app).outputs (control.execution.recall owner) := by
    apply List.mem_filterMap.mpr
    refine ⟨entry, ?_, sent⟩
    rw [recalled]
    exact List.mem_append_right _ List.mem_cons_self
  have present : message ∈ control.execution.network.inputs := by
    rw [← inputRecall owner] at output
    exact (List.mem_filter.mp output).1
  exact PhaseCount.clear_unfinished_input_attempt runtime leaks plan bounds inputs horizon
    scheduler trace singleton clear message present event named unfinished

end Vegas.EventGraphRuntime.PhaseService
