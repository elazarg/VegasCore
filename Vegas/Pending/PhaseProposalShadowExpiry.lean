/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowNormalization
import Vegas.Pending.EventCommandFrame

/-! # Actual expiry laws under supported private binding shadows

Expiry executes source FALSE at a resolution; it does not read or repair a
semantic guard. Its readiness, entered stamp and global clock are retained by
the shadow, so the SAME actual expiry decision is taken on both sides.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Clock advancement leaves semantic and candidate shadows literal. -/
theorem native_advanceClock (memory : BindingShadow graph) (owner : Player)
    (runtime : EventGraphRuntime graph) (state : State graph) :
    environmentStep runtime (memory.native owner state) .advanceClock =
      (environmentStep runtime state .advanceClock).map (memory.native owner) := by
  simp only [environmentStep, PMF.pure_map]
  rfl

/-- A supported shadow has no override at a ready event. Every actual
expiry branch therefore commutes, including false publication completion. -/
theorem native_expire (memory : BindingShadow graph) (owner : Player)
    (runtime : EventGraphRuntime graph) (state : State graph)
    (supported : memory.CompletedAt state.config) (event : graph.EventId) :
    environmentStep runtime (memory.native owner state) (.expire event) =
      (environmentStep runtime state (.expire event)).map (memory.native owner) := by
  classical
  by_cases ready : state.config.cut.Ready event
  · have originalReady : (memory.native owner state).config.cut.Ready event := ready
    cases stamp : state.activatedAt event with
    | none =>
        rw [environmentStep_expire_of_not_activated runtime state event ready stamp,
          environmentStep_expire_of_not_activated runtime (memory.native owner state) event
            originalReady stamp, PMF.pure_map]
    | some entered =>
        by_cases due : runtime.deadline event ≤ state.clock - entered
        · have originalDue : runtime.deadline event ≤
              (memory.native owner state).clock - entered := due
          obtain ⟨noAction, noValue⟩ := supported.ready_none event ready
          cases node : nodeView graph event with
          | bind actor payload outputEq codeEq =>
              rw [environmentStep_expire_bind_eq runtime state event ready entered stamp due
                actor payload outputEq codeEq node,
                environmentStep_expire_bind_eq runtime (memory.native owner state) event
                  originalReady entered stamp originalDue actor payload outputEq codeEq node,
                PMF.pure_map]
              exact congrArg PMF.pure
                (native_complete_unmodified memory owner state event ready noValue
                  noAction _ _).symm
          | resolve actor payload binding checks outputEq codeEq =>
              rw [environmentStep_expire_resolve_eq runtime state event ready entered stamp due
                actor payload binding checks outputEq codeEq node,
                environmentStep_expire_resolve_eq runtime (memory.native owner state) event
                  originalReady entered stamp originalDue actor payload binding checks outputEq
                    codeEq node, PMF.pure_map]
              exact congrArg PMF.pure
                (native_complete_unmodified memory owner state event ready noValue
                  noAction _ _).symm
          | sample payload law outputEq codeEq =>
              rw [environmentStep_expire_sample_eq runtime state event ready entered stamp due
                payload law outputEq codeEq node,
                environmentStep_expire_sample_eq runtime (memory.native owner state) event
                  originalReady entered stamp originalDue payload law outputEq codeEq node,
                PMF.pure_map]
        · have originalDue : ¬ runtime.deadline event ≤
              (memory.native owner state).clock - entered := due
          rw [environmentStep_expire_of_not_due runtime state event ready entered stamp due,
            environmentStep_expire_of_not_due runtime (memory.native owner state) event
              originalReady entered stamp originalDue, PMF.pure_map]
  · have originalReady : ¬ (memory.native owner state).config.cut.Ready event := ready
    rw [environmentStep_expire_of_not_ready runtime state event ready,
      environmentStep_expire_of_not_ready runtime (memory.native owner state) event originalReady,
      PMF.pure_map]

/-- A real supported expiry successor has an actual paired successor after
general phase recovery. This includes first and repeated delivery failures. -/
theorem PhaseStateFrame.environment_expire {memory : BindingShadow graph} {owner : Player}
    {original repaired : PhaseRuntimeState graph} (frame : PhaseStateFrame memory owner
      original repaired) (owned : memory.OwnBindings owner)
    (supported : memory.CompletedAt repaired.current.native.config)
    (runtime : EventGraphRuntime graph) (event : graph.EventId)
    (next : PhaseRuntimeState graph)
    (reached : next ∈ (repaired.environment runtime (.expire event)).support) :
    ∃ (nextMemory : BindingShadow graph) (image : PhaseRuntimeState graph),
      image ∈ (original.environment runtime (.expire event)).support ∧
      nextMemory.OwnBindings owner ∧ nextMemory.candidates = memory.candidates ∧
      PhaseStateFrame nextMemory owner image next ∧
      nextMemory.CompletedAt next.current.native.config := by
  classical
  have allowedEq : original.commandAllowed (.expire event) =
      repaired.commandAllowed (.expire event) := by
    simp only [PhaseRuntimeState.commandAllowed, frame.phases]
  cases allowed : repaired.commandAllowed (.expire event) with
  | false =>
      have leftAllowed := allowedEq.trans allowed
      simp only [PhaseRuntimeState.environment, allowed, Bool.false_eq_true,
        ↓reduceIte, PMF.mem_support_pure_iff] at reached
      subst next
      refine ⟨memory, original, ?_, owned, rfl, frame, supported⟩
      simp only [PhaseRuntimeState.environment, leftAllowed, Bool.false_eq_true,
        ↓reduceIte, PMF.mem_support_pure_iff]
  | true =>
      have leftAllowed := allowedEq.trans allowed
      simp only [PhaseRuntimeState.environment, allowed, ↓reduceIte] at reached
      obtain ⟨native, moved, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      let rightRaw : PhaseRuntimeState graph :=
        { repaired with current := repaired.current.environmentResult (.expire event) native }
      let leftRaw : PhaseRuntimeState graph :=
        { original with
          current :=
            original.current.environmentResult (.expire event) (memory.native owner native) }
      have currentEq : leftRaw.current = memory.recovery owner rightRaw.current := by
        dsimp only [leftRaw, rightRaw]
        rw [frame.current]
        rfl
      have rawFrame : PhaseStateFrame memory owner leftRaw rightRaw :=
        ⟨frame.phases, frame.generation, frame.entry, currentEq, frame.retired⟩
      have rawSupport : memory.CompletedAt rightRaw.current.native.config := by
        intro prior present
        exact environmentStep_completed_subset runtime repaired.current.native native
          (.expire event) moved (supported prior present)
      obtain ⟨nextMemory, nextOwned, candidates, normalized, nextSupport, _refinement⟩ :=
        rawFrame.normalize owned rawSupport
      have originalMoved : memory.native owner native ∈
          (environmentStep runtime original.current.native (.expire event)).support := by
        rw [frame.current]
        change memory.native owner native ∈
          (environmentStep runtime (memory.native owner repaired.current.native)
            (.expire event)).support
        rw [native_expire memory owner runtime repaired.current.native supported event]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨native, moved, rfl⟩
      refine ⟨nextMemory, leftRaw.normalize, ?_, nextOwned, candidates, normalized, nextSupport⟩
      simp only [PhaseRuntimeState.environment, leftAllowed, ↓reduceIte]
      exact (PMF.mem_support_map_iff _ _ _).mpr
        ⟨memory.native owner native, originalMoved, rfl⟩

end Vegas.EventGraphRuntime.BindingShadow
