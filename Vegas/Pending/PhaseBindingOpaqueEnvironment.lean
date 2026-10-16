/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingExpiryReplay
import Vegas.Pending.PhaseBindingResponseMemory
import Vegas.Pending.EventCommandFrame

/-! # All-value clear application-command laws while a binding phase is opaque -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem expiry_self (state : RecoveryState graph) (event : graph.EventId) :
    state.environmentResult (.expire event) state.native = state := by
  have impossible : ¬(event ∉ state.native.config.cut.completed ∧
      event ∈ state.native.config.cut.completed) := fun both => both.1 both.2
  simp only [RecoveryState.environmentResult, impossible, ↓reduceIte]

/-- Every actually clear application command in the opaque binding block has
exactly the reconstructed full-state law. A genuine expiry cannot hide a new
public miss in a clear result. Chance commands to binding slots stutter. -/
theorem environment_opaque_memory (runtime : EventGraphRuntime graph)
    (memory : BindingShadow graph) (owner : Player) (owned : memory.OwnBindings owner)
    (state : PhaseRuntimeState graph) (clear : state.current.excluded = ∅)
    (bindingPhase : ∀ phase ∈ state.phases.head?, phase.kind = .commitment)
    (command : EnvironmentCommand graph) (next : PhaseRuntimeState graph)
    (reached : next ∈ ((memory.phased owner state).environment runtime command).support)
    (nextClear : next.current.excluded = ∅) :
    (memory.phased owner state).environment runtime command =
      (state.environment runtime command).map (memory.phased owner) := by
  classical
  cases command with
  | advanceClock =>
      let raw : PhaseRuntimeState graph :=
        { state with current := { state.current with native :=
          { state.current.native with clock := state.current.native.clock + 1 } } }
      simp only [PhaseRuntimeState.environment, PhaseRuntimeState.commandAllowed,
        ite_true, environmentStep, PMF.pure_map]
      change PMF.pure (memory.phased owner raw).normalize =
        PMF.pure (memory.phased owner raw.normalize)
      rw [normalize_phased_of_clear memory owner raw clear]
  | executeSample event =>
      have allowedEq : (memory.phased owner state).commandAllowed (.executeSample event) =
          state.commandAllowed (.executeSample event) := rfl
      cases allowed : state.commandAllowed (.executeSample event) with
      | false =>
          simp only [PhaseRuntimeState.environment, allowedEq, allowed, Bool.false_eq_true,
            ↓reduceIte, PMF.pure_map]
      | true =>
          have actors : ∃ who, graph.actor? event = some who := by
            cases head : state.phases.head? with
            | none =>
                simp only [PhaseRuntimeState.commandAllowed, head, Option.any_none] at allowed
                cases allowed
            | some phase =>
                have inside : event ∈ phase.events := by
                  simpa only [PhaseRuntimeState.commandAllowed, head, Option.any_some,
                    decide_eq_true_eq] using allowed
                obtain ⟨lower, upper⟩ := (phase.mem_events event).mp inside
                have matched := phase.fields event lower upper
                rw [bindingPhase phase head] at matched
                obtain ⟨who, payload, binding⟩ := matched
                cases node : nodeView graph event with
                | sample ty law outputEq codeEq => cases outputEq.symm.trans binding
                | resolve who ty bound checks outputEq codeEq =>
                    cases outputEq.symm.trans binding
                | bind who ty outputEq codeEq =>
                    exact ⟨who, (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
                      (congrArg EventCode.actor codeEq)⟩
          obtain ⟨who, acting⟩ := actors
          have firstLaw := environmentStep_executeSample_of_owned runtime
            (memory.native owner state.current.native) event who acting
          have secondLaw := environmentStep_executeSample_of_owned runtime
            state.current.native event who acting
          simp only [PhaseRuntimeState.environment, allowedEq, allowed, ↓reduceIte]
          change (environmentStep runtime (memory.native owner state.current.native)
            (.executeSample event)).map _ = _
          rw [firstLaw, secondLaw]
          simp only [PMF.pure_map, RecoveryState.environmentResult]
          change PMF.pure (memory.phased owner state).normalize =
            PMF.pure (memory.phased owner state.normalize)
          rw [normalize_phased_of_clear memory owner state clear]
  | expire event =>
      have allowedEq : (memory.phased owner state).commandAllowed (.expire event) =
          state.commandAllowed (.expire event) := rfl
      cases allowed : state.commandAllowed (.expire event) with
      | false =>
          simp only [PhaseRuntimeState.environment, allowedEq, allowed, Bool.false_eq_true,
            ↓reduceIte, PMF.pure_map]
      | true =>
          have beforeAllowed := allowedEq.trans allowed
          have nativeMove : next ∈ ((environmentStep runtime
              (memory.phased owner state).current.native (.expire event)).map fun native =>
                ({ memory.phased owner state with current :=
                  (memory.phased owner state).current.environmentResult (.expire event) native } :
                    PhaseRuntimeState graph).normalize).support := by
            simpa only [PhaseRuntimeState.environment, beforeAllowed, ↓reduceIte] using reached
          obtain ⟨native, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp nativeMove
          have rawClear : ((memory.phased owner state).current.environmentResult
              (.expire event) native).excluded = ∅ := by
            have physical := (PhaseRuntimeState.settle_physical
              (memory.phased owner state).phases (memory.phased owner state).generation
              (memory.phased owner state).entry
              ((memory.phased owner state).current.environmentResult (.expire event) native)
              (memory.phased owner state).retired).1
            exact physical.symm.trans nextClear
          have publics : (memory.phased owner state).current.native.publicView =
              state.current.native.publicView := native_publicView owned _
          have stutters := RecoveryState.expiry_native_stutter
            (memory.phased owner state).current state.current publics event native supported
              rawClear
          simp only [PhaseRuntimeState.environment, beforeAllowed, allowed, ↓reduceIte]
          rw [stutters.1, stutters.2]
          simp only [PMF.pure_map, expiry_self]
          change PMF.pure (memory.phased owner state).normalize =
            PMF.pure (memory.phased owner state.normalize)
          rw [normalize_phased_of_clear memory owner state clear]

end Vegas.EventGraphRuntime.BindingShadow
