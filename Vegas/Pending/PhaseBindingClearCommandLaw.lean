/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingOpaqueEnvironment
import Vegas.Pending.PhaseBindingCountedIncludeMemory

/-! # Exact clear-restricted command laws under all-value binding reconstruction -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Clear support on the actual unmodified side suffices for the complete
command-law reconstruction. Genuine binding expiry is ruled out by its actual
public exclusion, rather than an assumed replay or nonexpiry condition. -/
theorem environment_opaque_memory_of_clear_right (runtime : EventGraphRuntime graph)
    (memory : BindingShadow graph) (owner : Player) (owned : memory.OwnBindings owner)
    (state : PhaseRuntimeState graph) (clear : state.current.excluded = ∅)
    (bindingPhase : ∀ phase ∈ state.phases.head?, phase.kind = .commitment)
    (command : EnvironmentCommand graph) (next : PhaseRuntimeState graph)
    (reached : next ∈ (state.environment runtime command).support)
    (nextClear : next.current.excluded = ∅) :
    (memory.phased owner state).environment runtime command =
      (state.environment runtime command).map (memory.phased owner) := by
  classical
  have expirySelf (current : RecoveryState graph) (event : graph.EventId) :
      current.environmentResult (.expire event) current.native = current := by
    have impossible : ¬(event ∉ current.native.config.cut.completed ∧
        event ∈ current.native.config.cut.completed) := fun both => both.1 both.2
    simp only [RecoveryState.environmentResult, impossible, ↓reduceIte]
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
              state.current.native (.expire event)).map fun native =>
                ({ state with current :=
                  state.current.environmentResult (.expire event) native } :
                    PhaseRuntimeState graph).normalize).support := by
            simpa only [PhaseRuntimeState.environment, allowed, ↓reduceIte] using reached
          obtain ⟨native, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp nativeMove
          have rawClear : (state.current.environmentResult
              (.expire event) native).excluded = ∅ := by
            have physical := (PhaseRuntimeState.settle_physical
              state.phases state.generation state.entry
              (state.current.environmentResult (.expire event) native) state.retired).1
            exact physical.symm.trans nextClear
          have publics : (memory.phased owner state).current.native.publicView =
              state.current.native.publicView := native_publicView owned _
          have stutters := RecoveryState.expiry_native_stutter
            state.current (memory.phased owner state).current publics.symm event native supported
              rawClear
          simp only [PhaseRuntimeState.environment, beforeAllowed, allowed, ↓reduceIte]
          rw [stutters.2, stutters.1]
          simp only [PMF.pure_map, expirySelf]
          change PMF.pure (memory.phased owner state).normalize =
            PMF.pure (memory.phased owner state.normalize)
          rw [normalize_phased_of_clear memory owner state clear]


/-- After mapping a first exclusion to the absent branch, the original command
laws agree globally. This is a projection of the actual runtime law, retaining
the original clear states and making no through-reset shadow claim. -/
theorem environment_clear_observation_law (runtime : EventGraphRuntime graph)
    (memory : BindingShadow graph) (owner : Player) (owned : memory.OwnBindings owner)
    (state : PhaseRuntimeState graph) (clear : state.current.excluded = ∅)
    (opaquePhase : ∀ phase ∈ state.phases.head?, phase.kind = .commitment)
    (command : EnvironmentCommand graph) :
    (((memory.phased owner state).environment runtime command).map fun next =>
      if next.current.excluded = ∅ then some next else none) =
      ((state.environment runtime command).map fun next =>
        if next.current.excluded = ∅ then some (memory.phased owner next) else none) := by
  classical
  by_cases survives : ∃ next ∈ ((memory.phased owner state).environment runtime command).support,
      next.current.excluded = ∅
  · obtain ⟨next, supported, nextClear⟩ := survives
    rw [environment_opaque_memory runtime memory owner owned state clear opaquePhase command next
      supported nextClear, PMF.map_comp]
    rfl
  · have noRight : ∀ next ∈ (state.environment runtime command).support,
        next.current.excluded ≠ ∅ := by
      intro next supported nextClear
      have exactLaw := environment_opaque_memory_of_clear_right runtime memory owner owned state
        clear opaquePhase command next supported nextClear
      apply survives
      refine ⟨memory.phased owner next, ?_, nextClear⟩
      rw [exactLaw]
      exact (PMF.mem_support_map_iff ..).mpr ⟨next, supported, rfl⟩
    have firstNone : (((memory.phased owner state).environment runtime command).map fun next =>
        if next.current.excluded = ∅ then some next else none) = PMF.pure none := by
      rw [← pmf_map_fun_const ((memory.phased owner state).environment runtime command) none]
      apply map_congr_on_support
      intro next supported
      exact ite_eq_right (fun nextClear => survives ⟨next, supported, nextClear⟩)
    rw [firstNone]
    symm
    rw [← pmf_map_fun_const (state.environment runtime command) none]
    apply map_congr_on_support
    intro next supported
    exact ite_eq_right (noRight next supported)


/-- An accepted typed failure does not create a public omission. Even the
last binding's real clean normalization preserves the clear excluded set. -/
theorem handled_commitmentPhase_clear (runtime : EventGraphRuntime graph)
    (state next : PhaseRuntimeState graph) (clear : state.current.excluded = ∅)
    (opaquePhase : ∀ phase ∈ state.phases.head?, phase.kind = .commitment)
    (message : Message Player (CommitAttemptPacket graph))
    (accepted : state.handle runtime message = some next) :
    next.current.excluded = ∅ := by
  obtain ⟨event, candidate, call⟩ := accepted_call_in_commitment runtime state next opaquePhase
    message accepted
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · obtain ⟨native, _handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
    exact (PhaseRuntimeState.settle_physical state.phases state.generation state.entry
      (state.current.inclusionResult message.payload.packet.call native) state.retired).1.trans
        (by simpa only [call, RecoveryState.inclusionResult] using clear)
  · cases accepted

/-- Every include command in the current commitment phase preserves public
clearance; rejected, stale, absent and accepted-failure packets are included. -/
theorem include_commitmentPhase_clear (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (physical : (phaseApplication runtime leaks).Execution)
    (clear : physical.application.current.excluded = ∅)
    (opaquePhase : ∀ phase ∈ physical.application.phases.head?, phase.kind = .commitment)
    (id : MessageId Player) :
    (physical.includePending (phaseApplication runtime leaks) id).application.current.excluded =
      ∅ := by
  cases found : physical.network.lookup id with
  | none =>
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found] using clear
  | some message =>
      cases handled : physical.application.handle runtime message with
      | none =>
          simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found, show (phaseApplication runtime leaks).handle physical.application message = none
              from handled, Option.getD_none] using clear
      | some next =>
          have nextClear := handled_commitmentPhase_clear runtime physical.application next clear
            opaquePhase message handled
          simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found, show (phaseApplication runtime leaks).handle physical.application message =
              some next from handled, Option.getD_some] using nextClear

end Vegas.EventGraphRuntime.BindingShadow
