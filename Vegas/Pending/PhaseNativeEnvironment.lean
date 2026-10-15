/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeInclusion
import Vegas.Pending.ExclusionPublicRecord

/-! # Shared native command draws before physical phase normalization -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)

/-- Current-phase command gates permit every genuinely ready event. -/
theorem commands_allowed_of_ready (state : PhaseRuntimeState graph)
    (ordered : graph.RevealRelaxedOrdered) (frontier : state.Frontier) (live : state.Live)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (event : graph.EventId) (ready : state.current.native.config.cut.Ready event) :
    state.commandAllowed (.executeSample event) = true ∧
      state.commandAllowed (.expire event) = true := by
  obtain ⟨phase, head, member⟩ :=
    state.ready_current_phase ordered frontier live maximal event ready
  change state.phases.head? = some phase at head
  simp only [PhaseRuntimeState.commandAllowed, head, Option.any_some, member, decide_true,
    and_self]

/-- A disallowed physical command is also an inert command in the native graph. -/
theorem native_environment_of_disallowed (state : PhaseRuntimeState graph)
    (ordered : graph.RevealRelaxedOrdered) (frontier : state.Frontier) (live : state.Live)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (chosen : EnvironmentCommand graph) (disallowed : state.commandAllowed chosen = false) :
    environmentStep runtime state.current.native chosen = PMF.pure state.current.native := by
  cases chosen with
  | advanceClock => cases disallowed
  | executeSample event =>
      have notReady : ¬ state.current.native.config.cut.Ready event := by
        intro ready
        have allowed :=
          (commands_allowed_of_ready state ordered frontier live maximal event ready).1
        simp only [allowed, Bool.true_eq_false] at disallowed
      exact environmentStep_executeSample_of_not_ready runtime state.current.native event notReady
  | expire event =>
      have notReady : ¬ state.current.native.config.cut.Ready event := by
        intro ready
        have allowed :=
          (commands_allowed_of_ready state ordered frontier live maximal event ready).2
        simp only [allowed, Bool.true_eq_false] at disallowed
      exact environmentStep_expire_of_not_ready runtime state.current.native event notReady

/-- The physical and native applications share their original native draw;
only the physical member is subsequently normalized. -/
def pairedApplication (state : PhaseRuntimeState graph) (chosen : EnvironmentCommand graph) :
    PMF (State graph × PhaseRuntimeState graph) :=
  if state.commandAllowed chosen then
    (environmentStep runtime state.current.native chosen).map fun native =>
      (native, ({ state with current := state.current.environmentResult chosen native } :
        PhaseRuntimeState graph).normalize)
  else PMF.pure (state.current.native, state)

/-- Exact marginals, clear endpoint agreement, and the pre-normalization public
failure record all follow from the same actual native command sample. -/
theorem pairedApplication_spec (state : PhaseRuntimeState graph)
    (ordered : graph.RevealRelaxedOrdered) (frontier : state.Frontier) (live : state.Live)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) (chosen : EnvironmentCommand graph) :
    (pairedApplication runtime state chosen).map Prod.fst =
        environmentStep runtime state.current.native chosen ∧
      (pairedApplication runtime state chosen).map Prod.snd = state.environment runtime chosen ∧
      (∀ pair ∈ (pairedApplication runtime state chosen).support,
        pair.2.current.excluded = ∅ → pair.1 = pair.2.current.native) ∧
      ∀ pair ∈ (pairedApplication runtime state chosen).support,
        PublicExclusionRecord state.current →
          PublicExclusionRecord (⟨pair.1, pair.2.current.excluded⟩ : RecoveryState graph) := by
  classical
  unfold pairedApplication
  by_cases allowed : state.commandAllowed chosen = true
  · simp only [allowed, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [PMF.map_comp, Function.comp_def]
      exact PMF.map_id _
    · simp only [PhaseRuntimeState.environment, allowed, ↓reduceIte, PMF.map_comp,
        Function.comp_def]
    · intro pair member clear
      obtain ⟨native, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      have same := PhaseRuntimeState.normalize_of_clear
        ({ state with current := state.current.environmentResult chosen native } :
          PhaseRuntimeState graph) clear
      exact (congrArg RecoveryState.native same.1).symm
    · intro pair member valid
      obtain ⟨native, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      have physical := (PhaseRuntimeState.settle_physical state.phases state.generation state.entry
        (state.current.environmentResult chosen native) state.retired).1
      change _ = (state.current.environmentResult chosen native).excluded at physical
      change PublicExclusionRecord
        (⟨native, (PhaseRuntimeState.settle state.phases state.generation state.entry
          (state.current.environmentResult chosen native) state.retired).current.excluded⟩ :
          RecoveryState graph)
      rw [physical]
      exact valid.environmentResult runtime chosen native supported
  · have disallowed : state.commandAllowed chosen = false := Bool.eq_false_iff.mpr allowed
    simp only [disallowed, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [PMF.pure_map,
        native_environment_of_disallowed runtime state ordered frontier live maximal chosen
          disallowed]
    · simp only [PMF.pure_map, PhaseRuntimeState.environment, disallowed, Bool.false_eq_true,
        ↓reduceIte]
    · intro pair member _clear
      cases (PMF.mem_support_pure_iff _ _).mp member
      rfl
    · intro pair member valid
      cases (PMF.mem_support_pure_iff _ _).mp member
      exact valid

end Vegas.EventGraphRuntime.PhaseNativeProjection
