/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeServiceContract
import Vegas.Pending.ReactiveFiniteCompiler
import Vegas.Pending.ReactiveCanonicalMenu

/-! # Canonical Bob responses in the actual bounded raw menu

Accepted handles and available preparation serials remain within the fixed
native bounds at every actual decision history. In particular, a canonical
opening is an available raw response at any Bob callback, including callbacks
produced by earlier deviations. Coverage is distinct from readiness, timely
delivery and acceptance.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobResponseMenu

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService

private theorem initial_law_eq :
    (setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph)) = initial := by
  rw [PMF.map_comp]
  rfl

theorem bounded_resources (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some bob) :
    (∀ field candidate,
      (control.execution.observe app bob).application.publicView.accepted field = some candidate →
        bounds.AllowsHandle candidate) ∧
    (∀ serial, reactiveFreshSlot (control.execution.observe app bob).application = some serial →
      serial < bounds.candidateCount) := by
  have inputTrace : (rawMenu.protocol
      ((setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := nativeGraph)))
      LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control) := by
    rwa [initial_law_eq]
  have handles := bounds.executionHandles_raw_history LateOpeningRuntimeService.runtime leaks
    (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) inputTrace
  obtain ⟨serial, small, selected⟩ :=
    LateOpeningRuntimeService.runtime.reactiveFreshSlot_lt_horizon leaks
      (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) control
      (rawMenu.toRawTrace _ _ _ inputTrace) bob active
  refine ⟨fun field candidate found => handles.1 field candidate found, ?_⟩
  intro chosen found
  have same := Option.some.inj (found.symm.trans selected)
  change chosen < 26
  change serial < 26 at small
  omega

/-- Availability holds even when the canonical response will be silent or
rejected. Service and payoff claims require separate operational premises. -/
theorem opening_available (weight : ℝ) (nonnegative : 0 ≤ weight)
    (values : bounds.CoversOutputValues) (control : app.Control)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some bob) :
    LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
      (control.execution.recall bob) (control.execution.observe app bob) bobRevealEvent true ∈
        rawMenu.actions bob (control.execution.recall bob) (control.execution.observe app bob) := by
  obtain ⟨handles, fresh⟩ := bounded_resources weight nonnegative control trace active
  apply bounds.menu_in_raw LateOpeningRuntimeService.runtime leaks
  apply bounds.canonicalServiceDecision_available LateOpeningRuntimeService.runtime leaks
  rw [LateOpeningRuntimeService.runtime.canonicalReactiveDecision_eq_of_not_bind leaks bob
    bobRevealEvent true _ (by
      intro owner payload outputEq _codeEq _same
      have wrong : (EventField.publication (.range 0 5) : EventField Player simpleExpr) =
          .binding owner payload := outputEq
      cases wrong)]
  exact bounds.reactiveDecision_available LateOpeningRuntimeService.runtime leaks bob
    (control.execution.recall bob) (control.execution.observe app bob) values handles fresh
      bobRevealEvent true

end Vegas.Examples.LateOpeningRuntimeBobResponseMenu
