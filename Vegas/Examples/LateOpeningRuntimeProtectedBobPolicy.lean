/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingService
import Vegas.Game.SourceServiceCanonicalPolicy

/-! # Canonical source decisions at native Bob callbacks

The existing source policy realizes the genuine typed binding and TRUE opening
at ready native callbacks. Once both Bob events settle, it remains silent even
at another callback with the same public clock. These are operational policy
identities; they do not assert optimality or an equilibrium.
-/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeProtectedBobPolicy

open Interaction SourceProgram Vegas Vegas.EventGraph Vegas.EventGraphRuntime
open LateOpeningRuntimeSource LateOpeningRuntimeService

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private theorem own_turn_of_ready (execution : app.Execution) (event : nativeGraph.EventId)
    (ready : execution.application.config.cut.Ready event)
    (owned : nativeGraph.actor? event = some bob) :
    execution.application.publicView.ownTurn? bob = some event := by
  apply PublicView.ownTurn?_of_ownTurn
  apply State.ownTurn_of_ready _
    (setup.eventGraph.sequentialize_barrierOrdered.revealRelaxedOrdered) bob event
  · exact (execution.application.publicView_eventReady event).mpr ready
  · exact owned

private theorem compiled_binding (answer : Answer)
    (observation : (toEventGraph program).PlayerObservation bob)
    (available : (observation.store (.inr aliceEvent)).isSome) :
    compileEventProfile program (constantProfile true answer true) bob bobBindEvent rfl
        observation = PMF.pure (PublicationResult.success answer) := by
  simp only [program, bobBindEvent, compileEventProfile, compileEventPolicy,
    constantProfile, compilePolicyTable, Fin.cases, Fin.induction, Fin.induction.go,
    Fin.zero_eta, Fin.isValue, dite_true, eq_mpr_eq_cast, cast_eq]
  simp only [initialCtx, withMode_eventCount, Fin.mk_one, Fin.isValue, decodeObservation?,
    FieldRef.get?, List.length_cons, List.length_nil, Nat.reduceAdd, outputRef,
    ContextRefs.initial, ContextRefs.cons, cast_eq, ContextRefs.tail, zero_ne_one,
    dite_false, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  cases head : observation.store (.inr aliceEvent) with
  | none => rw [head] at available; cases available
  | some published =>
    erw [head]
    rfl

/-- The existing canonical source policy realizes the actual early typed binding,
using Bob's genuine fresh resources; no new native policy is introduced. -/
theorem canonical_binding (answer : Answer) (remaining : Nat) (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining, some bob, execution⟩))
    (quiet : LateOpeningRuntimeBobBindingService.SilentRecall execution)
    (ready : execution.application.config.cut.Ready bobBindEvent) :
    serviceCanonicalPolicy setup .sequential LateOpeningRuntimeService.deadline leaks
        (constantProfile true answer true) bob (execution.recall bob) (execution.observe app bob) =
      PMF.pure (LateOpeningRuntimeBobSuffix.binding answer) := by
  erw [sourceServiceCanonicalPolicy_at_event setup leaks (constantProfile true answer true) bob
    execution bobBindEvent (own_turn_of_ready execution bobBindEvent ready rfl) rfl]
  have available : (execution.application.config.store (.inr aliceEvent)).isSome :=
    (execution.application.config.output_available aliceEvent).mpr (ready.2 (by decide))
  have visible : nativeGraph.fieldVisibleTo bob (.inr aliceEvent) := by decide
  have law := compiled_binding answer
    (setup.eventGraph.fromModeObservation .sequential bob
      ((serviceGraph setup .sequential).playerObserve bob execution.application.config))
    (by simpa only [EventGraph.fromModeObservation, EventGraph.playerObserve,
      EventGraph.playerStore_of_visible _ _ _ _ visible] using available)
  erw [law, PMF.pure_map]
  congr 1
  exact LateOpeningRuntimeBobBindingService.canonical_binding weight nonnegative
    ⟨remaining, some bob, execution⟩ trace quiet ready answer

/-- At the actual ready opening, the same source comparator selects the genuine
canonical TRUE disclosure. -/
theorem canonical_opening (answer : Answer) (execution : app.Execution)
    (ready : execution.application.config.cut.Ready bobRevealEvent) :
    serviceCanonicalPolicy setup .sequential LateOpeningRuntimeService.deadline leaks
        (constantProfile true answer true) bob (execution.recall bob) (execution.observe app bob) =
      PMF.pure (LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
        (execution.recall bob) (execution.observe app bob) bobRevealEvent true) := by
  erw [sourceServiceCanonicalPolicy_at_event setup leaks (constantProfile true answer true) bob
    execution bobRevealEvent (own_turn_of_ready execution bobRevealEvent ready rfl) rfl]
  simp only [setup, program, bobRevealEvent, withMode_eventCount, compileEventProfile,
    compileEventPolicy, constantProfile, compilePolicyTable, Fin.cases, Fin.induction,
    Fin.induction.go, Fin.zero_eta, Fin.isValue, dite_true, Fin.succ_zero_eq_one,
    eq_mpr_eq_cast, cast_eq]
  split <;> rw [PMF.pure_map] <;> rfl

/-- After both Bob events settle, the existing source policy emits nothing,
including the optional second callback at the same public clock. -/
theorem canonical_silent_after_completed (answer : Answer) (execution : app.Execution)
    (bound : bobBindEvent ∈ execution.application.config.cut.completed)
    (opened : bobRevealEvent ∈ execution.application.config.cut.completed) :
    serviceCanonicalPolicy setup .sequential LateOpeningRuntimeService.deadline leaks
        (constantProfile true answer true) bob (execution.recall bob) (execution.observe app bob) =
      PMF.pure ⟨none⟩ := by
  have idle : execution.application.publicView.Idle bob := by
    intro event ready
    have physical := (execution.application.publicView_eventReady event).mp ready
    fin_cases event
    · decide
    · exact False.elim (physical.1 bound)
    · exact False.elim (physical.1 opened)
  have turn := execution.application.publicView.ownTurn?_eq_none bob idle
  unfold serviceCanonicalPolicy
  erw [dite_eq_left (show (execution.observe app bob).application.who = bob from rfl)]
  erw [turn]

end Vegas.Examples.LateOpeningRuntimeProtectedBobPolicy
