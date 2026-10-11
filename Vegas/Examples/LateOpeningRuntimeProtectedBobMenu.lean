/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeProtectedBobPolicy
import Vegas.Examples.LateOpeningRuntimeEarlyBobSafeMenu
import Interaction.ReactiveRestrictedContinuation

/-! # Bounded representation of Bob's existing source-canonical policy

The ready-event policy is represented in the unchanged full native menu at every
legal Bob callback, including callbacks reached after arbitrary earlier traffic.
This is the whole-policy comparator used for protected-ready optimality.
-/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeProtectedBobMenu

open SourceProgram Vegas Vegas.EventGraph Vegas.EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private theorem binding_result_available (result : PublicationResult Answer)
    (control : app.Control)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some bob)
    (unfinished : bobBindEvent ∉ control.execution.application.config.cut.completed) :
    LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
      (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent result ∈
      rawMenu.actions bob (control.execution.recall bob) (control.execution.observe app bob) := by
  have count := LateOpeningRuntimeBobBindingService.binding_count_zero
    control.execution.application unfinished
  have resources := LateOpeningRuntimeBobResponseMenu.bounded_resources weight nonnegative
    control trace active
  cases selected : canonicalFreshSlot bob (control.execution.observe app bob).application with
  | none =>
      have silent : LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
          (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent result =
            ⟨none⟩ := by
        simp only [canonicalServiceDecision, canonicalReactiveDecision,
          show nodeView nativeGraph bobBindEvent = .bind bob (.range 0 5) rfl rfl from rfl,
          selected, Option.map_none]
        rfl
      rw [silent]
      exact bounds.silent_available LateOpeningRuntimeService.runtime leaks bob _ _
  | some serial =>
      have small : serial < bounds.candidateCount := by
        unfold canonicalFreshSlot at selected
        split at selected
        · cases Option.some.inj selected
          change control.execution.application.publicView.bindingCount bob < 26
          rw [count]
          decide
        · exact resources.2 serial selected
      erw [LateOpeningRuntimeService.runtime.canonicalServiceDecision_binding leaks bob
        (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent
          (.range 0 5) rfl rfl rfl serial selected result]
      apply bounds.menu_in_raw LateOpeningRuntimeService.runtime leaks
      erw [← LateOpeningRuntimeService.runtime.reactiveBinding_normal_of_fresh leaks bob
        (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent
          (.range 0 5) result serial
            (canonicalFreshSlot_spec bob (control.execution.observe app bob).application
              serial selected)]
      exact bounds.binding_normalized_available LateOpeningRuntimeService.runtime leaks bob
        (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent
          (.range 0 5) result serial small (fun chosen _ =>
            LateOpeningRuntimeService.binding_values_covered bobBindEvent chosen)

/-- Every source-canonical Bob policy is a genuine whole bounded raw deviation.
Selected bindings have an unfinished event and all six values fit the original
menu; resolutions and silence use the existing bounded resource certificates. -/
theorem canonical_admissible (profile : BehavioralProfile program) :
    rawMenu.Admissible initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) bob
      (serviceCanonicalPolicy setup .sequential deadline leaks profile bob) := by
  intro control trace active response supported
  unfold serviceCanonicalPolicy at supported
  rw [dite_eq_left (show (control.execution.observe app bob).application.who = bob from rfl)]
    at supported
  cases selected : (control.execution.observe app bob).application.publicView.ownTurn? bob with
  | none =>
      rw [selected] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact bounds.silent_available LateOpeningRuntimeService.runtime leaks bob _ _
  | some event =>
      rw [selected] at supported
      dsimp only at supported
      split at supported
      · rename_i owned
        obtain ⟨choice, _, rfl⟩ := PMF.support_map .. ▸ supported
        have publicReady := (PublicView.ownTurn?_spec _ bob event selected).1
        change control.execution.application.publicView.EventReady event at publicReady
        have ready := (control.execution.application.publicView_eventReady event).mp publicReady
        change Fin 3 at event
        fin_cases event
        · change some alice = some bob at owned
          exact False.elim ((by decide : alice ≠ bob) (Option.some.inj owned))
        · change PublicationResult Answer at choice
          exact binding_result_available weight nonnegative choice control trace active ready.1
        · change Bool at choice
          cases choice with
          | false =>
              have silent : LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
                  (control.execution.recall bob) (control.execution.observe app bob)
                    bobRevealEvent false = ⟨none⟩ := by
                rfl
              erw [silent]
              exact bounds.silent_available LateOpeningRuntimeService.runtime leaks bob _ _
          | true =>
              exact LateOpeningRuntimeBobResponseMenu.opening_available weight nonnegative
                LateOpeningRuntimeBobInformation.output_values_covered control trace active
      · cases (PMF.mem_support_pure_iff _ _).mp supported
        exact bounds.silent_available LateOpeningRuntimeService.runtime leaks bob _ _

end Vegas.Examples.LateOpeningRuntimeProtectedBobMenu
