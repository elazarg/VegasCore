/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobSafeContinuation
import Vegas.Examples.LateOpeningRuntimeBobInformation
import Interaction.ReactiveRestrictedContinuation

/-! # The Safe continuation is a genuine bounded native deviation

The clock-based quiet, binding and opening policy belongs to the current raw
response menu at every actual decision history. Its finite representation
therefore executes exactly the physical policy, including after arbitrary
earlier raw responses. No extra action or external implementation is added.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeEarlyBobSafeMenu

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobBindingService
  LateOpeningRuntimeBobResponseMenu LateOpeningRuntimeBobSafeContinuation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem binding_available (answer : Answer) (control : app.Control)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some bob)
    (unfinished : bobBindEvent ∉ control.execution.application.config.cut.completed) :
    LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
      (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent
        (.success answer) ∈
      rawMenu.actions bob (control.execution.recall bob) (control.execution.observe app bob) := by
  have count := binding_count_zero control.execution.application unfinished
  have resources := bounded_resources weight nonnegative control trace active
  cases selected : canonicalFreshSlot bob
      (control.execution.observe app bob).application with
  | none =>
    have silent : LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
        (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent
          (.success answer) = ⟨none⟩ := by
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
    have binding : LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
        (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent
          (.success answer) =
        LateOpeningRuntimeService.runtime.reactiveBinding leaks bob bobBindEvent (.range 0 5)
          (.success answer) serial := by
      exact LateOpeningRuntimeService.runtime.canonicalServiceDecision_binding leaks bob
        (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent
          (.range 0 5) rfl rfl rfl serial selected (.success answer)
    rw [binding]
    apply (ReactiveApplication.ResponseMenu.fromSubmissions_mem
      (app := app) (fun _ past view => bounds.submissions
        (ReactiveApplication.ResponseMenu.knownPackets past view)) bob _ _ _).mpr
    change (⟨⟨.commitment bobBindEvent (bob, .prepared serial),
        some ⟨.range 0 5, answer⟩⟩, .none⟩ : WitnessedSubmission nativeGraph) ∈ bounds.submissions _
    rw [bounds.submissions_mem]
    exact ⟨⟨small, binding_values_covered bobBindEvent answer⟩, trivial⟩

theorem answerPolicy_admissible (answer : Answer) :
    rawMenu.Admissible initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) bob (answerPolicy answer) := by
  intro control trace active response supported
  change response ∈ (PMF.pure (if control.execution.application.clock = 3 then
    if bobBindEvent ∈ control.execution.application.publicView.observation.completionOrder then
      LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
        (control.execution.recall bob) (control.execution.observe app bob) bobRevealEvent true
    else LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
        (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent
          (.success answer)
    else ⟨none⟩)).support at supported
  cases (PMF.mem_support_pure_iff _ _).mp supported
  split
  · split
    · exact opening_available weight nonnegative
        LateOpeningRuntimeBobInformation.output_values_covered control trace active
    · rename_i unfinished
      apply binding_available weight nonnegative answer control trace active
      intro completed
      apply unfinished
      exact (control.execution.application.config.history_exact bobBindEvent).mpr completed
  · exact bounds.silent_available LateOpeningRuntimeService.runtime leaks bob _ _

theorem safePolicy_admissible :
    rawMenu.Admissible initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) bob safePolicy :=
  answerPolicy_admissible weight nonnegative safe

def answerFinitePolicy (answer : Answer) :
    (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob :=
  rawMenu.restrictPolicy initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) bob (answerPolicy answer)

def safeFinitePolicy : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob :=
  rawMenu.restrictPolicy initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) bob safePolicy

end Vegas.Examples.LateOpeningRuntimeEarlyBobSafeMenu
