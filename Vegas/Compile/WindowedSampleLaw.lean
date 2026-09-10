/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationSampleLaw
import Vegas.Compile.WindowedApplication
import Vegas.Compile.ApplicationDeadlineInvariants

/-! # Chance preservation with ordered admission and relative timeouts

Activation metadata and deadline replacement affect admission, but neither the
sample kernel nor its storage footprint. Public message policies and the
environment may observe both the clock and previous samples. The continuation
law remains invariant; the actual marginal follows whenever the selected
sample resolves throughout the unconditioned run.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

theorem runPolicies_sample_continuation (runtime : WindowedApplication P L)
    (code : SampleCode L) (hcode : .sample code ∈ runtime.image.instructions)
    (hcovered : (runtime.image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : (runtime.image.instructions.flatMap ApplicationInstruction.allocatedFields).Nodup)
    (law : FinDist (L.Val code.dist.ty)) (hfixed : ∀ reads, code.dist.eval reads = law)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (execution : runtime.application.PolicyExecution) :
    (runtime.application.runPolicies players environment schedule execution).bind
        (fun next => code.continuation law next.native.application.base.memory) =
      code.continuation law execution.native.application.base.memory := by
  apply runtime.application.runPolicies_application_harmonic
    (fun state => code.continuation law state.base.memory)
  · intro state who command
    cases command
    rfl
  · intro state message next hnext
    obtain ⟨activation, base, _, _, hbase, rfl⟩ := runtime.handle_some state next message hnext
    have hraw := (runtime.atOrigin activation.since).application.withAdmission_handle_some
      (runtime.atOrigin activation.since).admitsMessage
      (runtime.atOrigin activation.since).admitsEnvironment state.base base message hbase
    have hmem : .sample code ∈ (runtime.atOrigin activation.since).instructions := by
      exact List.mem_map.mpr ⟨.sample code, hcode, rfl⟩
    have hnodes : ((runtime.atOrigin activation.since).instructions.flatMap
        ApplicationInstruction.coveredNodes).Nodup := by
      simpa only [atOrigin, ApplicationImage.coveredNodes_withDeadlines] using hcovered
    have hfields : ((runtime.atOrigin activation.since).instructions.flatMap
        ApplicationInstruction.allocatedFields).Nodup := by
      simpa only [atOrigin, ApplicationImage.allocatedFields_withDeadlines] using hallocated
    have hframe := (runtime.atOrigin activation.since).handle_sample_frame
      code hmem hnodes hfields state.base message base hraw
    exact code.continuation_of_frame law _ _ hframe.1 hframe.2
  · intro state command
    cases command with
    | advance clock =>
        simp only [application_advance, FinDist.pure_bind, SampleCode.continuation,
          SampleCode.read?, ApplicationImage.State.advance]
    | sample address =>
        change ((runtime.image.orderedApplication.environmentStep state.base (.sample address)).map
          (runtime.advanceTo state)).bind (fun next => code.continuation law next.base.memory) = _
        rw [FinDist.bind_map]
        change (runtime.image.orderedApplication.environmentStep state.base (.sample address)).bind
          (fun next => code.continuation law next.memory) = _
        by_cases hactive : runtime.image.activeAddress? state.base.memory = some address
        · rw [runtime.image.ordered_sample_eq state.base address hactive]
          exact runtime.image.sample_harmonic code hcode hcovered hallocated law hfixed
            state.base address
        · rw [runtime.image.ordered_sample_inactive state.base address hactive]
          exact FinDist.pure_bind _ _

/-- Arbitrary clock-aware policies cannot bias a fixed emitted chance draw
when it resolves on the whole support. No scheduler non-observation premise
is needed: the environment triggers the kernel but cannot select its draw. -/
theorem runPolicies_sample_law (runtime : WindowedApplication P L)
    (code : SampleCode L) (hcode : .sample code ∈ runtime.image.instructions)
    (hcovered : (runtime.image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : (runtime.image.instructions.flatMap ApplicationInstruction.allocatedFields).Nodup)
    (law : FinDist (L.Val code.dist.ty)) (hfixed : ∀ reads, code.dist.eval reads = law)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (execution : runtime.application.PolicyExecution)
    (hnotDone : execution.native.application.base.memory.done code.node = false)
    (hresolved : ∀ next ∈
        (runtime.application.runPolicies players environment schedule execution).support,
      next.native.application.base.memory.done code.node = true) :
    (runtime.application.runPolicies players environment schedule execution).map
        (fun next => code.read? next.native.application.base.memory) = law.map some := by
  rw [FinDist.map_eq_bind]
  calc
    _ = (runtime.application.runPolicies players environment schedule execution).bind
        (fun next => code.continuation law next.native.application.base.memory) := by
      apply FinDist.bind_congr
      intro next hnext
      simp only [SampleCode.continuation, hresolved next hnext, ↓reduceIte]
    _ = _ := by
      rw [runtime.runPolicies_sample_continuation code hcode hcovered hallocated law hfixed]
      simp only [SampleCode.continuation, hnotDone, Bool.false_eq_true, ↓reduceIte]

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_sample_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_sample_law
