/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationDeadlineInvariants
import Vegas.Compile.WindowedApplication

/-! # Native invariants of activation-relative applications

Activation-relative execution changes only deadline metadata before each
ordered handler call.  Completion prefixes and resolved binding dispositions
therefore remain invariants of the original image, even for arbitrary player
policies, environment policies, messages, and schedules.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
private theorem retimed_coveredNodes_nodup
    (runtime : WindowedApplication P L)
    (hnodup : (runtime.image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup)
    (origin : Nat) :
    ((runtime.atOrigin origin).instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup := by
  rw [atOrigin, ApplicationImage.coveredNodes_withDeadlines]
  exact hnodup

omit [DecidableEq P] in
private theorem retimed_instructions_allocated
    (runtime : WindowedApplication P L) (initialFields : Nat)
    (hallocated : ∀ instruction ∈ runtime.image.instructions,
      instruction.AllocatedAt initialFields) (origin : Nat) :
    ∀ instruction ∈ (runtime.atOrigin origin).instructions,
      instruction.AllocatedAt initialFields := by
  exact runtime.image.instructions_allocated_withDeadlines
    (fun address => origin + runtime.windowOf address) initialFields hallocated

/-- A successful windowed handler preserves the completion prefix of the
original, unretimed image. -/
theorem handle_completedPrefix (runtime : WindowedApplication P L)
    (hnodup : (runtime.image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup)
    (state next : State P L) (message : Message P (ApplicationImage.Payload P L))
    (hcompleted : runtime.image.CompletedPrefix state.base.memory)
    (hnext : runtime.handle state message = some next) :
    runtime.image.CompletedPrefix next.base.memory := by
  obtain ⟨activation, base, _, _, hbase, rfl⟩ :=
    runtime.handle_some state next message hnext
  have hretimed : (runtime.atOrigin activation.since).CompletedPrefix
      state.base.memory :=
    (runtime.image.completedPrefix_withDeadlines_iff
      (fun address => activation.since + runtime.windowOf address)
      state.base.memory).2 hcompleted
  have hbaseCompleted : (runtime.atOrigin activation.since).CompletedPrefix
      base.memory :=
    (runtime.atOrigin activation.since).ordered_handle_completedPrefix
      (retimed_coveredNodes_nodup runtime hnodup activation.since)
      state.base base message hretimed hbase
  exact (runtime.image.completedPrefix_withDeadlines_iff
    (fun address => activation.since + runtime.windowOf address)
    base.memory).1 hbaseCompleted

/-- Every supported windowed environment transition preserves the completion
prefix of the original image. -/
theorem environmentStep_completedPrefix (runtime : WindowedApplication P L)
    (hnodup : (runtime.image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup)
    (state next : State P L) (command : ApplicationImage.EnvironmentCommand)
    (hcompleted : runtime.image.CompletedPrefix state.base.memory)
    (hnext : next ∈ (runtime.environmentStep state command).support) :
    runtime.image.CompletedPrefix next.base.memory := by
  cases command with
  | advance clock =>
      rw [environmentStep, FinDist.mem_support_pure] at hnext
      subst next
      exact hcompleted.of_done_eq rfl
  | sample address =>
      simp only [environmentStep, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨base, hbase, rfl⟩ := hnext
      exact runtime.image.ordered_environment_completedPrefix hnodup
        state.base base (.sample address) hcompleted hbase

/-- Completion-prefix safety holds through arbitrary supported policy runs of
the actual activation-relative interpreter. -/
theorem runPolicies_completedPrefix (runtime : WindowedApplication P L)
    (hnodup : (runtime.image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (execution next : runtime.application.PolicyExecution)
    (hcompleted : runtime.image.CompletedPrefix
      execution.native.application.base.memory)
    (hnext : next ∈ (runtime.application.runPolicies players environment schedule
      execution).support) :
    runtime.image.CompletedPrefix next.native.application.base.memory := by
  exact runtime.application.runPolicies_application_invariant
    (fun state => runtime.image.CompletedPrefix state.base.memory)
    (fun state who command h => by cases command; exact h.of_done_eq rfl)
    (fun state message next h hnext =>
      runtime.handle_completedPrefix hnodup state next message h hnext)
    (fun state command next h hnext =>
      runtime.environmentStep_completedPrefix hnodup state next command h hnext)
    players environment schedule execution next hcompleted hnext

/-- A successful windowed handler preserves resolved binding dispositions of
the original image. -/
theorem handle_resolvedBindings (runtime : WindowedApplication P L)
    (initialFields : Nat)
    (hnodup : (runtime.image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : ∀ instruction ∈ runtime.image.instructions,
      instruction.AllocatedAt initialFields)
    (state next : State P L) (message : Message P (ApplicationImage.Payload P L))
    (hresolved : runtime.image.ResolvedBindings state.base)
    (hnext : runtime.handle state message = some next) :
    runtime.image.ResolvedBindings next.base := by
  obtain ⟨activation, base, _, _, hbase, rfl⟩ :=
    runtime.handle_some state next message hnext
  let retimed := runtime.atOrigin activation.since
  have hraw : retimed.application.handle state.base message = some base :=
    retimed.application.withAdmission_handle_some retimed.admitsMessage
      retimed.admitsEnvironment state.base base message hbase
  have hretimed : retimed.ResolvedBindings state.base :=
    (runtime.image.resolvedBindings_withDeadlines_iff
      (fun address => activation.since + runtime.windowOf address) state.base).2 hresolved
  have hbaseResolved : retimed.ResolvedBindings base :=
    ApplicationImage.handle_resolvedBindings retimed initialFields
      (retimed_coveredNodes_nodup runtime hnodup activation.since)
      (retimed_instructions_allocated runtime initialFields hallocated activation.since)
      state.base base message hretimed hraw
  exact (runtime.image.resolvedBindings_withDeadlines_iff
    (fun address => activation.since + runtime.windowOf address) base).1 hbaseResolved

/-- Every supported windowed environment transition preserves resolved
binding dispositions of the original image. -/
theorem environmentStep_resolvedBindings (runtime : WindowedApplication P L)
    (hnodup : (runtime.image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup)
    (state next : State P L) (command : ApplicationImage.EnvironmentCommand)
    (hresolved : runtime.image.ResolvedBindings state.base)
    (hnext : next ∈ (runtime.environmentStep state command).support) :
    runtime.image.ResolvedBindings next.base := by
  cases command with
  | advance clock =>
      rw [environmentStep, FinDist.mem_support_pure] at hnext
      subst next
      exact hresolved
  | sample address =>
      simp only [environmentStep, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨base, hbase, rfl⟩ := hnext
      rcases runtime.image.application.withAdmission_environment_support
          runtime.image.admitsMessage runtime.image.admitsEnvironment
          state.base base (.sample address) hbase with rfl | horiginal
      · exact hresolved
      · exact ApplicationImage.environmentStep_resolvedBindings runtime.image hnodup
          state.base base (.sample address) hresolved horiginal

/-- Resolved-binding safety holds through arbitrary supported policy runs of
the actual activation-relative interpreter. -/
theorem runPolicies_resolvedBindings (runtime : WindowedApplication P L)
    (initialFields : Nat)
    (hnodup : (runtime.image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : ∀ instruction ∈ runtime.image.instructions,
      instruction.AllocatedAt initialFields)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (execution next : runtime.application.PolicyExecution)
    (hresolved : runtime.image.ResolvedBindings execution.native.application.base)
    (hnext : next ∈ (runtime.application.runPolicies players environment schedule
      execution).support) :
    runtime.image.ResolvedBindings next.native.application.base := by
  exact runtime.application.runPolicies_application_invariant
    (fun state => runtime.image.ResolvedBindings state.base)
    (fun state who command h => by cases command; exact h)
    (fun state message next h hnext =>
      runtime.handle_resolvedBindings initialFields hnodup hallocated
        state next message h hnext)
    (fun state command next h hnext =>
      runtime.environmentStep_resolvedBindings hnodup state next command h hnext)
    players environment schedule execution next hresolved hnext

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_completedPrefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_completedPrefix

/-- info: 'Vegas.WindowedApplication.runPolicies_resolvedBindings' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_resolvedBindings
