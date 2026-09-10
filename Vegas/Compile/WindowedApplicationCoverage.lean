/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageCoverage
import Vegas.Compile.WindowedSourceSafety

/-! # Field coverage for activation-windowed applications

Activation-relative retiming and genuine expiry handling preserve the generated
image's field-allocation invariant throughout arbitrary policy executions.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
private theorem retimed_instructions_allocated
    (runtime : WindowedApplication P L) (initialFields : Nat)
    (hallocated : ∀ instruction ∈ runtime.image.instructions,
      instruction.AllocatedAt initialFields) (origin : Nat) :
    ∀ instruction ∈ (runtime.atOrigin origin).instructions,
      instruction.AllocatedAt initialFields := by
  exact runtime.image.instructions_allocated_withDeadlines
    (fun address => origin + runtime.windowOf address) initialFields hallocated

theorem handle_memory_covers (runtime : WindowedApplication P L)
    (initialFields : Nat)
    (hallocated : ∀ instruction ∈ runtime.image.instructions,
      instruction.AllocatedAt initialFields)
    (state next : State P L) (message : Message P (ApplicationImage.Payload P L))
    (hcovers : state.base.memory.Covers initialFields)
    (hnext : runtime.handle state message = some next) :
    next.base.memory.Covers initialFields := by
  obtain ⟨activation, base, _, _, hbase, rfl⟩ :=
    runtime.handle_some state next message hnext
  have hraw : (runtime.atOrigin activation.since).handle state.base message = some base :=
    (runtime.atOrigin activation.since).application.withAdmission_handle_some
      (runtime.atOrigin activation.since).admitsMessage
      (runtime.atOrigin activation.since).admitsEnvironment state.base base message hbase
  exact (runtime.atOrigin activation.since).handle_covers initialFields
    (retimed_instructions_allocated runtime initialFields hallocated activation.since)
    state.base base message hcovers hraw

theorem environmentStep_memory_covers (runtime : WindowedApplication P L)
    (initialFields : Nat)
    (hallocated : ∀ instruction ∈ runtime.image.instructions,
      instruction.AllocatedAt initialFields)
    (state next : State P L) (command : ApplicationImage.EnvironmentCommand)
    (hcovers : state.base.memory.Covers initialFields)
    (hnext : next ∈ (runtime.environmentStep state command).support) :
    next.base.memory.Covers initialFields := by
  cases command with
  | advance clock =>
      rw [environmentStep, FinDist.mem_support_pure] at hnext
      subst next
      exact state.base.advance_covers initialFields clock hcovers
  | sample address =>
      simp only [environmentStep, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨base, hbase, rfl⟩ := hnext
      rcases runtime.image.application.withAdmission_environment_support
          runtime.image.admitsMessage runtime.image.admitsEnvironment
          state.base base (.sample address) hbase with rfl | horiginal
      · exact hcovers
      · exact runtime.image.environmentStep_covers initialFields hallocated
          state.base base (.sample address) hcovers horiginal

/-- Memory coverage is invariant under arbitrary supported executions of the
actual activation-windowed interpreter. -/
theorem runPolicies_memory_covers (runtime : WindowedApplication P L)
    (initialFields : Nat)
    (hallocated : ∀ instruction ∈ runtime.image.instructions,
      instruction.AllocatedAt initialFields)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (execution next : runtime.application.PolicyExecution)
    (hcovers : execution.native.application.base.memory.Covers initialFields)
    (hnext : next ∈ (runtime.application.runPolicies players environment schedule
      execution).support) :
    next.native.application.base.memory.Covers initialFields := by
  exact runtime.application.runPolicies_application_invariant
    (fun state => state.base.memory.Covers initialFields)
    (fun state who command h => by cases command; exact state.base.register_covers _ h _ _ _)
    (fun state message next h hnext =>
      runtime.handle_memory_covers initialFields hallocated state next message h hnext)
    (fun state command next h hnext =>
      runtime.environmentStep_memory_covers initialFields hallocated state next command h hnext)
    players environment schedule execution next hcovers hnext

/-- Canonical initialization supplies coverage when the initial done table is
false everywhere. -/
theorem runPolicies_initial_memory_covers (runtime : WindowedApplication P L)
    (initialFields : Nat)
    (hallocated : ∀ instruction ∈ runtime.image.instructions,
      instruction.AllocatedAt initialFields)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P)) (memory : ApplicationImage.Memory P L)
    (hdone : ∀ node, memory.done node = false)
    (next : runtime.application.PolicyExecution)
    (hnext : next ∈ (runtime.application.runPolicies players environment schedule
      (PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (runtime.initial (ApplicationImage.State.initial memory))))).support) :
    next.native.application.base.memory.Covers initialFields := by
  exact runtime.runPolicies_memory_covers initialFields hallocated players environment schedule
    _ next (memory.covers_of_done_false initialFields hdone) hnext

end Vegas.WindowedApplication

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
variable {build : BuildState P L Γ}

/-- A generated activation-windowed application covers every completed event
field in every supported run from canonical public-memory initialization. -/
theorem windowed_runPolicies_memory_covers
    (plan : ApplicationPlan accounted fresh build) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat)
    (players : P → (plan.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (environment : (plan.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (next : (plan.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hnext : next ∈ ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      players environment schedule
      (PolicyExecution.initial (plan.windowed deadlineOf binding choice windowOf).application
        (MessageApplication.State.initial
          (plan.windowed deadlineOf binding choice windowOf).application
          ((plan.windowed deadlineOf binding choice windowOf).initial
            (ApplicationImage.State.initial
              (ApplicationImage.Memory.initial (compileCore prog fresh build).graph)))))).support) :
    next.native.application.base.memory.Covers build.initialFields.length := by
  apply (plan.windowed deadlineOf binding choice windowOf).runPolicies_initial_memory_covers
    build.initialFields.length
    (memory := ApplicationImage.Memory.initial (compileCore prog fresh build).graph)
  · dsimp only [windowed]
    apply ApplicationImage.instructions_allocated_withChoiceTimeouts
    apply ApplicationImage.instructions_allocated_withBindingTimeouts
    exact plan.instructions_allocated deadlineOf
  · intro node
    rfl
  · exact hnext

end Vegas.ApplicationPlan
