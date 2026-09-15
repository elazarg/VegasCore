/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageContinuationWire
import Vegas.Graph.MessageService
import GameTheoryExtensions.Math.Probability.FinDist

/-! # Continuation laws for reserved service inclusion -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- A reserved `includeLatest` slot is an ordinary deterministic wire
invocation, so it preserves the initialized compiled continuation law. The
complete plan is retained when selecting the current environment command. -/
theorem continuationAt_initialized_includeLatest
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ)
    (unique : (Γ.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (initialEnvironment : runtime.application.EnvironmentPolicy)
    (initialSchedule : List (@MessageApplication.Invocation Player))
    (execution : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies
      (runtime.compileProfile whole profile) initialEnvironment initialSchedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (plan : List (ServiceInstruction Player))
    (wire : runtime.application.WirePolicy) (owner : Player)
    (slot : (plan.filterMap
      ServiceInstruction.environmentSlot)[execution.environmentHistory.length]? =
      some (ServiceInstruction.includeLatest owner)) :
    let follows := runtime.runPolicies_follows whole 0 (runtime.compileProfile whole profile)
      initialEnvironment initialSchedule _ execution (State.initial_follows whole input) reached
    runtime.continuationAt whole profile execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke (runtime.compileProfile whole profile)
        (runtime.serviceEnvironment plan wire) execution .environment).bindOnSupport
        fun after supported => runtime.continuationAt whole profile after.principalHistory
          after.native.application
          (runtime.invoke_follows whole 0 (runtime.compileProfile whole profile)
            (runtime.serviceEnvironment plan wire) .environment execution after follows
            supported) := by
  let currentView := MessageApplication.State.environmentView runtime.application execution.native
  let reserved : runtime.application.WirePolicy := fun _ view =>
    match runtime.application.latestSubmissionCommand owner view with
    | .«include» id => FinDist.pure (.«include» id)
    | _ => FinDist.pure .wait
  have kernelEq : runtime.serviceEnvironment plan wire execution.environmentHistory currentView =
      runtime.application.wireEnvironment reserved execution.environmentHistory currentView := by
    simp only [serviceEnvironment, slot]
    rcases runtime.application.latestSubmissionCommand_cases owner currentView with
      wait | ⟨id, included⟩
    · simp [reserved, MessageApplication.wireEnvironment, wait,
        WireCommand.toEnvironmentCommand]
    · simp [reserved, MessageApplication.wireEnvironment, included,
        WireCommand.toEnvironmentCommand]
  have invokeEq : runtime.application.invoke (runtime.compileProfile whole profile)
      (runtime.serviceEnvironment plan wire) execution .environment =
      runtime.application.invoke (runtime.compileProfile whole profile)
        (runtime.application.wireEnvironment reserved) execution .environment := by
    simp only [MessageApplication.invoke]
    rw [kernelEq]
  have law := runtime.continuationAt_initialized_wire whole profile input unique discipline
    initialEnvironment initialSchedule execution reached reserved
  let serviceStep := runtime.application.invoke (runtime.compileProfile whole profile)
    (runtime.serviceEnvironment plan wire) execution .environment
  let wireStep := runtime.application.invoke (runtime.compileProfile whole profile)
    (runtime.application.wireEnvironment reserved) execution .environment
  have residualEq : serviceStep.bindOnSupport (fun after supported =>
      runtime.continuationAt whole profile after.principalHistory after.native.application
        (runtime.invoke_follows whole 0 (runtime.compileProfile whole profile)
          (runtime.serviceEnvironment plan wire) .environment execution after
          (runtime.runPolicies_follows whole 0 (runtime.compileProfile whole profile)
            initialEnvironment initialSchedule _ execution (State.initial_follows whole input)
            reached) supported)) =
      wireStep.bindOnSupport (fun after supported =>
        runtime.continuationAt whole profile after.principalHistory after.native.application
          (runtime.invoke_follows whole 0 (runtime.compileProfile whole profile)
            (runtime.application.wireEnvironment reserved) .environment execution after
            (runtime.runPolicies_follows whole 0 (runtime.compileProfile whole profile)
              initialEnvironment initialSchedule _ execution (State.initial_follows whole input)
              reached) supported)) := by
    apply FinDist.bindOnSupport_congr_measure invokeEq
    intro after serviceSupported wireSupported
    congr
  exact law.trans residualEq.symm

end Vegas.GraphRuntime
