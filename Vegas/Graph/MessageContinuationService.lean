/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageContinuationWire
import Vegas.Graph.MessageContinuationClock
import Vegas.Graph.MessageService
import GameTheoryExtensions.Math.Probability.FinDist

/-! # Continuation laws for reserved service inclusion -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

namespace State

/-- The current typed graph suffix is a chance node. This deliberately records
all dependent state fields, allowing service safety results to expose a sample
case without constructing a `Prefix` witness themselves. -/
def IsSample (state : State Player L Δ) : Prop :=
  ∃ (Γ : VCtx Player L) (name : VarId) (payload : L.Ty)
      (fresh : name ∉ Γ.map Prod.fst) (law : PublicDist (L := L) Γ payload)
      (tail : Graph Player L ((name, .pub payload) :: Γ) Δ)
      (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
      (candidates : CommitmentCandidates Player Slot (Raw L)) (pc clock enteredAt : Nat),
    state = .running (.sample name fresh law tail) ideal values bindings candidates
      pc clock enteredAt

end State

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

/-- An unreserved wire service slot has exactly the ordinary wire continuation
law, while retaining the complete service plan used by the environment. -/
theorem continuationAt_initialized_serviceWire
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
    (wire : runtime.application.WirePolicy)
    (slot : (plan.filterMap
      ServiceInstruction.environmentSlot)[execution.environmentHistory.length]? =
      some ServiceInstruction.wire) :
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
  have kernelEq := runtime.serviceEnvironment_wire plan wire execution.environmentHistory
    (MessageApplication.State.environmentView runtime.application execution.native) slot
  have invokeEq : runtime.application.invoke (runtime.compileProfile whole profile)
      (runtime.serviceEnvironment plan wire) execution .environment =
      runtime.application.invoke (runtime.compileProfile whole profile)
        (runtime.application.wireEnvironment wire) execution .environment := by
    simp only [MessageApplication.invoke]
    rw [kernelEq]
  have law := runtime.continuationAt_initialized_wire whole profile input unique discipline
    initialEnvironment initialSchedule execution reached wire
  apply law.trans
  symm
  apply FinDist.bindOnSupport_congr_measure invokeEq
  intro after serviceSupported wireSupported
  congr

/-- An expiry slot aimed at another phase is gated to `wait`, hence its actual
service invocation preserves the continuation exactly. -/
theorem continuationAt_initialized_expire_wait
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ)
    (initialEnvironment : runtime.application.EnvironmentPolicy)
    (initialSchedule : List (@MessageApplication.Invocation Player))
    (execution : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies
      (runtime.compileProfile whole profile) initialEnvironment initialSchedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (plan : List (ServiceInstruction Player))
    (wire : runtime.application.WirePolicy) (phase : Nat)
    (slot : (plan.filterMap
      ServiceInstruction.environmentSlot)[execution.environmentHistory.length]? =
      some (.expire phase))
    (gated : execution.native.application.phase ≠ phase) :
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
  apply runtime.continuationAt_environment_wait whole profile execution
  have viewPhase :
      (MessageApplication.State.environmentView runtime.application
        execution.native).application.pc = execution.native.application.phase := by
    change execution.native.application.publicView.pc = execution.native.application.phase
    simp
  simp [serviceEnvironment, slot, viewPhase, gated]

/-- At the current sample cursor, its matching expiry slot is the real chance
tick, so the actual service invocation satisfies the sample continuation law. -/
theorem Prefix.continuationAt_initialized_expire_sample
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (initialEnvironment : runtime.application.EnvironmentPolicy)
    (initialSchedule : List (@MessageApplication.Invocation Player))
    (execution : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies
      (runtime.compileProfile whole profile) initialEnvironment initialSchedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (plan : List (ServiceInstruction Player))
    (wire : runtime.application.WirePolicy) (site : Nat)
    (name : VarId) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (law : PublicDist (L := L) Γ payload)
    (tail : Graph Player L ((name, .pub payload) :: Γ) Δ)
    (walk : Prefix Δ whole (.sample name fresh law tail) site)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (atCursor : execution.native.application =
      .running (.sample name fresh law tail) ideal values bindings candidates site clock enteredAt)
    (slot : (plan.filterMap
      ServiceInstruction.environmentSlot)[execution.environmentHistory.length]? =
      some (.expire site)) :
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
  have follows := runtime.runPolicies_follows whole 0 (runtime.compileProfile whole profile)
    initialEnvironment initialSchedule _ execution (State.initial_follows whole input) reached
  have agreement := runtime.runPolicies_preserves_publicAgreement
    (runtime.compileProfile whole profile) initialEnvironment initialSchedule _ execution
    (State.initial_publicAgreement whole input) reached
  rw [atCursor] at agreement
  change (values : PublicValues Γ) = (PublicValues.ofVEnv ideal : PublicValues Γ) at agreement
  apply walk.continuationAt_sample_tick runtime whole profile site name fresh law tail execution
    ideal values bindings candidates clock enteredAt atCursor follows agreement
    (walk.target_names_nodup unique) (runtime.compileProfile whole profile)
    (runtime.serviceEnvironment plan wire)
  have viewPhase :
      (MessageApplication.State.environmentView runtime.application
        execution.native).application.pc = site := by
    change execution.native.application.publicView.pc = site
    simp [atCursor]
  simp [serviceEnvironment, slot, viewPhase]

/-- An initialized expiry invocation preserves the residual continuation when
service safety says either that its nominal phase is stale, or that the actual
cursor is a sample. The latter case internally recovers its unique typed prefix;
if its phase is also stale, the service gate still takes the wait branch. -/
theorem continuationAt_initialized_expire
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (initialEnvironment : runtime.application.EnvironmentPolicy)
    (initialSchedule : List (@MessageApplication.Invocation Player))
    (execution : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies
      (runtime.compileProfile whole profile) initialEnvironment initialSchedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (plan : List (ServiceInstruction Player))
    (wire : runtime.application.WirePolicy) (phase : Nat)
    (slot : (plan.filterMap
      ServiceInstruction.environmentSlot)[execution.environmentHistory.length]? =
      some (.expire phase))
    (safe : execution.native.application.phase ≠ phase ∨
      execution.native.application.IsSample) :
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
  rcases safe with stale | sample
  · exact runtime.continuationAt_initialized_expire_wait whole profile input
      initialEnvironment initialSchedule execution reached plan wire phase slot stale
  · rcases sample with ⟨Γ, name, payload, fresh, law, tail, ideal, values, bindings,
      candidates, pc, clock, enteredAt, atCursor⟩
    by_cases current : pc = phase
    · subst phase
      have follows := runtime.runPolicies_follows whole 0 (runtime.compileProfile whole profile)
        initialEnvironment initialSchedule _ execution (State.initial_follows whole input) reached
      have exactFollows : (State.running (.sample name fresh law tail) ideal values bindings
          candidates pc clock enteredAt).Follows whole 0 := atCursor ▸ follows
      obtain ⟨walk⟩ := State.prefix_of_running_follows whole (.sample name fresh law tail)
        ideal values bindings candidates pc clock enteredAt exactFollows
      exact walk.continuationAt_initialized_expire_sample runtime whole profile input unique
        initialEnvironment initialSchedule execution reached plan wire pc name fresh law tail
        ideal values bindings candidates clock enteredAt atCursor slot
    · apply runtime.continuationAt_initialized_expire_wait whole profile input
        initialEnvironment initialSchedule execution reached plan wire phase slot
      simpa [atCursor] using current

end Vegas.GraphRuntime
