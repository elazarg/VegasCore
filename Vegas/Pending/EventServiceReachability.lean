/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventReplayEnvironment
import Vegas.Pending.EventResolutionOrigin
import Vegas.Pending.EventPrescribedAction
import Vegas.Pending.EventBindingService

/-! # Invariants at arbitrary prefixes of adaptive event service -/

noncomputable section

namespace Vegas.EventGraphRuntime.ServiceReachable

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}
variable (runtime : EventGraphRuntime graph)
variable (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
variable (players : Player → runtime.application.PlayerPolicy)
variable (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)

/-- Instruction invariants hold at every actual small-step service prefix,
including prefixes inside partially executed event blocks. -/
theorem execution_invariant (invariant : runtime.application.PolicyExecution → Prop)
    (initial : ∀ input ∈ inputs.support,
      invariant (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial input))))
    (preserved : ∀ instruction before after, invariant before →
      after ∈ (runtime.serviceStep players wire instruction before).support → invariant after)
    {control : ServiceControl runtime}
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order control) :
    invariant control.execution := by
  induction reachable with
  | initial input member => exact initial input member
  | @step before after prior supported ih =>
      rcases runtime.serviceControlStep_cases roster reactionRounds players wire order
        before after supported with same | selected | executed
      · obtain ⟨_, _, rfl⟩ := same
        exact ih
      · obtain ⟨_, _, _, _, _, rfl⟩ := selected
        exact ih
      · obtain ⟨instruction, _, _, _, _, member⟩ := executed
        exact preserved instruction before.execution after.execution ih member

/-- A reachable prefix retains the native invariant for one supported setup
draw; no public observer is given that draw. -/
theorem native_invariant {control : ServiceControl runtime}
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order control) :
    ∃ input ∈ inputs.support, control.execution.native.application.Invariant input := by
  apply execution_invariant runtime inputs roster reactionRounds players wire order
    (fun execution => ∃ input ∈ inputs.support, execution.native.application.Invariant input)
    _ _ reachable
  · intro input member
    exact ⟨input, member, State.initial_invariant input⟩
  · intro instruction before after holds member
    obtain ⟨input, inputMem, invariant⟩ := holds
    have progress := runtime.serviceStep_facts input players wire instruction before after
      invariant member
    exact ⟨input, inputMem, progress.invariant⟩

theorem bindingInvariant {control : ServiceControl runtime}
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order control) :
    control.execution.native.application.BindingInvariant := by
  exact execution_invariant runtime inputs roster reactionRounds players wire order
    (fun execution => execution.native.application.BindingInvariant)
    (fun input _ => State.initial_bindingInvariant input)
    (runtime.serviceStep_bindingInvariant players wire) reachable

theorem authorship {control : ServiceControl runtime}
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order control) :
    runtime.application.Authorship control.execution := by
  exact execution_invariant runtime inputs roster reactionRounds players wire order
    runtime.application.Authorship
    (fun input _ => MessageApplication.PolicyExecution.initial_authorship runtime.application
      (State.initial input))
    (runtime.serviceStep_authorship players wire) reachable

/-- Prescribed-owner history/cache coherence holds even when the service is
interrupted between sampling, preparation, and submission. -/
theorem policyCoherentAll (owner : Player) (policy : graph.BehavioralPolicy owner)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    {control : ServiceControl runtime}
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order control) :
    PolicyCoherentAll runtime control.execution owner := by
  exact execution_invariant runtime inputs roster reactionRounds players wire order
    (fun execution => PolicyCoherentAll runtime execution owner)
    (fun input _ => runtime.policyCoherentAll_initial input owner)
    (fun instruction before after => runtime.serviceStep_policyCoherentAll owner policy players
      wire instruction before after prescribed) reachable

theorem bindingPolicyCoherentAll (owner : Player) (policy : graph.BehavioralPolicy owner)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    {control : ServiceControl runtime}
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order control) :
    BindingPolicyCoherentAll runtime control.execution owner := by
  have holds : control.execution.native.pool.Satisfies
      (CanonicalCommitments (graph := graph) owner) ∧
      BindingPolicyCoherentAll runtime control.execution owner := by
    apply execution_invariant runtime inputs roster reactionRounds players wire order
      (fun execution => execution.native.pool.Satisfies
        (CanonicalCommitments (graph := graph) owner) ∧
          BindingPolicyCoherentAll runtime execution owner) _ _ reachable
    · intro input _
      exact ⟨MessagePool.Satisfies.empty, runtime.bindingPolicyCoherentAll_initial input owner⟩
    · intro instruction before after holds member
      exact ⟨runtime.serviceStep_canonicalCommitments owner policy players prescribed wire
          instruction before after holds.1 member,
        runtime.serviceStep_bindingPolicyCoherentAll owner policy players wire instruction
          before after prescribed holds.1 holds.2 member⟩
  exact holds.2

theorem canonicalResources (owner : Player) (policy : graph.BehavioralPolicy owner)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    {control : ServiceControl runtime}
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order control) :
    control.execution.native.application.CanonicalResources owner := by
  have holds : control.execution.native.pool.Satisfies
      (CanonicalCommitments (graph := graph) owner) ∧
      control.execution.native.application.CanonicalResources owner := by
    apply execution_invariant runtime inputs roster reactionRounds players wire order
      (fun execution => execution.native.pool.Satisfies
        (CanonicalCommitments (graph := graph) owner) ∧
          execution.native.application.CanonicalResources owner) _ _ reachable
    · intro input _
      exact ⟨MessagePool.Satisfies.empty, State.canonicalResources_initial input owner⟩
    · intro instruction before after holds member
      exact ⟨runtime.serviceStep_canonicalCommitments owner policy players prescribed wire
          instruction before after holds.1 member,
        runtime.serviceStep_canonicalResources owner players wire instruction
          before after holds.1 holds.2 member⟩
  exact holds.2

theorem bindingSubmissions (owner : Player) (policy : graph.BehavioralPolicy owner)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    {control : ServiceControl runtime}
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order control) :
    control.execution.native.pool.Satisfies
      (PrescribedBindingSubmissions (graph := graph) owner) := by
  exact execution_invariant runtime inputs roster reactionRounds players wire order
    (fun execution => execution.native.pool.Satisfies
      (PrescribedBindingSubmissions (graph := graph) owner))
    (fun _ _ => MessagePool.Satisfies.empty)
    (runtime.serviceStep_prescribedBindingSubmissions owner policy players prescribed wire)
    reachable

/-- Packet provenance is available at arbitrary actual prefixes, not only at
epoch boundaries or complete service outcomes. -/
theorem resolutionOrigins (ordered : graph.BarrierOrdered)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    {control : ServiceControl runtime}
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order control) :
    ResolutionOrigins runtime control.execution owner := by
  have holds : ∃ input ∈ inputs.support,
      ResolutionOriginInvariant runtime input control.execution owner := by
    apply execution_invariant runtime inputs roster reactionRounds players wire order
      (fun execution => ∃ input ∈ inputs.support,
        ResolutionOriginInvariant runtime input execution owner) _ _ reachable
    · intro input member
      exact ⟨input, member, State.initial_invariant input,
        runtime.policyCoherentAll_initial input owner,
        runtime.resolutionOrigins_initial input owner⟩
    · intro instruction before after holds member
      obtain ⟨input, inputMem, invariant⟩ := holds
      exact ⟨input, inputMem, runtime.serviceStep_resolutionOriginInvariant input ordered owner
        policy players prescribed wire instruction before after invariant member⟩
  obtain ⟨_, _, invariant⟩ := holds
  exact invariant.2.2

end Vegas.EventGraphRuntime.ServiceReachable
