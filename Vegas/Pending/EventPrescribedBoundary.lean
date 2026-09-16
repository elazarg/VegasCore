/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPrescribedService

/-! # Boundary state for one prescribed event owner -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- At an epoch boundary an unfinished event of the prescribed owner has not
yet spent its unique addressed submission. -/
def OwnerUnsubmitted (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (owner : Player) : Prop :=
  ∀ event, graph.actor? event = some owner →
    event ∉ execution.native.application.config.cut.completed →
      submittedAt (execution.principalHistory owner) event = false

theorem ownerUnsubmitted_initial (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (owner : Player) :
    OwnerUnsubmitted runtime
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial inputs))) owner := by
  intro event actor unfinished
  rfl

theorem OwnerUnsubmitted.frame
    {runtime : EventGraphRuntime graph}
    {before after : runtime.application.PolicyExecution} {owner : Player}
    (holds : OwnerUnsubmitted runtime before owner)
    (completed : before.native.application.config.cut.completed ⊆
      after.native.application.config.cut.completed)
    (history : after.principalHistory owner = before.principalHistory owner) :
    OwnerUnsubmitted runtime after owner := by
  intro event actor unfinished
  rw [history]
  exact holds event actor (fun done => unfinished (completed done))

/-- The invariants needed at a boundary between whole event visits for one
prescribed owner. Other players and the wire remain unrestricted. -/
structure PrescribedOwnerBoundary (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (execution : runtime.application.PolicyExecution)
    (owner : Player) : Prop where
  invariant : execution.native.application.Invariant inputs
  age : execution.native.application.OwnerActivationAgeOne owner
  policyCoherent : PolicyCoherentAll runtime execution owner
  bindingCoherent : BindingPolicyCoherentAll runtime execution owner
  authorship : runtime.application.Authorship execution
  canonical : execution.native.pool.Satisfies
    (CanonicalCommitments (graph := graph) owner)
  resources : execution.native.application.CanonicalResources owner
  bindingSubmissions : execution.native.pool.Satisfies
    (PrescribedBindingSubmissions (graph := graph) owner)
  resolutionOrigins : ResolutionOrigins runtime execution owner
  bindingInvariant : execution.native.application.BindingInvariant
  unsubmitted : OwnerUnsubmitted runtime execution owner

theorem prescribedOwnerBoundary_initial
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs) (owner : Player) :
    PrescribedOwnerBoundary runtime inputs
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial inputs))) owner := by
  refine ⟨State.initial_invariant inputs, State.ownerActivationAgeOne_initial inputs owner,
    runtime.policyCoherentAll_initial inputs owner,
    runtime.bindingPolicyCoherentAll_initial inputs owner,
    MessageApplication.PolicyExecution.initial_authorship runtime.application _,
    MessagePool.Satisfies.empty, State.canonicalResources_initial inputs owner,
    MessagePool.Satisfies.empty, runtime.resolutionOrigins_initial inputs owner,
    State.initial_bindingInvariant inputs, runtime.ownerUnsubmitted_initial inputs owner⟩

end Vegas.EventGraphRuntime
