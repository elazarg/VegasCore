/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicyBindings
import Vegas.Compile.ApplicationImageProvenance
import Vegas.Compile.ApplicationRelayHistory

/-! # Binding provenance under a padded lifted player strategy

One player's commands may be supported by its structurally lifted source policy
or be inert waits and expiry submissions. This suffices to maintain agreement
between its recorded private registrations and accepted native snapshots.
All other players and the environment may use arbitrary runtime strategies.
The retained registrations are also typed by their fields in the plan's final
compiled graph. This proves a premise of the native-to-source readout law
throughout actual execution; successful loading and source-state
correspondence remain separate.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- From empty preparation and message histories, a player whose commands are
supported by its lifted policy or are idle/expiry commands maintains its
accepted-binding provenance through every supported run.
This requires no fairness, deadline protection, restrictions on opponents,
or source-matching readout supplied as a hypothesis. -/
theorem runPolicies_lifted_registeredBindings
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) (profile : SourceBehavioralProfile prog)
    (owner : P) (players : P → (plan.image deadlineOf).application.PlayerPolicy)
    (hcommands : ∀ history view command,
      command ∈ (players owner history view).support →
        command ∈ (plan.liftProfile deadlineOf profile owner history view).support ∨
          (plan.image deadlineOf).IdleOrExpiryCommand command)
    (environment : (plan.image deadlineOf).application.EnvironmentPolicy)
    (memory : ApplicationImage.Memory P L)
    (hempty : ∀ field, memory.accepted field = none)
    (schedule : List (@Invocation P))
    (next : (plan.image deadlineOf).application.PolicyExecution)
    (hnext : next ∈ ((plan.image deadlineOf).application.runPolicies players environment schedule
      (PolicyExecution.initial (plan.image deadlineOf).application
        (MessageApplication.State.initial (plan.image deadlineOf).application
          (ApplicationImage.State.initial memory)))).support) :
    (plan.image deadlineOf).RegisteredBindings owner
      (fun slot typed => ∃ spec : FieldSpec P L,
        (compileCore prog fresh state).graph.field? slot = some spec ∧
          typed.ty = spec.ty)
      (next.principalHistory owner) next.native.application := by
  apply (plan.image deadlineOf).runPolicies_registeredBindings_of_registered_submissions
    memory hempty owner
    (fun slot typed => ∃ spec : FieldSpec P L,
      (compileCore prog fresh state).graph.field? slot = some spec ∧
        typed.ty = spec.ty)
    players environment ?_ schedule next hnext
  intro history view address handle hcommand
  rcases hcommands history view (.submit (.binding address handle)) hcommand with
    hsource | hidle
  · exact plan.liftProfileIn_binding_submission (plan.image deadlineOf) deadlineOf
      profile owner history view address handle hsource
  · exact False.elim (hidle trivial)

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.runPolicies_lifted_registeredBindings' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.runPolicies_lifted_registeredBindings
