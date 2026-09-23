/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveProtocol

/-! # Service invariants at every legal reactive history

Player responses are unrestricted. Environment obligations cover the commands
supported by the chosen observation-local scheduler. The resulting invariant
therefore holds at off-path subgame roots as well as during prescribed play.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

structure ServiceInvariant (scheduler : app.Scheduler)
    (predicate : app.Execution → Prop) : Prop where
  respond : ∀ execution who action, predicate execution →
    predicate (execution.respond app who action)
  environment : ∀ execution next command, predicate execution →
    command ∈ (scheduler execution.environmentRecall
      (execution.observeEnvironment app)).support →
    next ∈ (execution.environmentStep app command).support → predicate next

variable {app} {scheduler : app.Scheduler} {predicate : app.Execution → Prop}

def serviceInvariant (predicate : app.Execution → Prop) : app.ProtocolState → Prop
  | none => True
  | some control => predicate control.execution

variable [Inhabited app.Memory]

theorem ServiceInvariant.transition (invariant : app.ServiceInvariant scheduler predicate)
    (initial : FinDist app.State) (horizon : Nat)
    (setup : ∀ state ∈ initial.support, predicate (Execution.initial app state))
    (before after : app.ProtocolState) (joint : Principal → Option app.Action)
    (valid : serviceInvariant predicate before)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    serviceInvariant predicate after := by
  cases before with
  | none =>
      obtain ⟨state, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      exact setup state supported
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases FinDist.mem_support_pure.mp reached
          exact invariant.respond execution who _ valid
      | none =>
          cases remaining with
          | zero => cases FinDist.mem_support_pure.mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, selected, moved⟩ :=
                Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ moved
              exact invariant.environment execution next command valid selected supported

theorem ServiceInvariant.history (invariant : app.ServiceInvariant scheduler predicate)
    (initial : FinDist app.State) (horizon : Nat)
    (setup : ∀ state ∈ initial.support, predicate (Execution.initial app state)) :
    ∀ {state} (_trace : (app.protocol initial horizon scheduler).Trace state),
      serviceInvariant predicate state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      invariant.transition initial horizon setup _ _ joint
        (invariant.history initial horizon setup prior) reached

end Interaction.ReactiveApplication
