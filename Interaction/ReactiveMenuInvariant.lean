/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseMenu
import Interaction.ReactiveServiceInvariant

/-! # Execution invariants for response-menu instances

Player obligations cover every legal menu action, including off-path deviations.
Environment obligations cover every supported command and transition of the
fixed scheduler. No prescribed strategy enters the certificate.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu)

structure ServiceInvariant (scheduler : app.Scheduler)
    (predicate : app.Execution → Prop) : Prop where
  respond : ∀ execution who action, predicate execution →
    action ∈ menu.actions who (execution.recall who) (execution.observe app who) →
    predicate (execution.respond app who action)
  environment : ∀ execution next command, predicate execution →
    command ∈ (scheduler execution.environmentRecall
      (execution.observeEnvironment app)).support →
    next ∈ (execution.environmentStep app command).support → predicate next

variable {menu} {scheduler : app.Scheduler} {predicate : app.Execution → Prop}

theorem ServiceInvariant.transition (invariant : menu.ServiceInvariant scheduler predicate)
    (initial : FinDist app.State) (horizon : Nat)
    (setup : ∀ state ∈ initial.support, predicate (Execution.initial app state))
    (before after : app.ProtocolState) (joint : Principal → Option app.Action)
    (valid : serviceInvariant predicate before)
    (legal : (menu.protocol initial horizon scheduler).Legal before joint)
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
          have localLegal := legal.2 who
          cases selected : joint who with
          | none => simp [selected, protocol, ReactiveApplication.actor] at localLegal
          | some action =>
              rw [selected] at localLegal
              cases FinDist.mem_support_pure.mp reached
              simpa only [serviceInvariant, selected, Option.getD_some] using
                invariant.respond execution who action valid localLegal.2
      | none =>
          cases remaining with
          | zero => cases FinDist.mem_support_pure.mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, selected, moved⟩ :=
                Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ moved
              exact invariant.environment execution next command valid selected supported

theorem ServiceInvariant.history (invariant : menu.ServiceInvariant scheduler predicate)
    (initial : FinDist app.State) (horizon : Nat)
    (setup : ∀ state ∈ initial.support, predicate (Execution.initial app state)) :
    ∀ {state} (_trace : (menu.protocol initial horizon scheduler).Trace state),
      serviceInvariant predicate state
  | _, .start => trivial
  | _, .extend prior joint legal reached =>
      invariant.transition initial horizon setup _ _ joint
        (invariant.history initial horizon setup prior) legal reached

end Interaction.ReactiveApplication.ResponseMenu
