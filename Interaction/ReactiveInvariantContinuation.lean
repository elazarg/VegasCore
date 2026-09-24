/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseKernel
import Interaction.ReactivePolicyInvariant

/-! # Application invariants in partial behavioral continuations -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal]
  {app : ReactiveApplication Principal} {predicate : app.State → Prop}

theorem Invariant.controlStep_some (invariant : app.Invariant predicate)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (before : app.Control) (after : app.ProtocolState)
    (valid : predicate before.execution.application)
    (supported : after ∈
      (app.controlStep initial horizon scheduler players (some before)).support) :
    ∃ result, after = some result ∧ predicate result.execution.application := by
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some who =>
      obtain ⟨response, _, reached⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      cases FinDist.mem_support_pure.mp reached
      exact ⟨_, rfl, invariant.respond execution who _ valid⟩
  | none =>
      cases remaining with
      | zero => cases FinDist.mem_support_pure.mp supported; exact ⟨_, rfl, valid⟩
      | succ remaining =>
          obtain ⟨command, _, moved⟩ :=
            Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
          obtain ⟨next, reached, rfl⟩ := FinDist.support_map .. ▸ moved
          exact ⟨_, rfl, invariant.environmentStep execution next command valid reached⟩

theorem Invariant.iterate_controlStep (invariant : app.Invariant predicate)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (fuel : Nat) (before : app.Control)
    (after : app.ProtocolState) (valid : predicate before.execution.application)
    (supported : after ∈ ((fun law => law.bind
      (app.controlStep initial horizon scheduler players))^[fuel]
        (FinDist.pure (some before))).support) :
    ∃ result, after = some result ∧ predicate result.execution.application := by
  induction fuel generalizing after with
  | zero => cases FinDist.mem_support_pure.mp supported; exact ⟨_, rfl, valid⟩
  | succ fuel ih =>
      rw [Function.iterate_succ_apply'] at supported
      obtain ⟨middle, middleMem, moved⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      obtain ⟨control, rfl, middleValid⟩ := ih middle middleMem
      exact invariant.controlStep_some initial horizon scheduler players control after
        middleValid moved

/-- Any amount of behavioral execution preserves a previously established
application invariant. The starting history need not be on the profile's path. -/
theorem Invariant.behavioral_continuation [Fintype Principal] (invariant : app.Invariant predicate)
    (menu : app.ResponseMenu) (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) (before : app.Control)
    (trace : (menu.protocol initial horizon scheduler).Trace (some before))
    (after : (menu.protocol initial horizon scheduler).History)
    (valid : predicate before.execution.application)
    (supported : after ∈ ((menu.information initial horizon scheduler).runBehavioralFrom
      profile fuel ⟨some before, trace⟩).support) :
    ∃ result, after.state = some result ∧ predicate result.execution.application := by
  apply invariant.iterate_controlStep initial horizon scheduler
    (menu.decodeProfile initial horizon scheduler profile) fuel before after.state valid
  have law := menu.run_map_controlStep initial horizon scheduler profile fuel ⟨some before, trace⟩
  apply (congrArg (fun law : FinDist app.ProtocolState => after.state ∈ law.support) law).mp
  rw [FinDist.support_map]
  exact ⟨after, supported, rfl⟩

end Interaction.ReactiveApplication
