/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveLocalContinuation
import Interaction.ReactivePolicyInvariant

/-! # Existing execution invariants through actual menu continuations -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
    {app : ReactiveApplication Principal}

/-- The original menu continuation retains any full-execution predicate whose
actual decoded response and environment kernels preserve it. -/
theorem PolicyInvariant.run_menu
    (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    {predicate : app.Execution → Prop}
    (invariant : app.PolicyInvariant
      (menu.decodeProfile initial horizon scheduler profile) predicate)
    (initialized : ∀ state ∈ initial.support, predicate (Execution.initial app state))
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (valid : executionInvariant predicate history.state) :
    ∀ final ∈ ((menu.information initial horizon scheduler).runBehavioralFrom
      profile fuel history).support, executionInvariant predicate final.state := by
  intro final supported
  have stateSupported : final.state ∈
      (((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history).map
        History.state).support := by
    rw [PMF.support_map]
    exact ⟨final, supported, rfl⟩
  rw [menu.run_map_controlSteps initial horizon scheduler profile] at stateSupported
  have propagate (count : Nat) (state : app.ProtocolState)
      (member : state ∈ ((fun law => law.bind (app.controlStep initial horizon scheduler
        (menu.decodeProfile initial horizon scheduler profile)))^[count]
          (PMF.pure history.state)).support) : executionInvariant predicate state := by
    induction count generalizing state with
    | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp member
      exact valid
    | succ count ih =>
      rw [Function.iterate_succ_apply'] at member
      obtain ⟨before, prior, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ member)
      exact invariant.controlStep initial horizon scheduler initialized
        before state (ih before prior) reached
  exact propagate fuel final.state stateSupported

end Interaction.ReactiveApplication
