/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Core.KernelGame
import Vegas.Machine.RoundView

/-!
# Kernel games from native round views

This module is the game-theoretic bridge for `Machine.RoundView`.

The bridge is explicitly bounded: a horizon defines the finite strategic
history space, and `steps` says how many bounded rounds are executed. Outcomes
are partial at the machine layer, so the caller must provide an explicit
cutoff utility for `none` instead of inheriting a hidden zero-payoff policy.
-/

namespace Vegas

open GameTheory

namespace Machine

variable {Player : Type} {M : Machine Player}

namespace RoundView

/-- Utility for partial machine outcomes with an explicit cutoff policy. -/
def optionOutcomeUtility (M : Machine Player) (cutoff : Payoff Player) :
    Option M.Outcome → Payoff Player
  | some outcome => M.utility outcome
  | none => cutoff

/-- Bounded pure-strategy kernel game induced by a native round view. -/
noncomputable def boundedPureKernelGame
    (view : M.RoundView) (horizon steps : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (cutoff : Payoff Player) : KernelGame Player where
  Strategy := fun player => view.BoundedPureStrategy horizon player
  Outcome := Option M.Outcome
  utility := optionOutcomeUtility M cutoff
  outcomeKernel := fun σ =>
    view.boundedOutcomeFromPure horizon σ steps

/-- Bounded behavioral-strategy kernel game induced by a native round view. -/
noncomputable def boundedBehavioralKernelGame
    (view : M.RoundView) (horizon steps : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (cutoff : Payoff Player) : KernelGame Player where
  Strategy := fun player => view.BoundedBehavioralStrategy horizon player
  Outcome := Option M.Outcome
  utility := optionOutcomeUtility M cutoff
  outcomeKernel := fun σ =>
    view.boundedOutcomeFromBehavioral horizon σ steps

@[simp] theorem optionOutcomeUtility_some
    (M : Machine Player) (cutoff : Payoff Player) (outcome : M.Outcome) :
    optionOutcomeUtility M cutoff (some outcome) = M.utility outcome := rfl

@[simp] theorem optionOutcomeUtility_none
    (M : Machine Player) (cutoff : Payoff Player) :
    optionOutcomeUtility M cutoff none = cutoff := rfl

@[simp] theorem boundedPureKernelGame_outcomeKernel
    (view : M.RoundView) (horizon steps : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (cutoff : Payoff Player)
    (σ : (view.boundedPureKernelGame horizon steps cutoff).Profile) :
    (view.boundedPureKernelGame horizon steps cutoff).outcomeKernel σ =
      view.boundedOutcomeFromPure horizon σ steps := rfl

@[simp] theorem boundedBehavioralKernelGame_outcomeKernel
    (view : M.RoundView) (horizon steps : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (cutoff : Payoff Player)
    (σ : (view.boundedBehavioralKernelGame horizon steps cutoff).Profile) :
    (view.boundedBehavioralKernelGame horizon steps cutoff).outcomeKernel σ =
      view.boundedOutcomeFromBehavioral horizon σ steps := rfl

end RoundView

end Machine

end Vegas
