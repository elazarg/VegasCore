/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Languages.Expressiveness.EFG_FOSG
import Vegas.Presentation.FOSG.RoundViewEquiv

/-!
# Round-view EFG presentation

Finite bounded round views can be serialized through the shared
`GameTheory.FOSG` bridge into extensive-form games.  The adapter is deliberately
generic over `Machine.RoundView`; compiled event graphs need an additional
finite-state presentation before they can use this export.
-/

namespace Vegas

open GameTheory

namespace Machine
namespace RoundView

variable {Player : Type} [DecidableEq Player] [Fintype Player]
variable {M : Machine Player}

/-- Bounded FOSG presentation package for a finite-state round view. -/
noncomputable def boundedFOSGPresentation
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public] :
    Languages.Expressiveness.BoundedFOSGPresentation Player := by
  classical
  exact
    { W := M.BoundedState horizon
      Act := view.Act
      PrivObs := M.Obs
      PubObs := M.Public
      game := view.toFOSG horizon cutoff
      horizon := horizon
      bounded := view.toFOSG_boundedHorizon horizon cutoff }

/-- Serialized plain EFG presentation of a finite-state bounded round view. -/
noncomputable def toPlainEFG
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public] :
    EFG.EFGGame :=
  (view.boundedFOSGPresentation horizon cutoff).toPlainEFG

/-- Reindexed kernel game induced by serializing a finite-state bounded round
view as an EFG. -/
noncomputable def toPlainEFGKernelGame
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public] :
    KernelGame Player :=
  (view.boundedFOSGPresentation horizon cutoff).toPlainEFGKernelGame

/-- Serialized plain EFG presentation with utility read from the final native
machine state instead of cumulative FOSG transition rewards. -/
noncomputable def toPlainEFGMachinePayoff
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public] :
    EFG.EFGGame := by
  classical
  let base := view.toPlainEFG horizon cutoff
  exact
    { base with
      utility := fun h playerIx =>
        optionOutcomeUtility M cutoff (M.outcome h.lastState.state)
          (FOSG.AugmentedEFGBridge.origPlayer (ι := Player) playerIx) }

/-- Reindexed EFG kernel game with final native machine payoff utility. -/
noncomputable def toPlainEFGMachinePayoffKernelGame
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public] :
    KernelGame Player where
  Strategy := (view.toPlainEFGKernelGame horizon cutoff).Strategy
  Outcome := (view.toPlainEFGKernelGame horizon cutoff).Outcome
  utility := fun h player =>
    optionOutcomeUtility M cutoff (M.outcome h.lastState.state) player
  outcomeKernel :=
    (view.toPlainEFGKernelGame horizon cutoff).outcomeKernel

/-- Native bounded FOSG kernel induced by the finite-state round view. -/
noncomputable def toFOSGKernelGame
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public] :
    KernelGame Player :=
  (view.boundedFOSGPresentation horizon cutoff).toKernelGame

/-- The serialized EFG has the same outcome law as the bounded FOSG
presentation under the bridge's behavioral-profile translation. -/
theorem toPlainEFGKernelGame_outcomeKernel_eq_fosg
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public]
    (profile : (view.toFOSGKernelGame horizon cutoff).Profile) :
    (view.toPlainEFGKernelGame horizon cutoff).outcomeKernel
        ((view.boundedFOSGPresentation horizon cutoff).translateProfile profile) =
      (view.toFOSGKernelGame horizon cutoff).outcomeKernel profile :=
  (view.boundedFOSGPresentation horizon cutoff).toPlainEFGKernelGame_outcomeKernel_eq_native
    profile

/-- The final-payoff EFG kernel has the same outcome law as the final-payoff
FOSG history kernel under the bridge's behavioral-profile translation. -/
theorem toPlainEFGMachinePayoffKernelGame_outcomeKernel_eq_fosg
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    [Fintype M.State]
    [∀ player, Fintype (view.Act player)]
    [∀ player, DecidableEq (view.Act player)]
    [∀ player, Fintype (M.Obs player)]
    [∀ player, DecidableEq (M.Obs player)]
    [Fintype M.Public] [DecidableEq M.Public]
    (profile :
      (Machine.RoundView.ToFOSG.machinePayoffHistoryKernelGame
        view horizon cutoff).Profile) :
    (view.toPlainEFGMachinePayoffKernelGame horizon cutoff).outcomeKernel
        ((view.boundedFOSGPresentation horizon cutoff).translateProfile profile) =
      (Machine.RoundView.ToFOSG.machinePayoffHistoryKernelGame
        view horizon cutoff).outcomeKernel profile := by
  classical
  have hEFG :
      (view.toPlainEFGMachinePayoffKernelGame horizon cutoff).outcomeKernel
        ((view.boundedFOSGPresentation horizon cutoff).translateProfile profile) =
        (view.toFOSGKernelGame horizon cutoff).outcomeKernel profile := by
    simpa [toPlainEFGMachinePayoffKernelGame] using
      view.toPlainEFGKernelGame_outcomeKernel_eq_fosg
        horizon cutoff profile
  have hFOSG :
      (view.toFOSGKernelGame horizon cutoff).outcomeKernel profile =
      (Machine.RoundView.ToFOSG.machinePayoffHistoryKernelGame
        view horizon cutoff).outcomeKernel profile := by
    letI : Fintype (view.toFOSG horizon cutoff).History :=
      (view.boundedFOSGPresentation horizon cutoff).historyFintype
    change
      ((view.toFOSG horizon cutoff).toKernelGameOfBoundedHorizon
          (view.toFOSG_boundedHorizon horizon cutoff)).outcomeKernel profile =
        (view.toFOSG horizon cutoff).runDist horizon profile
    exact FOSG.toKernelGameOfBoundedHorizon_outcomeKernel
      (G := view.toFOSG horizon cutoff)
      (hBound := view.toFOSG_boundedHorizon horizon cutoff) profile
  exact hEFG.trans hFOSG

end RoundView
end Machine

end Vegas
