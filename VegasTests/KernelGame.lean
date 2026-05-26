/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.GameBridge.EFG.FromRoundView
import Vegas.GameBridge.FOSG.FromRoundView
import Vegas.Machine.KernelGame

/-!
# Kernel game bridge tests

This module checks the round-view bridges into kernel games, FOSG, and EFG on
small finite-state and infinite-state examples.
-/

namespace VegasTests

open GameTheory

namespace InfiniteStateRoundView

noncomputable def machine : Vegas.Machine PUnit where
  State := Nat
  Action := fun _ => PUnit
  Internal := PUnit
  Public := PUnit
  Obs := fun _ => PUnit
  Outcome := PUnit
  init := 0
  available := fun _ _ => Set.univ
  availableInternal := fun _ => Set.univ
  stepPlay := fun _ _ state => PMF.pure (state + 1)
  stepInternal := fun _ state => PMF.pure (state + 1)
  terminal := fun _ => False
  publicView := fun _ => PUnit.unit
  observe := fun _ _ => PUnit.unit
  outcome := fun _ => none
  utility := fun _ _ => 0

noncomputable def view : machine.RoundView where
  Act := fun _ => PUnit
  active := fun _ => Finset.univ
  availableActions := fun _ _ => Set.univ
  transition := fun (state : Nat) _ => PMF.pure (state + 1)
  eventBatch := fun _ _ _ => []
  terminal_active_eq_empty := by
    intro _ hterminal
    cases hterminal
  nonterminal_exists_legal := by
    intro _ hterminal
    refine ⟨fun _ => some PUnit.unit, hterminal, ?_⟩
    intro player
    simp

noncomputable example : KernelGame PUnit := by
  classical
  letI : ∀ player, Fintype (Option (view.Act player)) := by
    intro player
    dsimp [view]
    infer_instance
  exact view.boundedPureKernelGame 2 2 (fun _ => 0)

noncomputable example : KernelGame PUnit := by
  classical
  letI : ∀ player, Fintype (Option (view.Act player)) := by
    intro player
    dsimp [view]
    infer_instance
  exact view.boundedBehavioralKernelGame 2 2 (fun _ => 0)

noncomputable example :
    GameTheory.FOSG PUnit (machine.BoundedState 2) view.Act machine.Obs
      machine.Public :=
  view.toFOSG 2 (fun _ => 0)

example : (view.toFOSG 2 (fun _ => 0)).BoundedHorizon 2 :=
  view.toFOSG_boundedHorizon 2 (fun _ => 0)

end InfiniteStateRoundView

namespace FiniteStateRoundView

noncomputable def machine : Vegas.Machine PUnit where
  State := Bool
  Action := fun _ => PUnit
  Internal := PUnit
  Public := PUnit
  Obs := fun _ => PUnit
  Outcome := PUnit
  init := false
  available := fun state _ =>
    match state with
    | true => ∅
    | false => Set.univ
  availableInternal := fun state =>
    match state with
    | true => ∅
    | false => Set.univ
  stepPlay := fun _ _ _ => PMF.pure true
  stepInternal := fun _ _ => PMF.pure true
  terminal := fun state => state = true
  publicView := fun _ => PUnit.unit
  observe := fun _ _ => PUnit.unit
  outcome := fun state => if state then some PUnit.unit else none
  utility := fun _ _ => 0

noncomputable instance instFintypeMachineState :
    Fintype machine.State := by
  dsimp [machine]
  infer_instance

noncomputable def view : machine.RoundView where
  Act := fun _ => PUnit
  active := fun state =>
    match state with
    | true => ∅
    | false => Finset.univ
  availableActions := fun state _ =>
    match state with
    | true => ∅
    | false => Set.univ
  transition := fun _ _ => PMF.pure true
  eventBatch := fun _ _ _ => []
  terminal_active_eq_empty := by
    intro state hterminal
    cases state <;> simp [machine] at hterminal ⊢
  nonterminal_exists_legal := by
    intro state hterminal
    refine ⟨fun _ => some PUnit.unit, hterminal, ?_⟩
    intro player
    cases state <;> simp [machine] at hterminal ⊢

noncomputable instance instFintypeViewAct (player : PUnit) :
    Fintype (view.Act player) := by
  dsimp [view]
  infer_instance

instance instDecidableEqViewAct (player : PUnit) :
    DecidableEq (view.Act player) := by
  dsimp [view]
  infer_instance

noncomputable instance instFintypeMachineObs (player : PUnit) :
    Fintype (machine.Obs player) := by
  dsimp [machine]
  infer_instance

instance instDecidableEqMachineObs (player : PUnit) :
    DecidableEq (machine.Obs player) := by
  dsimp [machine]
  infer_instance

noncomputable instance instFintypeMachinePublic :
    Fintype machine.Public := by
  dsimp [machine]
  infer_instance

instance instDecidableEqMachinePublic :
    DecidableEq machine.Public := by
  dsimp [machine]
  infer_instance

noncomputable example :
    GameTheory.Languages.Expressiveness.BoundedFOSGPresentation PUnit :=
  view.boundedFOSGPresentation 1 (fun _ => 0)

noncomputable example : EFG.EFGGame :=
  view.toPlainEFG 1 (fun _ => 0)

noncomputable example : KernelGame PUnit :=
  view.toPlainEFGKernelGame 1 (fun _ => 0)

end FiniteStateRoundView

end VegasTests
