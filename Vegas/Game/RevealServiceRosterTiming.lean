/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRoster
import GameTheoryExtensions.Math.Probability.DeferredChoice

/-! # A common timing perturbation for every finite activation roster

Every event owner needs at least one response opportunity. A positive uniform
component gives every opening time positive probability; its weight bounds
all earlier timing mass simultaneously and tends to zero. No assumption about
the relative speed of source trembles is needed.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (rosters : (graph setup).EventId → List Player)
  (coverage : ∀ event owner, (graph setup).actor? event = some owner → owner ∈ rosters event)

def rosterLastSlot (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) : Fin ((rosters event).count owner) :=
  ⟨(rosters event).count owner - 1, by
    have positive := List.count_pos_iff.mpr (coverage event owner owned)
    omega⟩

theorem rosterLastSlot_final (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) :
    (rosterLastSlot setup rosters coverage event owner owned).val + 1 =
      (rosters event).count owner := by
  have positive := List.count_pos_iff.mpr (coverage event owner owned)
  dsimp only [rosterLastSlot]
  omega

def rosterTiming (weight : ℝ) (nonnegative : 0 ≤ weight) (bounded : weight ≤ 1)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) :
    FinDist (Fin ((rosters event).count owner)) :=
  let last := rosterLastSlot setup rosters coverage event owner owned
  letI : Nonempty (Fin ((rosters event).count owner)) := ⟨last⟩
  FinDist.mix weight nonnegative bounded FinDist.uniformOfFintype (FinDist.pure last)

theorem rosterTiming_fullSupport (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bounded : weight ≤ 1) (positive : 0 < weight)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) :
    (rosterTiming setup rosters coverage weight nonnegative bounded
      event owner owned).FullSupport := by
  let _ : Nonempty (Fin ((rosters event).count owner)) :=
    ⟨rosterLastSlot setup rosters coverage event owner owned⟩
  intro slot
  exact FinDist.mem_support_mix_left weight nonnegative bounded positive
    (FinDist.mem_support_uniformOfFintype slot)

/-- One common error bound covers every owner at every occurrence before its
last opportunity, including source probabilities arbitrarily close to one. -/
theorem rosterTiming_prefix_le (weight : ℝ) (nonnegative : 0 ≤ weight) (bounded : weight ≤ 1)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (visits : Nat) (before : visits < (rosters event).count owner) :
    (rosterTiming setup rosters coverage weight nonnegative bounded event owner owned).timingPrefix
      visits ≤ weight := by
  let last := rosterLastSlot setup rosters coverage event owner owned
  let _ : Nonempty (Fin ((rosters event).count owner)) := ⟨last⟩
  have earlier : visits ≤ last.val := by
    have final := rosterLastSlot_final setup rosters coverage event owner owned
    change last.val + 1 = _ at final
    omega
  change (FinDist.mix weight nonnegative bounded FinDist.uniformOfFintype
    (FinDist.pure last)).timingPrefix visits ≤ weight
  rw [FinDist.timingPrefix_mix, FinDist.timingPrefix_pure_of_le last visits earlier,
    mul_zero, add_zero]
  exact (mul_le_mul_of_nonneg_left (FinDist.timingPrefix_le_one _ _) nonnegative).trans_eq
    (mul_one weight)

theorem rosterTiming_converges {weight : Nat → ℝ}
    (nonnegative : ∀ n, 0 ≤ weight n) (bounded : ∀ n, weight n ≤ 1)
    (vanishes : Tendsto weight atTop (nhds 0))
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) :
    FinDistConvergesPointwise
      (fun n => rosterTiming setup rosters coverage (weight n) (nonnegative n) (bounded n)
        event owner owned)
      (FinDist.pure (rosterLastSlot setup rosters coverage event owner owned)) := by
  let last := rosterLastSlot setup rosters coverage event owner owned
  let _ : Nonempty (Fin ((rosters event).count owner)) := ⟨last⟩
  intro slot
  have first := vanishes.mul_const
    ((FinDist.uniformOfFintype : FinDist (Fin ((rosters event).count owner))).prob slot)
  have one : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have second := (one.sub vanishes).mul_const ((FinDist.pure last).prob slot)
  simpa only [rosterTiming, FinDist.prob_mix, zero_mul, sub_zero, one_mul, zero_add] using
    first.add second

end Vegas.SourceProgram.RevealService
