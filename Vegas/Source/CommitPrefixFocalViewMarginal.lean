/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixConditioning

/-! # Foreign source words survive conditioning on a focal current view -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Finite Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}

/-- At one original source entry, conditioning on the current focal view
retains the entire foreign word profile with its original joint law. The focal
unseen suffix is not fixed, and no independence across source entries is used. -/
theorem prefixLaw_foreign_focal_view (earlier : CommitPrefix Γ O Δ P)
    (later : CommitPrefix Δ P Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (profile : BehavioralProfile (earlier.prepend (later.prepend suffix)))
    (entry : Config Player L Γ) (who : Player) (observed : DecisionView who Δ)
    (present : observed ∈ ((earlier.prefixLaw (later.prepend suffix) profile entry).map
      (Config.view who)).support) :
    let current := earlier.tailProfile (later.prepend suffix) profile
    let complete := (earlier.prefixLaw (later.prepend suffix) profile entry).bind
      (later.prefixLaw suffix current)
    (fiberPosterior complete (fun final => later.entryView who (final.view who)) observed).map
        (fun final => fun other : {other : Player // other ≠ who} => final.view other.val) =
      complete.map (fun final => fun other : {other : Player // other ≠ who} =>
        final.view other.val) := by
  classical
  let : Fintype Player := Fintype.ofFinite Player
  intro current complete
  let foreign := independentProduct (fun other : {other : Player // other ≠ who} =>
    complete.map (Config.view other.val))
  have conditioned := congrArg (PMF.map Prod.snd)
    (earlier.prefixLaw_focal_view_product later suffix profile entry who observed present)
  rw [PMF.map_comp] at conditioned
  conv_rhs at conditioned => rw [PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def] at conditioned
  change (fiberPosterior complete (fun final => later.entryView who (final.view who))
    observed).map (fun final => fun other : {other : Player // other ≠ who} =>
      final.view other.val) =
    (fiberPosterior (complete.map (Config.view who)) (later.entryView who) observed).bind
      (fun _ => foreign.map id) at conditioned
  rw [PMF.map_id, PMF.bind_const] at conditioned
  let fullProfile := cast (congrArg BehavioralProfile
    (earlier.prepend_append later suffix).symm) profile
  have fullLaw : (earlier.append later).prefixLaw suffix fullProfile entry = complete := by
    simpa only [fullProfile, cast_cast, cast_eq] using
      earlier.prefixLaw_append later suffix fullProfile entry
  have product := (earlier.append later).prefixLaw_views_product suffix fullProfile entry
  rw [fullLaw] at product
  have projected := congrArg (PMF.map (fun words =>
    fun other : {other : Player // other ≠ who} => words other.val)) product
  have selected : (independentProduct (fun owner => complete.map (Config.view owner))).map
      (fun words => fun other : {other : Player // other ≠ who} => words other.val) = foreign :=
    independentProduct_map_embedding ⟨Subtype.val, Subtype.val_injective⟩ _
  rw [PMF.map_comp] at projected
  exact conditioned.trans (projected.trans selected).symm

end Vegas.SourceProgram.CommitPrefix
