/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixProduct
import GameTheory.Math.Probability.Conditioning

/-! # Original complete source configurations with full owner plans -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- Independent full owner plans and one chronological complete source Config
induce exactly the ownerwise plan/word product. Coordinates inside a full plan
are not separated, and repeated source actions stay in their original word. -/
theorem prefixLaw_plan_views_product {Plan : Player → Type}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (profile : BehavioralProfile (block.prepend suffix)) (entry : Config Player L Γ)
    (plans : (who : Player) → PMF (Plan who)) :
    independentProduct (fun who => (plans who).bind fun plan =>
      ((block.prefixLaw suffix profile entry).map (Config.view who)).map (Prod.mk plan)) =
    (independentProduct plans).bind fun selected =>
      (block.prefixLaw suffix profile entry).map fun complete who =>
        (selected who, complete.view who) := by
  rw [← independentProduct_bind]
  apply bind_congr_on_support
  intro selected _
  rw [← independentProduct_map, ← block.prefixLaw_views_product suffix profile entry,
    PMF.map_comp]
  rfl

/-- The original complete Config can be retained, rather than replaced by an
independent reconstruction. Its conditional fiber is attached to the same
complete owned words and full owner plans. -/
theorem prefixLaw_plan_config_joint {Plan : Player → Type}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (profile : BehavioralProfile (block.prepend suffix)) (entry : Config Player L Γ)
    (plans : (who : Player) → PMF (Plan who)) :
    let law := block.prefixLaw suffix profile entry
    let words := fun complete : Config Player L Δ => fun who => complete.view who
    let priors := fun who => (plans who).bind fun plan =>
      (law.map (Config.view who)).map (Prod.mk plan)
    ((independentProduct plans).bind fun selected => law.map fun complete =>
      ((fun who => (selected who, complete.view who)), complete)) =
    (independentProduct priors).bind fun memories =>
      (fiberPosterior law words (fun who => (memories who).2)).map (Prod.mk memories) := by
  intro law words priors
  have product := block.prefixLaw_plan_views_product suffix profile entry plans
  change independentProduct priors = (independentProduct plans).bind
    (fun selected => law.map fun complete who => (selected who, complete.view who)) at product
  rw [product, PMF.bind_bind]
  apply bind_congr_on_support
  intro selected _
  have reconstruct := congrArg (PMF.map fun complete =>
    ((fun who => (selected who, complete.view who)), complete))
      (fiberPosterior_reconstruct law words)
  rw [PMF.map_bind] at reconstruct
  refine reconstruct.symm.trans ?_
  have joined : law.map (fun complete who => (selected who, complete.view who)) =
      (law.map words).map (fun word who => (selected who, word who)) := by
    rw [PMF.map_comp]
    rfl
  conv_rhs => rw [joined, PMF.bind_map]
  apply bind_congr_on_support
  intro word present
  apply map_congr_on_support
  intro complete supported
  have same := (mem_support_fiberPosterior present supported).1
  exact Prod.ext (congrArg (fun w => fun who => (selected who, w who)) same) rfl

end Vegas.SourceProgram.CommitPrefix
