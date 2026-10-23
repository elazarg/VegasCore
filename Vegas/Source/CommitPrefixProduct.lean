/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitPrefixInformationLaw
import GameTheory.Math.Probability.Product

/-! # Ownerwise joint laws of complete typed commitment blocks -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- Conditional on the actual entry configuration, distinct owners' full
block views are independent. Repeated choices of one owner remain in its
chronological marginal, evaluated at updated views and own-action histories. -/
theorem prefixLaw_views_product (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entry : Config Player L Γ) :
    (block.prefixLaw suffix profile entry).map (fun final who => final.view who) =
      independentProduct (fun who =>
        (block.prefixLaw suffix profile entry).map (Config.view who)) :=
    by
  classical
  induction block with
  | nil =>
      simp only [prefixLaw, PMF.pure_map]
      exact (independentProduct_pure _).symm
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let draw := commitKernel profile (entry.view owner)
      let next := fun result => rest.prefixLaw suffix (afterCommit profile)
        (commitSuccessor name guard entry result)
      let factors := fun result who => (next result).map (Config.view who)
      have conditional (result : PublicationResult (L.Val payload)) :
          (next result).map (fun final who => final.view who) =
            independentProduct (factors result) :=
        ih suffix (afterCommit profile) (commitSuccessor name guard entry result)
      have foreign (result : PublicationResult (L.Val payload)) (who : Player)
          (different : who ≠ owner) : factors result who = factors .failure who := by
        apply rest.prefixLaw_view_eq suffix (afterCommit profile) (afterCommit profile) who rfl
        exact Config.view_commit_congr name guard entry entry rfl result .failure
          (fun same => (different same.symm).elim)
      let residual := independentProduct (fun who : {who : Player // who ≠ owner} =>
        factors .failure who)
      let join := (Equiv.piSplitAt owner (fun who => DecisionView who Δ)).symm
      have remainder (result : PublicationResult (L.Val payload)) :
          independentProduct (fun who : {who : Player // who ≠ owner} => factors result who) =
            residual := by
        apply congrArg independentProduct
        funext who
        exact foreign result who who.2
      have split (result : PublicationResult (L.Val payload)) :
          independentProduct (factors result) =
            (factors result owner).bind fun value =>
              residual.map (fun rest => join (value, rest)) := by
        rw [independentProduct_splitAt _ owner, remainder result]
      have marginalized : independentProduct
          (fun who : {who : Player // who ≠ owner} =>
            draw.bind (fun result => factors result who)) =
            residual := by
        apply congrArg independentProduct
        funext who
        calc
          _ = draw.bind (fun _ => factors .failure who) := by
            apply bind_congr_on_support
            intro result _supported
            exact foreign result who who.2
          _ = _ := PMF.bind_const _ _
      simp only [prefixLaw, PMF.map_bind]
      change draw.bind (fun result => (next result).map (fun final who => final.view who)) =
        independentProduct (fun who => draw.bind (fun result => factors result who))
      calc
        _ = draw.bind (fun result => independentProduct (factors result)) := by
          apply congrArg (PMF.bind draw)
          funext result
          exact conditional result
        _ = draw.bind (fun result => (factors result owner).bind fun value =>
            residual.map (fun rest => join (value, rest))) := by
          apply congrArg (PMF.bind draw)
          funext result
          exact split result
        _ = (draw.bind (fun result => factors result owner)).bind
            (fun value => residual.map (fun rest => join (value, rest))) :=
          (PMF.bind_bind _ _ _).symm
        _ = _ := by rw [independentProduct_splitAt _ owner, marginalized]

/-- The same block law factors across complete effective own-action words.
No independence between successive actions of one player is asserted. -/
theorem prefixLaw_histories_product (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entry : Config Player L Γ) :
    (block.prefixLaw suffix profile entry).map Config.history =
      independentProduct (fun who => (block.prefixLaw suffix profile entry).map
        (fun final => final.history who)) := by
  have joint := congrArg (fun law : PMF (∀ who, DecisionView who Δ) =>
    law.map (fun views who => (views who).2)) (block.prefixLaw_views_product suffix profile entry)
  rw [independentProduct_map] at joint
  simpa only [PMF.map_comp, Function.comp_def, Config.view] using joint

end Vegas.SourceProgram.CommitPrefix
