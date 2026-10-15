/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixLaw
import Vegas.Source.CommitBlockInformation

/-! # Hidden source prefix laws and the next owned binding draw -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- Through a hidden commitment segment, the focal view law depends only on
its original policy and entry view. Foreign owners retain arbitrary dependence
on their own previous choices; no independent-per-event hypothesis is used. -/
theorem prefixLaw_view_eq (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (left right : BehavioralProfile (block.prepend suffix)) (who : Player)
    (samePolicy : left who = right who) (first second : Config Player L Γ)
    (sameView : first.view who = second.view who) :
    (block.prefixLaw suffix left first).map (Config.view who) =
      (block.prefixLaw suffix right second).map (Config.view who) := by
  induction block with
  | nil => simpa only [prefixLaw, PMF.pure_map] using congrArg PMF.pure sameView
  | commit name owner fresh guard rest ih =>
      simp only [prefixLaw, PMF.map_bind]
      have tail : afterCommit left who = afterCommit right who := congrArg Prod.snd samePolicy
      by_cases own : owner = who
      · subst owner
        have head : commitKernel left (first.view who) =
            commitKernel right (second.view who) := by
          simpa only [commitKernel, sameView] using
            congrArg (fun policy => policy.1 rfl (second.view who)) samePolicy
        rw [head]
        apply bind_congr_on_support
        intro result _drawn
        exact ih suffix (afterCommit left) (afterCommit right) tail
          (commitSuccessor name guard first result) (commitSuccessor name guard second result)
          (Config.view_commit_congr name guard first second sameView result result (fun _ => rfl))
      · let firstLaw := commitKernel left (first.view owner)
        let secondLaw := commitKernel right (second.view owner)
        let leftNext := fun result =>
          (rest.prefixLaw suffix (afterCommit left)
            (commitSuccessor name guard first result)).map (Config.view who)
        let rightNext := fun result =>
          (rest.prefixLaw suffix (afterCommit right)
            (commitSuccessor name guard second result)).map (Config.view who)
        change firstLaw.bind leftNext = secondLaw.bind rightNext
        calc
          _ = firstLaw.bind (fun result => secondLaw.bind (fun _ => leftNext result)) := by
            apply congrArg (PMF.bind firstLaw)
            funext result
            exact (PMF.bind_const _ _).symm
          _ = firstLaw.bind (fun _ => secondLaw.bind rightNext) := by
            apply bind_congr_on_support
            intro leftResult _leftDrawn
            apply bind_congr_on_support
            intro rightResult _rightDrawn
            exact ih suffix (afterCommit left) (afterCommit right) tail
              (commitSuccessor name guard first leftResult)
              (commitSuccessor name guard second rightResult)
              (Config.view_commit_congr name guard first second sameView _ _
                (fun impossible => (own impossible).elim))
          _ = _ := PMF.bind_const _ _

/-- Conditional latent completion retains the original law for the next
owned source binding. Its action is sampled at the actual full focal view. -/
theorem prefixPosterior_binding_joint
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (block : CommitPrefix Γ O Δ P)
    (profile : BehavioralProfile (block.prepend (.commit name owner fresh guard next)))
    (entry : Config Player L Γ) (observed : DecisionView owner Δ)
    (present : observed ∈ ((block.prefixLaw (.commit name owner fresh guard next) profile entry).map
      (Config.view owner)).support) :
    bindPairLaw (block.prefixPosterior (.commit name owner fresh guard next) profile entry owner
        observed) (fun final =>
          commitKernel (block.tailProfile (.commit name owner fresh guard next) profile)
            (final.view owner)) =
      bindPairLaw (block.prefixPosterior (.commit name owner fresh guard next) profile entry owner
        observed) (fun _ =>
          commitKernel (block.tailProfile (.commit name owner fresh guard next) profile)
            observed) := by
  unfold bindPairLaw
  apply bind_congr_on_support
  intro final supported
  have same := (block.prefixPosterior_supported (.commit name owner fresh guard next) profile
    entry owner observed present final supported).1
  dsimp only
  rw [same]

/-- The complete next binding marginal is the original source kernel; drawing
latent foreign choices does not alter or resample the current owned decision. -/
theorem prefixPosterior_binding_law
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (block : CommitPrefix Γ O Δ P)
    (profile : BehavioralProfile (block.prepend (.commit name owner fresh guard next)))
    (entry : Config Player L Γ) (observed : DecisionView owner Δ)
    (present : observed ∈ ((block.prefixLaw (.commit name owner fresh guard next) profile entry).map
      (Config.view owner)).support) :
    (block.prefixPosterior (.commit name owner fresh guard next) profile entry owner observed).bind
      (fun final => commitKernel (block.tailProfile (.commit name owner fresh guard next) profile)
        (final.view owner)) =
      commitKernel (block.tailProfile (.commit name owner fresh guard next) profile) observed := by
  have joint := congrArg (fun law : PMF (Config Player L Δ × PublicationResult (L.Val payload)) =>
    law.map Prod.snd) (block.prefixPosterior_binding_joint fresh guard next profile entry observed
      present)
  simpa only [bindPairLaw_map_snd, PMF.bind_const] using joint

end Vegas.SourceProgram.CommitPrefix
