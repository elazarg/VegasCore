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

end Vegas.SourceProgram.CommitPrefix
