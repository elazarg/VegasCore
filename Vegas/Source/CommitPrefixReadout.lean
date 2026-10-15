/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixInformationLaw
import Vegas.Source.ObservationRecall

/-! # Earlier owned views and binding draws inside a complete commitment word

Readouts discard only the later source constructors. They retain every old
public cell and the complete earlier own-action history, including failed
accepted bindings. The laws are those of the existing chronological kernels.
-/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}

/-- Recover the view at a telescope's entry from its complete final view. -/
def entryView : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    (block : CommitPrefix Γ O Δ P) → (who : Player) → DecisionView who Δ → DecisionView who Γ
  | _, _, _, _, .nil, _, view => view
  | _, _, _, _, .commit _ owner _ _ rest, who, view =>
      (rest.entryView who view).back (decide (owner = who))

/-- Every supported full word reconstructs the exact entry observation. -/
theorem prefixLaw_entryView (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entry : Config Player L Γ) (who : Player) :
    ((block.prefixLaw suffix profile entry).map (Config.view who)).map (block.entryView who) =
      PMF.pure (entry.view who) := by
  induction block with
  | nil => simp only [prefixLaw, PMF.pure_map, entryView]
  | commit name owner fresh guard rest ih =>
      change BehavioralProfile (.commit name owner fresh guard (rest.prepend suffix)) at profile
      simp only [prefixLaw, PMF.map_bind]
      have step (result : PublicationResult (L.Val _)) :
          ((rest.prefixLaw suffix (afterCommit profile)
            (commitSuccessor name guard entry result)).map (Config.view who)).map
              (fun view => (rest.entryView who view).back (decide (owner = who))) =
            PMF.pure (entry.view who) := by
        have recovered := congrArg (fun law =>
          law.map (fun view => view.back (decide (owner = who))))
            (ih suffix (afterCommit profile) (commitSuccessor name guard entry result))
        simpa only [PMF.map_comp, PMF.pure_map, back_commit_view, Function.comp_def] using recovered
      change (commitKernel profile (entry.view owner)).bind (fun result =>
        ((rest.prefixLaw suffix (afterCommit profile)
          (commitSuccessor name guard entry result)).map (Config.view who)).map
            (fun view => (rest.entryView who view).back (decide (owner = who)))) = _
      simp_rw [step]
      exact PMF.bind_const _ _

/-- A full word reconstructs the exact pre-binding view and binding result at
an interior position. Later foreign and repeated-owner choices remain sampled. -/
theorem prefixLaw_binding_readout
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (earlier : CommitPrefix Γ O Δ P)
    (later : CommitPrefix ((name, .commitment owner payload) :: Δ) (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (profile : BehavioralProfile
      (earlier.prepend (.commit name owner fresh guard (later.prepend suffix))))
    (entry : Config Player L Γ) :
    let current := earlier.tailProfile (.commit name owner fresh guard (later.prepend suffix))
      profile
    let before := earlier.prefixLaw (.commit name owner fresh guard (later.prepend suffix))
      profile entry
    let complete := before.bind (fun config =>
      ((CommitPrefix.commit name owner fresh guard later).prefixLaw suffix current config))
    let read := fun config : Config Player L Ξ =>
      let view := later.entryView owner (config.view owner)
      (view.back true, (view.1.cells name (.commitment owner payload) .here).getD .failure)
    complete.map read = bindPairLaw (before.map (Config.view owner)) (commitKernel current) := by
  intro current before complete read
  change (before.bind fun config =>
    (commitKernel current (config.view owner)).bind fun result =>
      later.prefixLaw suffix (afterCommit current) (commitSuccessor name guard config result)).map
        read = _
  rw [PMF.map_bind]
  calc
    _ = before.bind (fun config =>
        (commitKernel current (config.view owner)).map fun result => (config.view owner, result)) :=
      by
        apply bind_congr_on_support _
        intro config _supported
        rw [PMF.map_bind]
        change _ = (commitKernel current (config.view owner)).bind _
        apply bind_congr_on_support _
        intro result _drawn
        have recovered := later.prefixLaw_entryView suffix (afterCommit current)
          (commitSuccessor name guard config result) owner
        have projected := congrArg (fun law : PMF
            (DecisionView owner ((name, .commitment owner payload) :: Δ)) =>
          law.map fun view =>
            (view.back true, (view.1.cells name (.commitment owner payload) .here).getD .failure))
              recovered
        simp only [PMF.map_comp, PMF.pure_map] at projected
        change (later.prefixLaw suffix (afterCommit current)
          (commitSuccessor name guard config result)).map read = _ at projected
        have back : ((commitSuccessor name guard config result).view owner).back true =
            config.view owner := by
          simpa only [decide_true] using back_commit_view owner name guard config result
        have cell : (((commitSuccessor name guard config result).view owner).1.cells name
            (.commitment owner payload) .here).getD .failure = result := by
          simp only [Config.view, commitSuccessor, sourceObserve_commitment, ite_true,
            Option.getD_some]
          rfl
        simpa only [back, cell, Function.comp_apply] using projected
    _ = _ := by
      rw [bindPairLaw, PMF.bind_map]
      rfl

/-- Conditioning a complete block word recovers the original next typed draw
at the actual updated view. The later block word is not sampled independently. -/
theorem prefixLaw_binding_conditional
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (earlier : CommitPrefix Γ O Δ P)
    (later : CommitPrefix ((name, .commitment owner payload) :: Δ) (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (profile : BehavioralProfile
      (earlier.prepend (.commit name owner fresh guard (later.prepend suffix))))
    (entry : Config Player L Γ)
    (observed : DecisionView owner Δ)
    (present : observed ∈ ((earlier.prefixLaw
      (.commit name owner fresh guard (later.prepend suffix)) profile entry).map
        (Config.view owner)).support) :
    let current := earlier.tailProfile (.commit name owner fresh guard (later.prepend suffix))
      profile
    let before := earlier.prefixLaw (.commit name owner fresh guard (later.prepend suffix))
      profile entry
    let complete := before.bind (fun config =>
      ((CommitPrefix.commit name owner fresh guard later).prefixLaw suffix current config))
    let read := fun config : Config Player L Ξ =>
      let view := later.entryView owner (config.view owner)
      (view.back true, (view.1.cells name (.commitment owner payload) .here).getD .failure)
    (fiberPosterior complete (fun config => (read config).1) observed).map
      (fun config => (read config).2) = commitKernel current observed := by
  intro current before complete read
  have joint := earlier.prefixLaw_binding_readout fresh guard later suffix profile entry
  change complete.map read = bindPairLaw (before.map (Config.view owner))
    (commitKernel current) at joint
  have marginal : (complete.map read).map Prod.fst = before.map (Config.view owner) := by
    rw [joint, bindPairLaw_map_fst]
  have fullPresent : observed ∈
      (complete.map (fun config => (read config).1)).support := by
    have composed := marginal
    rw [PMF.map_comp] at composed
    exact composed.symm ▸ present
  have transfer := map_fiberPosterior_readout complete read Prod.fst observed fullPresent
  have composed := congrArg (fun law => law.map Prod.snd) transfer
  rw [PMF.map_comp, joint] at composed
  rw [show (fiberPosterior complete (fun config => (read config).1) observed).map
      (fun config => (read config).2) =
        (fiberPosterior (bindPairLaw (before.map (Config.view owner))
          (commitKernel current)) Prod.fst observed).map Prod.snd from composed]
  have pairPresent : observed ∈ ((bindPairLaw (before.map (Config.view owner))
      (commitKernel current)).map Prod.fst).support := by
    rw [bindPairLaw_map_fst]
    exact present
  ext result
  rw [fiberPosterior_map_snd_apply _ _ pairPresent, bindPairLaw_apply, bindPairLaw_map_fst,
    mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel ((PMF.mem_support_iff _ _).mp present)
      (PMF.apply_ne_top _ _), one_mul]

end Vegas.SourceProgram.CommitPrefix
