/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixReadout

/-! # Complete commitment words jointly with their original entry

The entry law remains inside the chronological source mixture. Conditioning
the current owned view retains its entry posterior; it does not replace the
entry mixture by an independent product of words.
-/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}

/-- The full chronological word retains the original entry jointly with the
earlier owned view and next result, for an arbitrary correlated entry law. -/
theorem prefixLaw_binding_entry_readout
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (earlier : CommitPrefix Γ O Δ P)
    (later : CommitPrefix ((name, .commitment owner payload) :: Δ) (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (profile : BehavioralProfile
      (earlier.prepend (.commit name owner fresh guard (later.prepend suffix))))
    (entryLaw : PMF (Config Player L Γ)) :
    let current := earlier.tailProfile (.commit name owner fresh guard (later.prepend suffix))
      profile
    let before := fun entry => earlier.prefixLaw
      (.commit name owner fresh guard (later.prepend suffix)) profile entry
    let complete := fun entry => (before entry).bind fun config =>
      (CommitPrefix.commit name owner fresh guard later).prefixLaw suffix current config
    let read := fun config : Config Player L Ξ =>
      let view := later.entryView owner (config.view owner)
      (view.back true, (view.1.cells name (.commitment owner payload) .here).getD .failure)
    let joint := entryLaw.bind fun entry => (complete entry).map (Prod.mk entry)
    let prior := entryLaw.bind fun entry =>
      (before entry).map fun config => (entry, config.view owner)
    joint.map (fun pair => ((pair.1, (read pair.2).1), (read pair.2).2)) =
      bindPairLaw prior (fun pair => commitKernel current pair.2) := by
  intro current before complete read joint prior
  dsimp only [joint, prior]
  simp only [PMF.map_bind, PMF.map_comp, bindPairLaw, PMF.bind_bind, PMF.bind_map,
    Function.comp_def]
  apply bind_congr_on_support
  intro entry _
  have law := earlier.prefixLaw_binding_readout fresh guard later suffix profile entry
  have tagged := congrArg (PMF.map fun pair => ((entry, pair.1), pair.2)) law
  simpa only [current, before, complete, read, PMF.map_comp, bindPairLaw, PMF.map_bind,
    PMF.bind_map, Function.comp_def] using tagged

/-- Observing the current owned view conditions the original entry and the
same complete word jointly. Its entry/result marginal retains the actual
entry posterior and the original next source kernel. -/
theorem prefixLaw_binding_entry_posterior
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (earlier : CommitPrefix Γ O Δ P)
    (later : CommitPrefix ((name, .commitment owner payload) :: Δ) (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (profile : BehavioralProfile
      (earlier.prepend (.commit name owner fresh guard (later.prepend suffix))))
    (entryLaw : PMF (Config Player L Γ)) (observed : DecisionView owner Δ)
    (present : observed ∈ ((entryLaw.bind fun entry =>
      earlier.prefixLaw (.commit name owner fresh guard (later.prepend suffix)) profile entry).map
        (Config.view owner)).support) :
    let current := earlier.tailProfile (.commit name owner fresh guard (later.prepend suffix))
      profile
    let before := fun entry => earlier.prefixLaw
      (.commit name owner fresh guard (later.prepend suffix)) profile entry
    let complete := fun entry => (before entry).bind fun config =>
      (CommitPrefix.commit name owner fresh guard later).prefixLaw suffix current config
    let read := fun config : Config Player L Ξ =>
      let view := later.entryView owner (config.view owner)
      (view.back true, (view.1.cells name (.commitment owner payload) .here).getD .failure)
    let joint := entryLaw.bind fun entry => (complete entry).map (Prod.mk entry)
    let prior := entryLaw.bind fun entry =>
      (before entry).map fun config => (entry, config.view owner)
    (fiberPosterior joint (fun pair => (read pair.2).1) observed).map
        (fun pair => (pair.1, (read pair.2).2)) =
      bindPairLaw ((fiberPosterior prior Prod.snd observed).map Prod.fst)
        (fun _ => commitKernel current observed) := by
  intro current before complete read joint prior
  let tagged := fun pair : Config Player L Γ × Config Player L Ξ =>
    ((pair.1, (read pair.2).1), (read pair.2).2)
  have law : joint.map tagged = bindPairLaw prior (fun pair => commitKernel current pair.2) :=
    earlier.prefixLaw_binding_entry_readout fresh guard later suffix profile entryLaw
  have priorPresent : observed ∈ (prior.map Prod.snd).support := by
    simpa only [prior, PMF.map_bind, PMF.map_comp, Function.comp_def] using present
  have observation : joint.map (fun pair => (read pair.2).1) = prior.map Prod.snd := by
    have marginal := congrArg (fun pmf => (pmf.map Prod.fst).map Prod.snd) law
    rw [bindPairLaw_map_fst] at marginal
    simpa only [PMF.map_comp, Function.comp_def, tagged] using marginal
  have jointPresent : observed ∈ (joint.map
      ((fun pair => pair.1.2) ∘ tagged)).support := by
    simpa only [Function.comp_def, tagged] using (observation.symm ▸ priorPresent)
  have moved := map_fiberPosterior_readout joint tagged (fun pair => pair.1.2) observed jointPresent
  have shifted := fiberPosterior_bind_of_observation prior
    (fun pair => (commitKernel current pair.2).map (Prod.mk pair)) Prod.snd
      (fun pair => pair.1.2)
      (by
        intro pair _ result supported
        obtain ⟨value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        rfl) observed priorPresent
  change fiberPosterior (bindPairLaw prior (fun pair => commitKernel current pair.2))
    (fun pair => pair.1.2) observed = _ at shifted
  rw [law, shifted] at moved
  have selected := congrArg (PMF.map (fun pair => (pair.1.1, pair.2))) moved
  simp only [PMF.map_comp, PMF.map_bind] at selected
  change (fiberPosterior joint (fun pair => (read pair.2).1) observed).map
    (fun pair => (pair.1, (read pair.2).2)) = _ at selected
  rw [selected, bindPairLaw, PMF.bind_map]
  apply bind_congr_on_support
  intro pair supported
  have same := (mem_support_fiberPosterior priorPresent supported).1
  simp only [Function.comp_def, same]

end Vegas.SourceProgram.CommitPrefix
