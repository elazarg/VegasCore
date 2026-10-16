/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixProduct
import Vegas.Source.CommitPrefixWord
import GameTheory.Math.Probability.ConditionalObservation

/-! # Latent block words after observing partial owner histories -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}

open Classical in
/-- Completing a source block conditional on observed prefixes of each
owner's actual word preserves the original ownerwise kernels. Missing future
choices are drawn inside each complete chronological owner marginal. -/
theorem prefixLaw_history_prefix_product (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entry : Config Player L Γ) (observed : History Player L)
    (present : ∃ final ∈ (block.prefixLaw suffix profile entry).support,
      ∀ who, (observed who).IsPrefix (final.history who)) :
    fiberPosterior ((block.prefixLaw suffix profile entry).map Config.history)
        (fun words => decide (∀ who, (observed who).IsPrefix (words who))) true =
      independentProduct (fun who =>
        fiberPosterior ((block.prefixLaw suffix profile entry).map (fun final => final.history who))
          (fun word => decide ((observed who).IsPrefix word)) true) := by
  classical
  let laws := fun who => (block.prefixLaw suffix profile entry).map
    (fun final => final.history who)
  let restriction := fun who => {word : List (OwnAction Player L) | (observed who).IsPrefix word}
  have coordinate (who : Player) : ∃ word ∈ restriction who, word ∈ (laws who).support := by
    obtain ⟨final, supported, compatible⟩ := present
    exact ⟨final.history who, compatible who,
      (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩⟩
  have rect : ∃ words ∈ Set.pi Set.univ restriction,
      words ∈ (independentProduct laws).support := by
    obtain ⟨final, supported, compatible⟩ := present
    refine ⟨final.history, fun who _ => compatible who, ?_⟩
    rw [← block.prefixLaw_histories_product suffix profile entry]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
  have conditional (who : Player) :
      fiberPosterior (laws who) (fun word => decide ((observed who).IsPrefix word)) true =
        (laws who).filter (restriction who) (coordinate who) := by
    have meets : ∃ word ∈ {word | decide ((observed who).IsPrefix word) = true},
        word ∈ (laws who).support := by
      simpa only [Set.mem_ofPred_eq, decide_eq_true_eq, restriction] using coordinate who
    simpa only [decide_eq_true_eq] using fiberPosterior_eq_filter (laws who)
      (fun word => decide ((observed who).IsPrefix word)) meets
  have total : fiberPosterior (independentProduct laws)
        (fun words => decide (∀ who, (observed who).IsPrefix (words who))) true =
      (independentProduct laws).filter (Set.pi Set.univ restriction) rect := by
    have meets : ∃ words ∈ {words | decide (∀ who,
        (observed who).IsPrefix (words who)) = true},
        words ∈ (independentProduct laws).support := by
      obtain ⟨words, belongs, supported⟩ := rect
      exact ⟨words, by simpa only [Set.mem_ofPred_eq, decide_eq_true_eq, restriction] using
        (fun who => belongs who (Set.mem_univ who)), supported⟩
    have same : {words | decide (∀ who, (observed who).IsPrefix (words who)) = true} =
        Set.pi Set.univ restriction := by
      ext words
      simp only [Set.mem_ofPred_eq, decide_eq_true_eq, Set.mem_pi, Set.mem_univ, forall_true_left,
        restriction]
    rw [fiberPosterior_eq_filter _ _ meets]
    simp only [same]
  rw [block.prefixLaw_histories_product suffix profile entry]
  change fiberPosterior (independentProduct laws) _ true = independentProduct
    (fun who => fiberPosterior (laws who) (fun word => decide ((observed who).IsPrefix word)) true)
  rw [total]
  simp_rw [conditional]
  exact filter_independentProduct laws restriction coordinate

/-- Conditioning on the focal player's current view changes only that player's
complete word marginal. Foreign complete words retain their original product
law, while the focal player's unseen suffix remains sampled chronologically.
The source entry is fixed throughout this equality. -/
theorem prefixLaw_focal_view_product (earlier : CommitPrefix Γ O Δ P)
    (later : CommitPrefix Δ P Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (profile : BehavioralProfile (earlier.prepend (later.prepend suffix)))
    (entry : Config Player L Γ) (who : Player) (observed : DecisionView who Δ)
    (present : observed ∈ ((earlier.prefixLaw (later.prepend suffix) profile entry).map
      (Config.view who)).support) :
    let current := earlier.tailProfile (later.prepend suffix) profile
    let before := earlier.prefixLaw (later.prepend suffix) profile entry
    let complete := before.bind (later.prefixLaw suffix current)
    let own := complete.map (Config.view who)
    let foreign := independentProduct (fun other : {other : Player // other ≠ who} =>
      complete.map (Config.view other.val))
    (fiberPosterior complete (fun final => later.entryView who (final.view who)) observed).map
        (fun final => (final.view who, fun other : {other : Player // other ≠ who} =>
          final.view other.val)) =
      (fiberPosterior own (later.entryView who) observed).bind
        (fun word => foreign.map (Prod.mk word)) := by
  classical
  intro current before complete own foreign
  let fullProfile := cast (congrArg BehavioralProfile
    (earlier.prepend_append later suffix).symm) profile
  have fullLaw : (earlier.append later).prefixLaw suffix fullProfile entry = complete := by
    simpa only [fullProfile, cast_cast, cast_eq] using
      earlier.prefixLaw_append later suffix fullProfile entry
  have product := (earlier.append later).prefixLaw_views_product suffix fullProfile entry
  rw [fullLaw] at product
  let read := fun final : Config Player L Ξ =>
    (final.view who, fun other : {other : Player // other ≠ who} => final.view other.val)
  let observe := fun pair : DecisionView who Ξ ×
    (∀ other : {other : Player // other ≠ who}, DecisionView other.val Ξ) =>
      later.entryView who pair.1
  have paired : complete.map read = own.bind (fun word => foreign.map (Prod.mk word)) := by
    have split := congrArg (fun law => law.map
      (Equiv.piSplitAt who (fun owner => DecisionView owner Ξ))) product
    rw [independentProduct_splitAt _ who] at split
    simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, Equiv.apply_symm_apply,
      Equiv.piSplitAt_apply, read, own, foreign] using split
  have marginal : own.map (later.entryView who) = before.map (Config.view who) := by
    change ((before.bind (later.prefixLaw suffix current)).map
      (Config.view who)).map (later.entryView who) = _
    rw [PMF.map_bind, PMF.map_bind]
    simp_rw [later.prefixLaw_entryView suffix current]
    exact (PMF.bind_pure_comp _ _).symm
  have ownPresent : observed ∈ (own.map (later.entryView who)).support := by
    rwa [marginal]
  have fullPresent : observed ∈ (complete.map (observe ∘ read)).support := by
    simpa only [own, PMF.map_comp, Function.comp_def, observe, read] using ownPresent
  have moved := map_fiberPosterior_readout complete read observe observed fullPresent
  change (fiberPosterior complete (fun final => later.entryView who (final.view who))
    observed).map read = _ at moved
  rw [moved, paired]
  exact fiberPosterior_bind_of_observation own (fun word => foreign.map (Prod.mk word))
    (later.entryView who) observe (by
      intro word _ pair supported
      obtain ⟨rest, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      rfl) observed ownPresent

/-- With a correlated entry mixture, observing the current focal view retains
the posterior of the original entry jointly with the focal complete word.
Foreign complete words are then drawn from their original product at that
same retained entry, rather than from an entry-independent marginal. -/
theorem prefixLaw_focal_view_entry_product (earlier : CommitPrefix Γ O Δ P)
    (later : CommitPrefix Δ P Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (profile : BehavioralProfile (earlier.prepend (later.prepend suffix)))
    (entryLaw : PMF (Config Player L Γ)) (who : Player) (observed : DecisionView who Δ)
    (present : observed ∈ ((entryLaw.bind fun entry =>
      earlier.prefixLaw (later.prepend suffix) profile entry).map (Config.view who)).support) :
    let current := earlier.tailProfile (later.prepend suffix) profile
    let complete := fun entry =>
      (earlier.prefixLaw (later.prepend suffix) profile entry).bind
        (later.prefixLaw suffix current)
    let original := entryLaw.bind fun entry => (complete entry).map (Prod.mk entry)
    let own := entryLaw.bind fun entry =>
      ((complete entry).map (Config.view who)).map (Prod.mk entry)
    let foreign := fun entry => independentProduct
      (fun other : {other : Player // other ≠ who} => (complete entry).map (Config.view other.val))
    (fiberPosterior original
      (fun pair => later.entryView who (pair.2.view who)) observed).map
        (fun pair => ((pair.1, pair.2.view who),
          fun other : {other : Player // other ≠ who} => pair.2.view other.val)) =
      (fiberPosterior own (fun pair => later.entryView who pair.2) observed).bind
        (fun pair => (foreign pair.1).map (Prod.mk pair)) := by
  classical
  intro current complete original own foreign
  let fullProfile := cast (congrArg BehavioralProfile
    (earlier.prepend_append later suffix).symm) profile
  have fullLaw (entry : Config Player L Γ) :
      (earlier.append later).prefixLaw suffix fullProfile entry = complete entry := by
    simpa only [fullProfile, cast_cast, cast_eq] using
      earlier.prefixLaw_append later suffix fullProfile entry
  let read := fun pair : Config Player L Γ × Config Player L Ξ =>
    ((pair.1, pair.2.view who),
      fun other : {other : Player // other ≠ who} => pair.2.view other.val)
  let observe := fun pair : (Config Player L Γ × DecisionView who Ξ) ×
    (∀ other : {other : Player // other ≠ who}, DecisionView other.val Ξ) =>
      later.entryView who pair.1.2
  have paired : original.map read = own.bind
      (fun pair => (foreign pair.1).map (Prod.mk pair)) := by
    simp only [original, own, PMF.map_bind, PMF.map_comp, PMF.bind_bind, PMF.bind_map]
    apply bind_congr_on_support
    intro entry _
    have product := (earlier.append later).prefixLaw_views_product suffix fullProfile entry
    rw [fullLaw] at product
    have split := congrArg (fun law => law.map
      (Equiv.piSplitAt who (fun owner => DecisionView owner Ξ))) product
    rw [independentProduct_splitAt _ who] at split
    simp only [PMF.map_comp, PMF.map_bind, Function.comp_def,
      Equiv.apply_symm_apply, Equiv.piSplitAt_apply] at split
    have tagged := congrArg (PMF.map fun pair => ((entry, pair.1), pair.2)) split
    simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def,
      foreign, read] using tagged
  have marginal : own.map (fun pair => later.entryView who pair.2) =
      (entryLaw.bind fun entry => earlier.prefixLaw (later.prepend suffix) profile entry).map
        (Config.view who) := by
    simp only [own, PMF.map_bind, PMF.map_comp, Function.comp_def]
    apply bind_congr_on_support
    intro entry _
    change (complete entry).map (later.entryView who ∘ Config.view who) = _
    rw [← PMF.map_comp]
    dsimp only [complete]
    rw [PMF.map_bind, PMF.map_bind]
    simp_rw [later.prefixLaw_entryView suffix current]
    exact (PMF.bind_pure_comp _ _).symm
  have ownPresent : observed ∈
      (own.map (fun pair => later.entryView who pair.2)).support := by
    rwa [marginal]
  have fullPresent : observed ∈ (original.map (observe ∘ read)).support := by
    simpa only [original, own, PMF.map_bind, PMF.map_comp, Function.comp_def,
      observe, read] using ownPresent
  have moved := map_fiberPosterior_readout original read observe observed fullPresent
  change (fiberPosterior original (fun pair => later.entryView who (pair.2.view who))
    observed).map read = _ at moved
  rw [moved, paired]
  exact fiberPosterior_bind_of_observation own
    (fun pair => (foreign pair.1).map (Prod.mk pair))
    (fun pair => later.entryView who pair.2) observe (by
      intro pair _ result supported
      obtain ⟨rest, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      rfl) observed ownPresent

end Vegas.SourceProgram.CommitPrefix
