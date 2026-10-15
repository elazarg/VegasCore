/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixProduct
import GameTheory.Math.Probability.Conditioning

/-! # Latent block words after observing partial owner histories -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

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

end Vegas.SourceProgram.CommitPrefix
