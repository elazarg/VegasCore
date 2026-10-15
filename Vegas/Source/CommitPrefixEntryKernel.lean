/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixProduct
import GameTheory.Math.Probability.ConditionalObservation

/-! # Complete owned words sampled from observable entry views

The original entry law stays joint with the completed source word. Each owner
can draw its complete word using only its own entry view. Repeated decisions
remain those of the existing chronological source prefix law.
-/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- Condition the original entry law on the observed owned entry view, then
use the existing full chronological block law. No foreign entry cell is an
input of this kernel. Its impossible-view branch remains total. -/
def ownedEntryWordKernel (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entryLaw : PMF (Config Player L Γ)) (who : Player) (observed : DecisionView who Γ) :
    PMF (DecisionView who Δ) :=
  ((fiberPosterior entryLaw (Config.view who) observed).bind
    (block.prefixLaw suffix profile)).map (Config.view who)

/-- At every supported original entry, the observable-entry kernel is exactly
the original complete owned-word marginal at that entry. Other private entry
cells are integrated out without altering the owner's sequential kernels. -/
theorem ownedEntryWordKernel_at_entry (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entryLaw : PMF (Config Player L Γ)) (entry : Config Player L Γ)
    (supported : entry ∈ entryLaw.support) (who : Player) :
    block.ownedEntryWordKernel suffix profile entryLaw who (entry.view who) =
      (block.prefixLaw suffix profile entry).map (Config.view who) := by
  have present : entry.view who ∈ (entryLaw.map (Config.view who)).support :=
    (PMF.mem_support_map_iff ..).mpr ⟨entry, supported, rfl⟩
  rw [ownedEntryWordKernel, PMF.map_bind]
  calc
    _ = (fiberPosterior entryLaw (Config.view who) (entry.view who)).bind
        (fun _ => (block.prefixLaw suffix profile entry).map (Config.view who)) := by
      apply bind_congr_on_support _
      intro other member
      exact block.prefixLaw_view_eq suffix profile profile who rfl other entry
        (mem_support_fiberPosterior present member).1
    _ = _ := PMF.bind_const _ _

variable [Fintype Player]

/-- Sampling every owner's complete word through its observable entry-view
kernel reconstructs the exact original joint entry/full-word law. Independence
is conditional on the retained entry; the entry mixture is never factored. -/
theorem prefixLaw_entry_word_kernels (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entryLaw : PMF (Config Player L Γ)) :
    (entryLaw.bind fun entry => (block.prefixLaw suffix profile entry).map
      (fun final => (entry, fun who => final.view who))) =
      entryLaw.bind (fun entry =>
        (independentProduct (fun who =>
          block.ownedEntryWordKernel suffix profile entryLaw who (entry.view who))).map
            (fun words => (entry, words))) := by
  apply bind_congr_on_support _
  intro entry supported
  have kernels : independentProduct (fun who =>
        block.ownedEntryWordKernel suffix profile entryLaw who (entry.view who)) =
      independentProduct (fun who =>
        (block.prefixLaw suffix profile entry).map (Config.view who)) := by
    apply congrArg independentProduct
    funext who
    exact block.ownedEntryWordKernel_at_entry suffix profile entryLaw entry supported who
  rw [kernels, ← block.prefixLaw_views_product suffix profile entry, PMF.map_comp]
  rfl

end Vegas.SourceProgram.CommitPrefix
