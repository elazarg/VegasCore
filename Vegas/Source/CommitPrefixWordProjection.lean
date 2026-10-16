/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixWordHistory
import Vegas.Source.CommitPrefixWordRecall

/-! # Earlier source information retained by a complete chronological word -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}

private theorem entryView_of_supported (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entry : Config Player L Γ) (who : Player) (final : Config Player L Δ)
    (supported : final ∈ (block.prefixLaw suffix profile entry).support) :
    block.entryView who (final.view who) = entry.view who := by
  have present : block.entryView who (final.view who) ∈
      (((block.prefixLaw suffix profile entry).map (Config.view who)).map
        (block.entryView who)).support := by
    exact (PMF.mem_support_map_iff ..).mpr ⟨final.view who,
      (PMF.mem_support_map_iff ..).mpr ⟨final, supported, rfl⟩, rfl⟩
  rw [block.prefixLaw_entryView] at present
  exact (PMF.mem_support_pure_iff ..).mp present

/-- A complete chronological word projects to exactly the original earlier
prefix law. Later repeated-owner choices are sampled at updated views and
then forgotten by the actual source entry-view map. -/
theorem prefixLaw_split_entryView (earlier : CommitPrefix Γ O Δ P)
    (later : CommitPrefix Δ P Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (profile : BehavioralProfile (earlier.prepend (later.prepend suffix)))
    (entry : Config Player L Γ) (who : Player) :
    let current := earlier.tailProfile (later.prepend suffix) profile
    let before := earlier.prefixLaw (later.prepend suffix) profile entry
    let complete := before.bind (later.prefixLaw suffix current)
    (complete.map (Config.view who)).map (later.entryView who) = before.map (Config.view who) := by
  intro current before complete
  calc
    _ = before.bind (fun point => PMF.pure (point.view who)) := by
      rw [PMF.map_comp, PMF.map_bind]
      apply bind_congr_on_support
      intro point _supported
      have projection := later.prefixLaw_entryView suffix current point who
      rw [PMF.map_comp] at projection
      exact projection
    _ = _ := PMF.bind_pure_comp _ _

/-- On the original chronological source prior, all earlier addressed owned
actions determine the full earlier source view. This retains foreign failed
values and all repeated-owner dependence in the unconditioned complete law. -/
theorem prefixLaw_split_entryView_iff_wordActions
    (earlier : CommitPrefix Γ O Δ P) (later : CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (profile : BehavioralProfile (earlier.prepend (later.prepend suffix)))
    (entry : Config Player L Γ) (who : Player) (left right : DecisionView who Ξ) :
    let current := earlier.tailProfile (later.prepend suffix) profile
    let before := earlier.prefixLaw (later.prepend suffix) profile entry
    let prior := (before.bind (later.prefixLaw suffix current)).map (Config.view who)
    left ∈ prior.support → right ∈ prior.support →
    (later.entryView who left = later.entryView who right ↔
      ∀ index < earlier.length, (earlier.append later).wordAction who index left =
        (earlier.append later).wordAction who index right) := by
  intro current before prior leftSupported rightSupported
  constructor
  · intro same index bounded
    rw [wordAction_append_prefix earlier later who index left bounded,
      wordAction_append_prefix earlier later who index right bounded, same]
  · intro same
    obtain ⟨leftFinal, leftDrawn, leftView⟩ := (PMF.mem_support_map_iff ..).mp leftSupported
    obtain ⟨rightFinal, rightDrawn, rightView⟩ := (PMF.mem_support_map_iff ..).mp rightSupported
    obtain ⟨leftPoint, leftBefore, leftTail⟩ := (PMF.mem_support_bind_iff ..).mp leftDrawn
    obtain ⟨rightPoint, rightBefore, rightTail⟩ := (PMF.mem_support_bind_iff ..).mp rightDrawn
    have leftCurrent : later.entryView who left = leftPoint.view who := by
      rw [← leftView]
      exact entryView_of_supported later suffix current leftPoint who leftFinal leftTail
    have rightCurrent : later.entryView who right = rightPoint.view who := by
      rw [← rightView]
      exact entryView_of_supported later suffix current rightPoint who rightFinal rightTail
    have actions : ∀ index < earlier.length,
        earlier.wordAction who index (leftPoint.view who) =
          earlier.wordAction who index (rightPoint.view who) := by
      intro index bounded
      have compared := same index bounded
      rw [wordAction_append_prefix earlier later who index left bounded,
        wordAction_append_prefix earlier later who index right bounded, leftCurrent, rightCurrent]
        at compared
      exact compared
    have leftHistory := earlier.prefixLaw_wordAction_history (later.prepend suffix) profile entry
      who leftPoint leftBefore
    have rightHistory := earlier.prefixLaw_wordAction_history (later.prepend suffix) profile entry
      who rightPoint rightBefore
    have sameHistory : leftPoint.history who = rightPoint.history who := by
      rw [leftHistory, rightHistory]
      apply congrArg (entry.history who ++ ·)
      apply List.filterMap_congr
      intro index bounded
      exact actions index (List.mem_range.mp bounded)
    rw [leftCurrent, rightCurrent]
    exact earlier.prefixLaw_view_eq_of_history_eq (later.prepend suffix) profile profile entry entry
      who rfl leftPoint rightPoint leftBefore rightBefore sameHistory

end Vegas.SourceProgram.CommitPrefix
