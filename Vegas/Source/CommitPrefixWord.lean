/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixReadout

/-! # Addressed actions in complete owned commitment words

A complete owned view determines the action at every owned static position.
The readout uses only that owner's cells and history. Distinct owners' complete
views are not combined into an observable input.
-/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}

/-- Concatenate two existing typed commitment telescopes. -/
def append : {Γ Δ Ξ : SourceCtx Player L} → {O P Q : Finset VarId} →
    CommitPrefix Γ O Δ P → CommitPrefix Δ P Ξ Q → CommitPrefix Γ O Ξ Q
  | _, _, _, _, _, _, .nil, later => later
  | _, _, _, _, _, _, .commit name owner fresh guard rest, later =>
      .commit name owner fresh guard (rest.append later)

theorem prepend_append (earlier : CommitPrefix Γ O Δ P) (later : CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q) :
    (earlier.append later).prepend suffix = earlier.prepend (later.prepend suffix) := by
  induction earlier with
  | nil => rfl
  | commit name owner fresh guard rest ih =>
      exact congrArg (SourceProgram.commit name owner fresh guard) (ih later)

/-- Read a static addressed action from one owner's complete word. Outside
the telescope or at a foreign-owned slot the readout is absent. -/
def wordAction : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    (block : CommitPrefix Γ O Δ P) → (who : Player) → Nat →
      DecisionView who Δ → Option (OwnAction Player L)
  | _, _, _, _, .nil, _, _, _ => none
  | _, _, _, _, .commit name owner _fresh _guard rest, who, index, view =>
      match index with
      | 0 => if owner = who then
          some (.commit owner name _
            (((rest.entryView who view).1.cells name (.commitment owner _) .here).getD .failure))
        else none
      | index + 1 => rest.wordAction who index view

omit [IExpr.ResultTypes L] in
/-- The selector is total on the complete word and uses the original source
name, payload and result at the selected owned position. -/
theorem wordAction_append_binding
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (earlier : CommitPrefix Γ O Δ P)
    (later : CommitPrefix ((name, .commitment owner payload) :: Δ) (insert name P) Ξ Q)
    (view : DecisionView owner Ξ) :
    (earlier.append (.commit name owner fresh guard later)).wordAction owner earlier.length view =
      some (.commit owner name payload
        (((later.entryView owner view).1.cells name (.commitment owner payload) .here).getD
          .failure)) := by
  induction earlier with
  | nil => simp only [append, length, wordAction, ite_true]
  | commit _ _ _ _ _ ih => exact ih fresh guard later

/-- Complete block conditioning can use only the owner's complete view,
rather than a memory containing foreign cells. Repeated owned choices remain
in the chronological source kernel at the reconstructed earlier view. -/
theorem prefixLaw_owned_word_conditional
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (earlier : CommitPrefix Γ O Δ P)
    (later : CommitPrefix ((name, .commitment owner payload) :: Δ) (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (profile : BehavioralProfile
      (earlier.prepend (.commit name owner fresh guard (later.prepend suffix))))
    (entry : Config Player L Γ) (observed : DecisionView owner Δ)
    (present : observed ∈ ((earlier.prefixLaw
      (.commit name owner fresh guard (later.prepend suffix)) profile entry).map
        (Config.view owner)).support) :
    let current := earlier.tailProfile (.commit name owner fresh guard (later.prepend suffix))
      profile
    let before := earlier.prefixLaw (.commit name owner fresh guard (later.prepend suffix))
      profile entry
    let complete := before.bind (fun config =>
      ((CommitPrefix.commit name owner fresh guard later).prefixLaw suffix current config))
    let beforeView := fun view : DecisionView owner Ξ => (later.entryView owner view).back true
    (fiberPosterior (complete.map (Config.view owner)) beforeView observed).map
      ((earlier.append (.commit name owner fresh guard later)).wordAction owner earlier.length) =
      (commitKernel current observed).map (fun result =>
        some (OwnAction.commit owner name payload result)) := by
  intro current before complete beforeView
  have next := earlier.prefixLaw_binding_conditional fresh guard later suffix profile entry
    observed present
  let read := fun config : Config Player L Ξ =>
    let view := later.entryView owner (config.view owner)
    (view.back true, (view.1.cells name (.commitment owner payload) .here).getD .failure)
  change (fiberPosterior complete (fun config => (read config).1) observed).map
    (fun config => (read config).2) = commitKernel current observed at next
  have marginal := congrArg (fun law => law.map Prod.fst)
    (earlier.prefixLaw_binding_readout fresh guard later suffix profile entry)
  rw [bindPairLaw_map_fst, PMF.map_comp] at marginal
  change complete.map (fun config => (read config).1) = before.map (Config.view owner)
    at marginal
  have possible : observed ∈ (complete.map (beforeView ∘ Config.view owner)).support := by
    change observed ∈ (complete.map (fun config => (read config).1)).support
    rw [marginal]
    exact present
  have moved := map_fiberPosterior_readout complete (Config.view owner) beforeView observed
    possible
  have selected := congrArg (fun law => law.map
    ((earlier.append (.commit name owner fresh guard later)).wordAction owner earlier.length))
      moved
  rw [PMF.map_comp] at selected
  rw [← selected]
  calc
    _ = ((fiberPosterior complete (fun config => (read config).1) observed).map
        (fun config => (read config).2)).map
          (fun result => some (OwnAction.commit owner name payload result)) := by
      rw [PMF.map_comp]
      apply congrArg (PMF.map · (fiberPosterior complete (fun config => (read config).1) observed))
      funext config
      exact wordAction_append_binding fresh guard earlier later (config.view owner)
    _ = _ := congrArg (PMF.map (fun result =>
      some (OwnAction.commit owner name payload result))) next

end Vegas.SourceProgram.CommitPrefix
