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

private theorem commitKernel_cast_tail
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    {first second : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name O)} (same : first = second)
    (profile : BehavioralProfile (.commit name owner fresh guard first))
    (view : DecisionView owner Γ) :
    commitKernel (cast (congrArg BehavioralProfile
      (congrArg (SourceProgram.commit name owner fresh guard) same)) profile) view =
      commitKernel profile view := by
  cases same
  rfl

theorem afterCommit_cast_tail
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    {first second : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name O)} (same : first = second)
    (profile : BehavioralProfile (.commit name owner fresh guard first)) :
    afterCommit (cast (congrArg BehavioralProfile
      (congrArg (SourceProgram.commit name owner fresh guard) same)) profile) =
      cast (congrArg BehavioralProfile same) (afterCommit profile) := by
  cases same
  rfl

/-- Sampling concatenated commitment telescopes is exactly chronological
sampling of the earlier telescope followed by the later one at its updated
configuration and residual profile. Repeated owners retain their full past. -/
theorem prefixLaw_append (earlier : CommitPrefix Γ O Δ P) (later : CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (profile : BehavioralProfile ((earlier.append later).prepend suffix))
    (entry : Config Player L Γ) :
    (earlier.append later).prefixLaw suffix profile entry =
      let split := cast (congrArg BehavioralProfile (earlier.prepend_append later suffix)) profile
      (earlier.prefixLaw (later.prepend suffix) split entry).bind
        (later.prefixLaw suffix (earlier.tailProfile (later.prepend suffix) split)) := by
  induction earlier with
  | nil => simp only [append, prepend, prefixLaw, tailProfile, cast_eq, PMF.pure_bind]
  | commit name owner fresh guard rest ih =>
      have transported :
          cast (congrArg BehavioralProfile
            ((CommitPrefix.commit name owner fresh guard rest).prepend_append later suffix))
            profile = cast (congrArg BehavioralProfile
              (congrArg (SourceProgram.commit name owner fresh guard)
                (rest.prepend_append later suffix))) profile := rfl
      rw [transported]
      simp only [append, prefixLaw, tailProfile, PMF.bind_bind]
      have head := commitKernel_cast_tail fresh guard (rest.prepend_append later suffix) profile
        (entry.view owner)
      have tail := afterCommit_cast_tail fresh guard (rest.prepend_append later suffix) profile
      rw [head, tail]
      apply bind_congr_on_support _
      intro result _
      exact ih later (afterCommit profile) (commitSuccessor name guard entry result)

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Concatenating commitment telescopes adds their static lengths. -/
theorem length_append (earlier : CommitPrefix Γ O Δ P) (later : CommitPrefix Δ P Ξ Q) :
    (earlier.append later).length = earlier.length + later.length := by
  induction earlier with
  | nil => simp only [append, length, Nat.zero_add]
  | commit _ _ _ _ _ ih => simp only [append, length, ih]; omega

omit [IExpr.ResultTypes L] in
/-- Recovering an earlier view discards the later telescope first, retaining
the same complete earlier own history even when owners repeat. -/
theorem entryView_append (earlier : CommitPrefix Γ O Δ P) (later : CommitPrefix Δ P Ξ Q)
    (who : Player) (view : DecisionView who Ξ) :
    (earlier.append later).entryView who view =
      earlier.entryView who (later.entryView who view) := by
  induction earlier with
  | nil => rfl
  | commit _ _ _ _ _ ih => simp only [append, entryView, ih]

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
/-- An addressed action in the earlier telescope reads the same original
typed result after discarding the later owned view. -/
theorem wordAction_append_prefix (earlier : CommitPrefix Γ O Δ P)
    (later : CommitPrefix Δ P Ξ Q) (who : Player) (index : Nat)
    (view : DecisionView who Ξ) (bounded : index < earlier.length) :
    (earlier.append later).wordAction who index view =
      earlier.wordAction who index (later.entryView who view) := by
  induction earlier generalizing index with
  | nil => simp only [length] at bounded; omega
  | commit _ _ _ _ rest ih =>
    cases index with
    | zero => simp only [append, wordAction, entryView_append]
    | succ index =>
      simp only [append, wordAction]
      exact ih later index (by simpa only [length, Nat.succ_lt_succ_iff] using bounded)

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
