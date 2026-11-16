module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.BindingSourceObservation

@[expose] public section

/-! # Source checkpoints after private binding runs

Complete private binding runs restore the original source checkpoint from their exact
records, stores and public defaults. Intermediate cuts may contain foreign bindings
outside the current source prefix.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies}

theorem SourceCheckpoint.restore_binding_path
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (serviceGraph setup deps).layout Γ}
    {inputs : (serviceGraph setup deps).Inputs}
    (origin current ghost : (serviceGraph setup deps).Config) (start finish : Nat)
    (originReach : origin.Reachable inputs) (before : origin.cut.IsPrefix start)
    (currentPath : Relation.ReflTransGen EventGraph.Config.Step origin current)
    (ghostPath : Relation.ReflTransGen EventGraph.Config.Step origin ghost)
    (currentOrdered : current.cut.IsPrefix finish)
    (checkpoint : SourceCheckpoint setup source refs finish ghost)
    (bindings : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish →
      ∃ owner payload, (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (records : completionOf current = completionOf ghost)
    (ghostClean : ghost.NoBindingDefaults) :
    SourceCheckpoint setup source refs finish current := by
  have stores := store_eq_of_binding_paths origin current ghost start finish originReach before
    currentPath ghostPath currentOrdered checkpoint.ordered bindings records
  have histories : decodeHistory setup.program current.history =
      decodeHistory setup.program ghost.history := by
    funext who
    change decodeCompletions setup.program
        ((serviceGraph setup deps).ownCompletions who current.history) =
      decodeCompletions setup.program ((serviceGraph setup deps).ownCompletions who ghost.history)
    rw [ownCompletions_eq_of_records relaxed current ghost (EventGraph.Config.Step.path_reachable
      currentPath originReach)
      (EventGraph.Config.Step.path_reachable ghostPath originReach) records who]
  have currentClean : current.NoBindingDefaults := by
    intro record member owner payload binding
    have found := (completionOf_eq_some_iff current record.event record).mpr ⟨member, rfl⟩
    rw [records] at found
    exact ghostClean record ((completionOf_eq_some_iff ghost record.event record).mp found).1
      owner payload binding
  have currentDefaults := defaults_of_binding_path origin current start finish currentPath before
    currentOrdered bindings currentClean
  have ghostDefaults := defaults_of_binding_path origin ghost start finish ghostPath before
    checkpoint.ordered bindings ghostClean
  have defaults : current.defaults = ghost.defaults :=
    congrArg DefaultHistory.mk (currentDefaults.trans ghostDefaults.symm)
  refine ⟨?_, histories.trans checkpoint.history, defaults.trans checkpoint.defaults,
    currentOrdered⟩
  rw [stores]
  exact checkpoint.agrees

private theorem defaults_events_eq_replicate_of_clear
    {graph : Vegas.EventGraph Player L} (config : graph.Config) {rank : Nat}
    (ordered : config.cut.IsPrefix rank) (clear : config.defaulted = ∅) :
    config.defaults.events = List.replicate rank none := by
  have entries : config.history.map EventCompletion.defaultEvent =
      List.replicate config.history.length none := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp, ?_⟩
    intro event member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    cases recorded : record.defaultEvent with
    | none => rfl
    | some who =>
        have found := (completionOf_eq_some_iff config record.event record).mpr ⟨present, rfl⟩
        have defaulted : who ∈ config.defaulted :=
          (mem_defaulted_iff_completionOf config who).mpr ⟨record.event, by
            rw [found]; exact recorded⟩
        simp only [clear, Finset.notMem_empty] at defaulted
  change (config.history.map EventCompletion.defaultEvent).reverse = List.replicate rank none
  rw [entries, List.reverse_replicate, Config.history_length_of_isPrefix config ordered]

/-- A reachable clear source checkpoint transports along the complete order-free graph key.
The completion chronology may differ. -/
theorem SourceCheckpoint.of_runKey
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (serviceGraph setup deps).layout Γ} {rank : Nat}
    {left right : (serviceGraph setup deps).Config}
    {leftInputs rightInputs : (serviceGraph setup deps).Inputs}
    (leftReach : left.Reachable leftInputs) (rightReach : right.Reachable rightInputs)
    (clear : left.defaulted = ∅) (same : runKey left = runKey right)
    (checkpoint : SourceCheckpoint setup source refs rank right) :
    SourceCheckpoint setup source refs rank left := by
  have cuts : left.cut = right.cut := congrArg Prod.fst same
  have stores : left.store = right.store := congrArg (fun key => key.2.1) same
  have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
  have ordered : left.cut.IsPrefix rank := cuts.symm ▸ checkpoint.ordered
  have rightClear : right.defaulted = ∅ :=
    (defaulted_eq_of_completionOf_eq records).symm.trans clear
  have histories : decodeHistory setup.program left.history =
      decodeHistory setup.program right.history := by
    funext who
    change decodeCompletions setup.program
      ((serviceGraph setup deps).ownCompletions who left.history) =
      decodeCompletions setup.program ((serviceGraph setup deps).ownCompletions who right.history)
    rw [ownCompletions_eq_of_records relaxed left right leftReach rightReach records who]
  have defaults : left.defaults = right.defaults := by
    apply congrArg DefaultHistory.mk
    exact (defaults_events_eq_replicate_of_clear left ordered clear).trans
      (defaults_events_eq_replicate_of_clear right checkpoint.ordered rightClear).symm
  refine ⟨?_, histories.trans checkpoint.history, defaults.trans checkpoint.defaults, ordered⟩
  rw [stores]
  exact checkpoint.agrees

end Vegas
