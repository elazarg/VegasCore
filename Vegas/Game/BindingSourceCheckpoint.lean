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

end Vegas
