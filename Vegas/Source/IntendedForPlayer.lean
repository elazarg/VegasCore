/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.FailedBindingDeviation
import Vegas.Source.DisclosureAliases
import GameTheory.Math.Probability.Convergence

/-! # Play intended for one player

A configuration is intended for a player (`Vegas.SourceProgram.Config.IntendedFor`)
when names are unique, revelations are accounted, every commitment cell of the
player holds a value, the player's revealed commitments publish their bindings,
and every retained guard of the player is predicted to accept its subject's
binding. An intended configuration is intended for every player
(`Vegas.SourceProgram.Config.Intended.intendedFor`).

At a configuration intended for a player, the player's disclosure opens a value
(`Vegas.SourceProgram.Config.IntendedFor.reveal_own`): a reveal completes only
guards of the revealer, and their predictions are exact.

Every source step from a point intended for a player keeps it intended for the
player, or leaves the player owing a failed reveal
(`Vegas.SourceProgram.ProtocolState.intendedFor_step`): the player binds a
failure or a value its guard is predicted to reject, or withholds a reveal. So
being intended for a player or owing a failure is closed under every step
(`Vegas.SourceProgram.ProtocolState.intendedForOrOwes_step`), whatever the
other players do.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

variable {Γ : SourceCtx Player L}

omit [IExpr.ResultTypes L] in
/-- **A configuration intended for one player.** Unique names, accounted
revelations, a value in every commitment cell of the player, the player's
revealed commitments publishing their bindings, and every retained guard of the
player predicted to accept its subject's binding. -/
structure IntendedFor (who : Player) (unresolved : Finset VarId) (config : Config Player L Γ) :
    Prop where
  unique : (Γ.map Prod.fst).Nodup
  accounted : Accounted config.revelations unresolved
  bound : ∀ {x : VarId} {payload : L.Ty} (cell : HasVar Γ x (.commitment who payload)),
    ∃ value, config.state.get cell = .success value
  publishes : PublishesBindings who config.revelations config.state
  predicted : ∀ obligation ∈ config.registry, obligation.owner = who → ∀ value,
    config.state.get obligation.source = .success value →
      obligation.guard.predicts (sourceObserve obligation.owner config.state) value = true

variable {config : Config Player L Γ} {unresolved : Finset VarId} {who : Player}

omit [IExpr.ResultTypes L] in
/-- An intended configuration is intended for every player. -/
theorem Intended.intendedFor (intended : config.Intended unresolved) (who : Player) :
    config.IntendedFor who unresolved where
  unique := intended.unique
  accounted := intended.accounted
  bound cell := intended.bound cell
  publishes := intended.publishes who
  predicted obligation member _ value bound := intended.predicted obligation member value bound

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem unique_cons' {name : VarId} {cell : CellTy Player L}
    (fresh : name ∉ Γ.map Prod.fst) (unique : (Γ.map Prod.fst).Nodup) :
    (((name, cell) :: Γ).map Prod.fst).Nodup := by
  simp [fresh, unique]

omit [IExpr.ResultTypes L] in
private theorem IntendedFor.predicted_weaken {name : VarId} {cell : CellTy Player L}
    (intended : config.IntendedFor who unresolved) (head : CellVal L cell) :
    ∀ obligation ∈ (config.registry.weaken (x := name) (c := cell)), obligation.owner = who →
      ∀ value, (Env.cons head config.state).get obligation.source = .success value →
        obligation.guard.predicts
          (sourceObserve obligation.owner (Env.cons head config.state)) value = true := by
  intro obligation member own value bound
  obtain ⟨original, kept, rfl⟩ := List.mem_map.mp member
  exact (SourceGuard.predicts_weaken _ _ _ _).trans
    (intended.predicted original kept own value bound)

omit [IExpr.ResultTypes L] in
theorem IntendedFor.sample {name : VarId} {payload : L.Ty}
    (intended : config.IntendedFor who unresolved) (fresh : name ∉ Γ.map Prod.fst)
    (value : L.Val payload) :
    (sampleSuccessor name config value).IntendedFor who unresolved where
  unique := unique_cons' fresh intended.unique
  accounted :=
    Accounted.weaken_noncommitment (by intro _ _ equal; cases equal) intended.accounted
  bound cell := by
    cases cell with
    | there cell => exact intended.bound cell
  publishes := PublishesBindings.weaken _ intended.publishes
  predicted := intended.predicted_weaken _

omit [IExpr.ResultTypes L] in
/-- Another player's binding keeps a configuration intended for the player. -/
theorem IntendedFor.commit_other {name : VarId} {owner : Player} {payload : L.Ty}
    (intended : config.IntendedFor who unresolved) (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload) (different : owner ≠ who)
    (choice : PublicationResult (L.Val payload)) :
    (commitSuccessor name guard config choice).IntendedFor who (insert name unresolved) where
  unique := unique_cons' fresh intended.unique
  accounted := Accounted.commit fresh intended.accounted
  bound cell := by
    cases cell with
    | here => exact (different rfl).elim
    | there cell => exact intended.bound cell
  publishes := PublishesBindings.weaken _ intended.publishes
  predicted := by
    intro obligation member own bound bindsBound
    rcases List.mem_cons.mp member with rfl | member
    · exact (different own).elim
    · exact intended.predicted_weaken _ obligation member own bound bindsBound

omit [IExpr.ResultTypes L] in
/-- The player's binding of a value its guard is predicted to accept keeps the
configuration intended for the player. -/
theorem IntendedFor.commit_own {name : VarId} {payload : L.Ty}
    (intended : config.IntendedFor who unresolved) (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ who name payload) (value : L.Val payload)
    (accepted : guard.predicts (sourceObserve who config.state) value = true) :
    (commitSuccessor name guard config (.success value)).IntendedFor who
      (insert name unresolved) where
  unique := unique_cons' fresh intended.unique
  accounted := Accounted.commit fresh intended.accounted
  bound cell := by
    cases cell with
    | here => exact ⟨value, rfl⟩
    | there cell => exact intended.bound cell
  publishes := PublishesBindings.weaken _ intended.publishes
  predicted := by
    intro obligation member own bound bindsBound
    rcases List.mem_cons.mp member with rfl | member
    · cases bindsBound
      exact (SourceGuard.predicts_weaken _ _ _ _).trans accepted
    · exact intended.predicted_weaken _ obligation member own bound bindsBound

omit [IExpr.ResultTypes L] in
/-- The player's binding of a value its guard is predicted to reject leaves the
player indebted. -/
theorem IntendedFor.indebted_commit {name : VarId} {payload : L.Ty}
    (intended : config.IntendedFor who unresolved) (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ who name payload) (value : L.Val payload)
    (rejected : guard.predicts (sourceObserve who config.state) value = false) :
    (commitSuccessor name guard config (.success value)).Indebted who
      (insert name unresolved) where
  unique := unique_cons' fresh intended.unique
  accounted := Accounted.commit fresh intended.accounted
  publishes := PublishesBindings.weaken _ intended.publishes
  pending := ⟨Obligation.mk who name payload .here guard.weaken, List.mem_cons_self .., rfl,
    rfl, value, rfl, (SourceGuard.predicts_weaken _ _ _ _).trans rejected⟩

omit [IExpr.ResultTypes L] in
/-- The player's binding of a failure leaves the player with a failed
binding. -/
theorem IntendedFor.failedBinding_commit {name : VarId} {payload : L.Ty}
    (intended : config.IntendedFor who unresolved) (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ who name payload) :
    (commitSuccessor name guard config .failure).FailedBinding who (insert name unresolved) where
  unique := unique_cons' fresh intended.unique
  pending := ⟨name, payload, .here, Finset.mem_insert_self _ _, rfl⟩

omit [IExpr.ResultTypes L] in
/-- Every obligation a reveal of the player completes accepts the opened
binding. -/
theorem IntendedFor.completed_accept {payload : L.Ty} {name published : VarId}
    (intended : config.IntendedFor who unresolved)
    (source : HasVar Γ name (.commitment who payload)) :
    (Registry.completedBy (published := published) config.registry config.revelations
        source).all
      (·.accepts (Revelations.reveal (published := published) config.revelations source)
        (Env.cons (Val := CellVal (Player := Player) L) (x := published)
          (τ := .publication payload) (bindingOf config source) config.state)) = true := by
  refine List.all_eq_true.mpr fun completed member => ?_
  obtain ⟨original, filtered, rfl⟩ := List.mem_map.mp member
  have own : original.owner = who := Obligation.owner_eq_of_completedBy original
    config.revelations source (List.mem_filter.mp filtered).2
  subst own
  obtain ⟨value, bound⟩ := intended.bound original.source
  rw [Obligation.accepts_eq_predicts original.weaken _ _
    (Registry.revealed_of_mem_completedBy _ _ _ member)
    (PublishesBindings.reveal intended.unique source _ (fun _ => rfl) intended.publishes)
    (value := value) bound]
  exact (SourceGuard.predicts_weaken _ _ _ _).trans
    (intended.predicted original (List.mem_filter.mp filtered).1 rfl value bound)

omit [IExpr.ResultTypes L] in
/-- **The player's disclosure opens a value.** At a configuration intended for
the player, its disclosure publishes its binding, a value, and keeps the
configuration intended for the player. -/
theorem IntendedFor.reveal_own {payload : L.Ty} {name published : VarId}
    (intended : config.IntendedFor who unresolved) (fresh : published ∉ Γ.map Prod.fst)
    (source : HasVar Γ name (.commitment who payload)) :
    (revealSuccessor published source config true).IntendedFor who (unresolved.erase name) ∧
      ∃ value, (revealSuccessor published source config true).state.get .here =
        .success value := by
  obtain ⟨value, bound⟩ := intended.bound source
  have state : (revealSuccessor published source config true).state =
      Env.cons (Val := CellVal (Player := Player) L) (x := published)
        (τ := .publication payload) (bindingOf config source) config.state := by
    simp only [revealSuccessor, ↓reduceIte, intended.completed_accept source]
  refine ⟨{ unique := unique_cons' fresh intended.unique
            accounted := Accounted.reveal source intended.unique intended.accounted
            bound := ?_
            publishes := ?_
            predicted := ?_ }, value, ?_⟩
  · intro x σ cell
    cases cell with
    | there cell =>
        rw [state]
        exact intended.bound cell
  · rw [state]
    exact PublishesBindings.reveal intended.unique source _ (fun _ => rfl) intended.publishes
  · rw [state]
    exact intended.predicted_weaken _
  · rw [state]
    exact bound

omit [IExpr.ResultTypes L] in
/-- Another player's reveal keeps a configuration intended for the player. -/
theorem IntendedFor.reveal_other {owner : Player} {payload : L.Ty} {name published : VarId}
    (intended : config.IntendedFor who unresolved) (fresh : published ∉ Γ.map Prod.fst)
    (source : HasVar Γ name (.commitment owner payload)) (different : owner ≠ who)
    (disclose : Bool) :
    (revealSuccessor published source config disclose).IntendedFor who
      (unresolved.erase name) where
  unique := unique_cons' fresh intended.unique
  accounted := Accounted.reveal source intended.unique intended.accounted
  bound cell := by
    cases cell with
    | there cell => exact intended.bound cell
  publishes := PublishesBindings.reveal intended.unique source _
    (fun same => (different same).elim) intended.publishes
  predicted := intended.predicted_weaken _

end Config

namespace ProtocolState

/-- **A point intended for one player**: its current configuration is intended
for the player. -/
def IntendedFor (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Prop
  | _, _, .ret _ => fun config => Config.IntendedFor who ∅ config
  | _, O, .sample _ _ _ next => Sum.elim (Config.IntendedFor who O) (IntendedFor who next)
  | _, O, .commit _ _ _ _ next => Sum.elim (Config.IntendedFor who O) (IntendedFor who next)
  | _, O, .reveal _ _ _ _ _ _ next =>
      Sum.elim (Config.IntendedFor who O) (IntendedFor who next)

theorem intendedFor_entry {who : Player} {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ)
    (intended : config.IntendedFor who O) : IntendedFor who program (entry program config) := by
  cases program <;> exact intended

/-- A point of the intended game is intended for every player. -/
theorem intendedFor_of_intended (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    Intended program state → IntendedFor who program state
  | _, _, .ret _, _, intended => intended.intendedFor who
  | _, _, .sample _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact intended.1.intendedFor who
      | inr rest => exact intendedFor_of_intended who next rest intended
  | _, _, .commit _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact intended.1.intendedFor who
      | inr rest => exact intendedFor_of_intended who next rest intended
  | _, _, .reveal _ _ _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact intended.1.intendedFor who
      | inr rest => exact intendedFor_of_intended who next rest intended.2

/-- **Intended for a player or owing.** Every source step, whatever anyone plays,
from a point intended for a player keeps it intended for the player or leaves
the player owing a failed reveal. -/
theorem intendedFor_step (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → (target : ProtocolState program) →
    IntendedFor who program state → target ∈ (step program state joint).support →
      IntendedFor who program target ∨ OwesFailure who program target
  | _, _, .ret _, _, _, _, intended, reached => by
      rw [step, PMF.mem_support_pure_iff] at reached
      rw [reached]
      exact Or.inl intended
  | _, _, .sample _ fresh _ next, state, joint, target, intended, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          exact Or.inl (intendedFor_entry next _ (Config.IntendedFor.sample intended fresh value))
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact intendedFor_step who next rest joint after intended supported
  | _, _, .commit (payload := payload) name owner fresh guard next, state, joint, target,
      intended, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          generalize OwnAction.binding owner name payload (joint owner) = choice
          by_cases same : owner = who
          · subst same
            cases choice with
            | failure =>
                exact Or.inr (Or.inr (failedBinding_entry next _
                  (Config.IntendedFor.failedBinding_commit intended fresh guard)))
            | success value =>
                cases predicted : guard.predicts (sourceObserve owner config.state) value with
                | true =>
                    exact Or.inl (intendedFor_entry next _
                      (Config.IntendedFor.commit_own intended fresh guard value predicted))
                | false =>
                    exact Or.inr (Or.inl (indebted_entry next _
                      (Config.IntendedFor.indebted_commit intended fresh guard value predicted)))
          · exact Or.inl (intendedFor_entry next _
              (Config.IntendedFor.commit_other intended fresh guard same choice))
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact intendedFor_step who next rest joint after intended supported
  | _, _, .reveal published owner name fresh source _ next, state, joint, target, intended,
      reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          generalize OwnAction.disclosure (joint owner) = disclose
          by_cases same : owner = who
          · subst same
            cases disclose with
            | true =>
                exact Or.inl (intendedFor_entry next _
                  (Config.IntendedFor.reveal_own intended fresh source).1)
            | false =>
                refine Or.inr (Or.inl (Or.inl ⟨rfl, ?_⟩))
                rw [base_entry]
                exact disclosureResult_false published source _
          · exact Or.inl (intendedFor_entry next _
              (Config.IntendedFor.reveal_other intended fresh source same disclose))
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases intendedFor_step who next rest joint after intended supported with
            kept | indebted | failed
          · exact Or.inl kept
          · exact Or.inr (Or.inl (Or.inr indebted))
          · exact Or.inr (Or.inr (Or.inr failed))

/-- **Intended for a player or owing is closed under every step.** -/
theorem intendedForOrOwes_step (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program)
    (joint : Player → Option (OwnAction Player L)) (target : ProtocolState program)
    (holds : IntendedFor who program state ∨ OwesFailure who program state)
    (reached : target ∈ (step program state joint).support) :
    IntendedFor who program target ∨ OwesFailure who program target := by
  rcases holds with intended | owed
  · exact intendedFor_step who program state joint target intended reached
  · exact Or.inr (owesFailure_step who program state joint target owed reached)

end ProtocolState

end Vegas.SourceProgram
