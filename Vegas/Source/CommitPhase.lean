/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Semantics

/-! # Typed commit phases and their attempts

A phase is a contiguous commitment block of an actual source program. Active
commitments use the existing successor, with guard checks deferred to reveals.
An excluded owner's slot is filled automatically and records no owned action.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A typed telescope of consecutive source commitments. -/
inductive CommitPrefix : SourceCtx Player L → Finset VarId →
    SourceCtx Player L → Finset VarId → Type where
  | nil {Γ O} : CommitPrefix Γ O Γ O
  | commit {Γ O Δ P} (name : VarId) (owner : Player) {payload : L.Ty}
      (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
      (rest : CommitPrefix ((name, .commitment owner payload) :: Γ) (insert name O) Δ P) :
      CommitPrefix Γ O Δ P

namespace CommitPrefix

variable {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

def prepend : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    CommitPrefix Γ O Δ P → SourceProgram Player L Δ P → SourceProgram Player L Γ O
  | _, _, _, _, .nil, suffix => suffix
  | _, _, _, _, .commit name owner fresh guard rest, suffix =>
      .commit name owner fresh guard (rest.prepend suffix)

def length : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    CommitPrefix Γ O Δ P → Nat
  | _, _, _, _, .nil => 0
  | _, _, _, _, .commit _ _ _ _ rest => rest.length + 1

def owners : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    CommitPrefix Γ O Δ P → Finset Player
  | _, _, _, _, .nil => ∅
  | _, _, _, _, .commit _ owner _ _ rest => insert owner rest.owners

end CommitPrefix

/-- A commit phase stops before a sample, reveal, or return. -/
def IsCommitBoundary : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Prop
  | _, _, .commit _ _ _ _ _ => False
  | _, _, _ => True

/-- The maximal contiguous commitment block at a source program point. -/
structure CommitPhase {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) where
  context : SourceCtx Player L
  pending : Finset VarId
  suffix : SourceProgram Player L context pending
  block : CommitPrefix Γ O context pending
  reconstruct : block.prepend suffix = program
  boundary : IsCommitBoundary suffix

def commitPhase : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → CommitPhase program
  | _, _, .ret payoffs => ⟨_, _, .ret payoffs, .nil, rfl, trivial⟩
  | _, _, .sample name fresh law next =>
      ⟨_, _, .sample name fresh law next, .nil, rfl, trivial⟩
  | _, _, .reveal published owner name fresh source unresolved next =>
      ⟨_, _, .reveal published owner name fresh source unresolved next, .nil, rfl, trivial⟩
  | _, _, .commit name owner fresh guard next =>
      let later := commitPhase next
      ⟨later.context, later.pending, later.suffix,
        .commit name owner fresh guard later.block,
        congrArg (SourceProgram.commit name owner fresh guard) later.reconstruct, later.boundary⟩

/-- An excluded slot has no binding and no new guard obligation or owned choice. -/
def automaticCommit {Γ : SourceCtx Player L} (name : VarId) (owner : Player)
    (payload : L.Ty) (config : Config Player L Γ) :
    Config Player L ((name, .commitment owner payload) :: Γ) :=
  ⟨Env.cons .failure config.state, Registry.weaken config.registry,
    Revelations.weaken config.revelations, config.history⟩

/-- Only an actual missing binding excludes an active owner. A received but
unusable binding may have a failed typed value without being a public miss. -/
def excludeCommit (excluded : Finset Player) (owner : Player) (missed : Bool) : Finset Player :=
  if missed then insert owner excluded else excluded

namespace CommitPrefix

variable {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

def automatic : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    CommitPrefix Γ O Δ P → Config Player L Γ → Config Player L Δ
  | _, _, _, _, .nil, config => config
  | _, _, _, _, .commit name owner _ _ rest, config =>
      rest.automatic (automaticCommit name owner _ config)

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem automatic_history (block : CommitPrefix Γ O Δ P) (config : Config Player L Γ) :
    (block.automatic config).history = config.history := by
  induction block with
  | nil => rfl
  | commit _ _ _ _ rest ih => exact ih _

/-- A completed phase attempt executes precisely its source commitment slots.
The physical miss flag is separate from its typed result: accepted unusable
bindings retain their failed value without excluding the owner at commitment.
New exclusions affect later slots internally. -/
inductive Attempt : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    CommitPrefix Γ O Δ P → Config Player L Γ → Finset Player →
      Config Player L Δ → Finset Player → Type where
  | nil {Γ : SourceCtx Player L} {O : Finset VarId}
      (config : Config Player L Γ) (excluded : Finset Player) :
      Attempt (.nil (O := O)) config excluded config excluded
  | active {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
      {name : VarId} {owner : Player} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
      {guard : SourceGuard L Γ owner name payload}
      {rest : CommitPrefix ((name, .commitment owner payload) :: Γ) (insert name O) Δ P}
      {config : Config Player L Γ} {excluded : Finset Player}
      {finished : Config Player L Δ} {afterExcluded : Finset Player}
      (active : owner ∉ excluded) (choice : PublicationResult (L.Val payload))
      (missed : Bool) (missingFailure : missed = true → choice = .failure)
      (later : Attempt rest (commitSuccessor name guard config choice)
        (excludeCommit excluded owner missed) finished afterExcluded) :
      Attempt (.commit name owner fresh guard rest) config excluded finished afterExcluded
  | excluded {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
      {name : VarId} {owner : Player} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
      {guard : SourceGuard L Γ owner name payload}
      {rest : CommitPrefix ((name, .commitment owner payload) :: Γ) (insert name O) Δ P}
      {config : Config Player L Γ} {excluded : Finset Player}
      {finished : Config Player L Δ} {afterExcluded : Finset Player}
      (inactive : owner ∈ excluded)
      (later : Attempt rest (automaticCommit name owner payload config) excluded
        finished afterExcluded) :
      Attempt (.commit name owner fresh guard rest) config excluded finished afterExcluded

namespace Attempt

variable {block : CommitPrefix Γ O Δ P} {entry : Config Player L Γ}
  {excluded : Finset Player} {finished : Config Player L Δ} {afterExcluded : Finset Player}

def failedOwners : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    {block : CommitPrefix Γ O Δ P} → {entry : Config Player L Γ} →
    {excluded : Finset Player} → {finished : Config Player L Δ} →
    {afterExcluded : Finset Player} → Attempt block entry excluded finished afterExcluded →
      Finset Player
  | _, _, _, _, _, _, _, _, _, .nil _ _ => ∅
  | _, _, _, _, _, _, _, _, _, .active (owner := owner) _ _ missed _ later =>
      if missed then insert owner later.failedOwners else later.failedOwners
  | _, _, _, _, _, _, _, _, _, .excluded _ later => later.failedOwners

omit [IExpr.ResultTypes L] in
theorem excluded_eq (attempt : Attempt block entry excluded finished afterExcluded) :
    afterExcluded = excluded ∪ attempt.failedOwners := by
  induction attempt with
  | nil => simp [failedOwners]
  | @active _ _ _ _ name owner payload fresh guard rest config excluded finished afterExcluded
      active choice missed missingFailure later ih =>
      cases missed <;> simpa [failedOwners, excludeCommit, Finset.union_insert,
        Finset.insert_union] using ih
  | excluded _ _ ih => exact ih

omit [IExpr.ResultTypes L] in
theorem failed_disjoint (attempt : Attempt block entry excluded finished afterExcluded) :
    Disjoint attempt.failedOwners excluded := by
  induction attempt with
  | nil => simp [failedOwners]
  | @active _ _ _ _ name owner payload fresh guard rest config excluded finished afterExcluded
      active choice missed missingFailure later ih =>
      cases missed with
      | true =>
          simp only [excludeCommit, ↓reduceIte,
            Finset.disjoint_insert_right] at ih
          exact Finset.disjoint_insert_left.mpr ⟨active, ih.2⟩
      | false => exact ih
  | excluded _ _ ih => exact ih

omit [IExpr.ResultTypes L] in
theorem failed_subset_owners (attempt : Attempt block entry excluded finished afterExcluded) :
    attempt.failedOwners ⊆ block.owners := by
  induction attempt with
  | nil => exact Finset.empty_subset _
  | active _ _ missed _ later ih =>
      cases missed with
      | true => exact Finset.insert_subset_insert _ ih
      | false => exact fun who member => Finset.mem_insert_of_mem (ih member)
  | excluded _ later ih => exact fun who member => Finset.mem_insert_of_mem (ih member)

omit [IExpr.ResultTypes L] in
theorem excluded_subset (attempt : Attempt block entry excluded finished afterExcluded) :
    excluded ⊆ afterExcluded := by
  rw [attempt.excluded_eq]
  exact Finset.subset_union_left

omit [IExpr.ResultTypes L] in
theorem newly_excluded (attempt : Attempt block entry excluded finished afterExcluded) :
    afterExcluded \ excluded = attempt.failedOwners := by
  calc afterExcluded \ excluded = (excluded ∪ attempt.failedOwners) \ excluded :=
        congrArg (fun owners => owners \ excluded) attempt.excluded_eq
    _ = attempt.failedOwners := by
        rw [Finset.union_sdiff_left]
        exact Finset.sdiff_eq_self_iff_disjoint.mpr attempt.failed_disjoint

omit [IExpr.ResultTypes L] in
private theorem commit_history_prefix {Γ : SourceCtx Player L} {owner : Player}
    {name : VarId} {payload : L.Ty} (guard : SourceGuard L Γ owner name payload)
    (config : Config Player L Γ) (choice : PublicationResult (L.Val payload)) (who : Player) :
    (config.history who).IsPrefix ((commitSuccessor name guard config choice).history who) := by
  by_cases same : who = owner
  · subst who
    simp only [commitSuccessor, Function.update_self]
    exact List.prefix_append _ _
  · simpa only [commitSuccessor, Function.update_of_ne same] using
      (List.prefix_refl (config.history who))

omit [IExpr.ResultTypes L] in
theorem history_prefix (attempt : Attempt block entry excluded finished afterExcluded)
    (who : Player) : (entry.history who).IsPrefix (finished.history who) := by
  induction attempt with
  | nil => exact List.prefix_refl _
  | active _ choice _ _ later ih => exact (commit_history_prefix _ _ choice who).trans ih
  | excluded _ later ih => exact ih

end Attempt
end CommitPrefix
end Vegas.SourceProgram
