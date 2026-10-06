/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.IntendedGame
import Vegas.Source.Forfeit
import Vegas.Source.Accounting
import Vegas.Source.ProtocolEvaluation

/-! # Play of the intended game and departures from it

Every configuration the intended game reaches keeps an invariant
(`Vegas.SourceProgram.Config.Intended`): commitment cells hold values, revealed
commitments publish their bindings, and every retained guard is predicted to
accept its subject's binding. Prediction is then exact
(`Vegas.SourceProgram.Obligation.accepts_eq_predicts`), so every reveal of the
intended game opens a value and no reveal fails
(`Vegas.SourceProgram.ProtocolState.failedReveals_eq_zero_of_intended`).

A player that leaves the intended game, by withholding at an own reveal or by
binding a value its guard is predicted to reject, owes a failed reveal on every
continuation, whatever anyone plays
(`Vegas.SourceProgram.ProtocolState.failedReveals_pos_of_indebted`). A rejected
binding stays pending (`Vegas.SourceProgram.Config.Indebted`) until the reveal
that completes its guard, which belongs to the same player because a guard reads
only its author's commitments; that reveal fails, either because the player
withholds or because its own revealed commitments publish their bindings and
the guard rejects. Every commitment is revealed before the program returns, so
the debt is always paid.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The revealed commitments of `who` publish their bindings. -/
def PublishesBindings {Γ : SourceCtx Player L} (who : Player) (revelations : Revelations Γ)
    (state : State L Γ) : Prop :=
  ∀ {x : VarId} {payload : L.Ty} (cell : HasVar Γ x (.commitment who payload)),
    (revelations cell).isRevealed = true → (revelations cell).result state = state.get cell

section Revelations

variable {Γ : SourceCtx Player L}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem PublishesBindings.weaken {who : Player} {revelations : Revelations Γ}
    {state : State L Γ} {name : VarId} {cell : CellTy Player L} (head : CellVal L cell)
    (publishes : PublishesBindings who revelations state) :
    PublishesBindings who (revelations.weaken (name := name) (cell := cell))
      (Env.cons head state) := by
  intro x payload member revealed
  cases member with
  | here => simp [Revelations.weaken, HasVar.tail?, Revelation.isRevealed] at revealed
  | there member =>
      simp only [Revelations.weaken_there, Revelation.isRevealed_weaken] at revealed
      simp only [Revelations.weaken_there, Revelation.result_weaken, Env.cons_get_there]
      exact publishes member revealed

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Revealing one owner's commitment leaves another owner's commitments as they
were. -/
theorem Revelations.reveal_there_of_ne_owner {owner other : Player} {payload τ : L.Ty}
    {name x published : VarId} (revelations : Revelations Γ)
    (source : HasVar Γ name (.commitment owner payload))
    (cell : HasVar Γ x (.commitment other τ)) (different : other ≠ owner) :
    revelations.reveal (published := published) source (.there cell) =
      (revelations cell).weaken := by
  cases found : cell.sameCell? source with
  | none => simp only [Revelations.reveal, HasVar.tail?_there, found]
  | some same => exact absurd (CellTy.commitment.inj same.down.2).1 different

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A reveal keeps `who`'s commitments publishing their bindings when the new
publication carries the binding of any commitment of `who` it reveals. -/
theorem PublishesBindings.reveal {who owner : Player} {payload : L.Ty} {name published : VarId}
    (unique : (Γ.map Prod.fst).Nodup) {revelations : Revelations Γ} {state : State L Γ}
    (source : HasVar Γ name (.commitment owner payload))
    (head : PublicationResult (L.Val payload)) (opens : owner = who → head = state.get source)
    (publishes : PublishesBindings who revelations state) :
    PublishesBindings who (revelations.reveal (published := published) source)
      (Env.cons (Val := CellVal (Player := Player) L) (x := published)
        (τ := .publication payload) head state) := by
  intro x σ member revealed
  cases member with
  | there member =>
      by_cases same : x = name
      · subst same
        have cellEq := HasVar.type_unique unique member source
        cases cellEq
        cases HasVar.eq_of_nodup unique member source
        simp only [Revelations.reveal_source, Revelation.result, Env.cons_get_here,
          Env.cons_get_there]
        exact opens rfl
      · simp only [Revelations.reveal_of_ne _ source member same,
          Revelation.isRevealed_weaken] at revealed ⊢
        rw [Revelation.result_weaken, Env.cons_get_there]
        exact publishes member revealed

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A guard reads only its author's commitments, so a reveal completes an
obligation only when it reveals a commitment of the obligation's owner. -/
theorem Obligation.owner_eq_of_completedBy {owner : Player} {payload : L.Ty}
    {name published : VarId} (obligation : Obligation (Player := Player) (L := L) Γ)
    (revelations : Revelations Γ) (source : HasVar Γ name (.commitment owner payload))
    (completed : obligation.completedBy (published := published) revelations source = true) :
    obligation.owner = owner := by
  by_contra different
  simp only [Obligation.completedBy, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at completed
  obtain ⟨before, after⟩ := completed
  have revealed : obligation.revealed revelations = true := by
    simp only [Obligation.revealed, Obligation.weaken, Bool.and_eq_true] at after ⊢
    obtain ⟨subject, reads⟩ := after
    refine ⟨?_, ?_⟩
    · rwa [Revelations.reveal_there_of_ne_owner _ _ _ different,
        Revelation.isRevealed_weaken] at subject
    · simp only [SourceGuard.readsRevealed, SourceGuard.weaken] at reads ⊢
      rw [GuardCode.allReads_iff] at reads ⊢
      intro x τ member used
      have read := reads member used
      revert read
      cases obligation.guard.reads member with
      | publicData _ => exact fun _ => rfl
      | publication _ => exact fun _ => rfl
      | commitment cell =>
          simp [SourceGuardRead.weaken, SourceGuardRead.revealed,
            Revelations.reveal_there_of_ne_owner _ _ _ different]
  rw [revealed] at before
  exact absurd before (by decide)

end Revelations

namespace Config

omit [IExpr.ResultTypes L]

variable {Γ : SourceCtx Player L}

/-- A configuration the intended game can be in: unique names, accounted
revelations, a value in every commitment cell, revealed commitments publishing
their bindings, and every retained guard predicted to accept its subject's
binding. -/
structure Intended (unresolved : Finset VarId) (config : Config Player L Γ) : Prop where
  unique : (Γ.map Prod.fst).Nodup
  accounted : Accounted config.revelations unresolved
  bound : ∀ {x : VarId} {owner : Player} {payload : L.Ty}
    (cell : HasVar Γ x (.commitment owner payload)),
    ∃ value, config.state.get cell = .success value
  publishes : ∀ who, PublishesBindings who config.revelations config.state
  predicted : ∀ obligation ∈ config.registry, ∀ value,
    config.state.get obligation.source = .success value →
      obligation.guard.predicts (sourceObserve obligation.owner config.state) value = true

/-- A configuration in which `who` owes a failed reveal: an obligation of
`who`, not yet checked, whose guard is predicted to reject the bound value,
while `who`'s revealed commitments publish their bindings. -/
structure Indebted (who : Player) (unresolved : Finset VarId) (config : Config Player L Γ) :
    Prop where
  unique : (Γ.map Prod.fst).Nodup
  accounted : Accounted config.revelations unresolved
  publishes : PublishesBindings who config.revelations config.state
  pending : ∃ obligation ∈ config.registry, obligation.owner = who ∧
    obligation.revealed config.revelations = false ∧
    ∃ value, config.state.get obligation.source = .success value ∧
      obligation.guard.predicts (sourceObserve obligation.owner config.state) value = false

variable {config : Config Player L Γ} {unresolved : Finset VarId}

private theorem Intended.predicted_weaken {name : VarId} {cell : CellTy Player L}
    (intended : config.Intended unresolved) (head : CellVal L cell) :
    ∀ obligation ∈ (config.registry.weaken (x := name) (c := cell)), ∀ value,
      (Env.cons head config.state).get obligation.source = .success value →
        obligation.guard.predicts
          (sourceObserve obligation.owner (Env.cons head config.state)) value = true := by
  intro obligation member value bound
  obtain ⟨original, kept, rfl⟩ := List.mem_map.mp member
  exact (SourceGuard.predicts_weaken _ _ _ _).trans
    (intended.predicted original kept value bound)

/-- The binding of a commitment cell, as the result its opening would publish. -/
abbrev bindingOf {owner : Player} {payload : L.Ty} {name : VarId} (config : Config Player L Γ)
    (source : HasVar Γ name (.commitment owner payload)) : PublicationResult (L.Val payload) :=
  config.state.get source

omit [DecidableEq Player] in
private theorem unique_cons {name : VarId} {cell : CellTy Player L}
    (fresh : name ∉ Γ.map Prod.fst) (unique : (Γ.map Prod.fst).Nodup) :
    (((name, cell) :: Γ).map Prod.fst).Nodup := by
  simp [fresh, unique]

theorem Intended.sample {name : VarId} {payload : L.Ty} (intended : config.Intended unresolved)
    (fresh : name ∉ Γ.map Prod.fst) (value : L.Val payload) :
    (sampleSuccessor name config value).Intended unresolved where
  unique := unique_cons fresh intended.unique
  accounted :=
    Accounted.weaken_noncommitment (by intro _ _ equal; cases equal) intended.accounted
  bound cell := by
    cases cell with
    | there cell => exact intended.bound cell
  publishes who := PublishesBindings.weaken _ (intended.publishes who)
  predicted := intended.predicted_weaken _

theorem Intended.commit {name : VarId} {owner : Player} {payload : L.Ty}
    (intended : config.Intended unresolved) (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload) (value : L.Val payload)
    (accepted : guard.predicts (sourceObserve owner config.state) value = true) :
    (commitSuccessor name guard config (.success value)).Intended (insert name unresolved) where
  unique := unique_cons fresh intended.unique
  accounted := Accounted.commit fresh intended.accounted
  bound cell := by
    cases cell with
    | here => exact ⟨value, rfl⟩
    | there cell => exact intended.bound cell
  publishes who := PublishesBindings.weaken _ (intended.publishes who)
  predicted := by
    intro obligation member bound bindsBound
    rcases List.mem_cons.mp member with rfl | member
    · cases bindsBound
      exact (SourceGuard.predicts_weaken _ _ _ _).trans accepted
    · exact intended.predicted_weaken _ obligation member bound bindsBound

/-- Every obligation an intended reveal completes accepts the opened binding. -/
theorem Intended.completed_accept {owner : Player} {payload : L.Ty} {name published : VarId}
    (intended : config.Intended unresolved) (source : HasVar Γ name (.commitment owner payload)) :
    (Registry.completedBy (published := published) config.registry config.revelations
        source).all
      (·.accepts (Revelations.reveal (published := published) config.revelations source)
        (Env.cons (Val := CellVal (Player := Player) L) (x := published)
          (τ := .publication payload) (bindingOf config source) config.state)) = true := by
  refine List.all_eq_true.mpr fun completed member => ?_
  obtain ⟨original, filtered, rfl⟩ := List.mem_map.mp member
  obtain ⟨value, bound⟩ := intended.bound original.source
  rw [Obligation.accepts_eq_predicts original.weaken _ _
    (Registry.revealed_of_mem_completedBy _ _ _ member)
    (PublishesBindings.reveal intended.unique source _ (fun _ => rfl)
      (intended.publishes original.owner)) (value := value) bound]
  exact (SourceGuard.predicts_weaken _ _ _ _).trans
    (intended.predicted original (List.mem_filter.mp filtered).1 value bound)

theorem Intended.reveal_state {owner : Player} {payload : L.Ty} {name published : VarId}
    (intended : config.Intended unresolved) (source : HasVar Γ name (.commitment owner payload)) :
    (revealSuccessor published source config true).state =
      Env.cons (Val := CellVal (Player := Player) L) (x := published)
        (τ := .publication payload) (bindingOf config source) config.state := by
  simp only [revealSuccessor, ↓reduceIte, intended.completed_accept source]

/-- An intended reveal opens a value and keeps the invariant. -/
theorem Intended.reveal {owner : Player} {payload : L.Ty} {name published : VarId}
    (intended : config.Intended unresolved) (fresh : published ∉ Γ.map Prod.fst)
    (source : HasVar Γ name (.commitment owner payload)) :
    (revealSuccessor published source config true).Intended (unresolved.erase name) ∧
      ∃ value, (revealSuccessor published source config true).state.get .here =
        .success value := by
  obtain ⟨value, bound⟩ := intended.bound source
  have state := intended.reveal_state (published := published) source
  refine ⟨{ unique := unique_cons fresh intended.unique
            accounted := Accounted.reveal source intended.unique intended.accounted
            bound := ?_
            publishes := fun who => ?_
            predicted := ?_ }, value, ?_⟩
  · intro x other τ cell
    cases cell with
    | there cell =>
        rw [state]
        exact intended.bound cell
  · rw [state]
    exact PublishesBindings.reveal intended.unique source _ (fun _ => rfl)
      (intended.publishes who)
  · rw [state]
    exact intended.predicted_weaken _
  · rw [state]
    exact bound

theorem Indebted.sample {who : Player} {name : VarId} {payload : L.Ty}
    (indebted : config.Indebted who unresolved) (fresh : name ∉ Γ.map Prod.fst)
    (value : L.Val payload) :
    (sampleSuccessor name config value).Indebted who unresolved where
  unique := unique_cons fresh indebted.unique
  accounted :=
    Accounted.weaken_noncommitment (by intro _ _ equal; cases equal) indebted.accounted
  publishes := PublishesBindings.weaken _ indebted.publishes
  pending := by
    obtain ⟨obligation, member, own, unrevealed, value, bound, rejected⟩ := indebted.pending
    exact ⟨obligation.weaken, List.mem_map_of_mem member, own,
      (Obligation.revealed_weaken _ _).trans unrevealed, value, bound,
      (SourceGuard.predicts_weaken _ _ _ _).trans rejected⟩

theorem Indebted.commit {who owner : Player} {name : VarId} {payload : L.Ty}
    (indebted : config.Indebted who unresolved) (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload) (choice : PublicationResult (L.Val payload)) :
    (commitSuccessor name guard config choice).Indebted who (insert name unresolved) where
  unique := unique_cons fresh indebted.unique
  accounted := Accounted.commit fresh indebted.accounted
  publishes := PublishesBindings.weaken _ indebted.publishes
  pending := by
    obtain ⟨obligation, member, own, unrevealed, value, bound, rejected⟩ := indebted.pending
    exact ⟨obligation.weaken, List.mem_cons_of_mem _ (List.mem_map_of_mem member), own,
      (Obligation.revealed_weaken _ _).trans unrevealed, value, bound,
      (SourceGuard.predicts_weaken _ _ _ _).trans rejected⟩

/-- Binding a value its guard is predicted to reject leaves the owner indebted. -/
theorem Intended.indebted_commit {who : Player} {name : VarId} {payload : L.Ty}
    (intended : config.Intended unresolved) (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ who name payload) (value : L.Val payload)
    (rejected : guard.predicts (sourceObserve who config.state) value = false) :
    (commitSuccessor name guard config (.success value)).Indebted who
      (insert name unresolved) where
  unique := unique_cons fresh intended.unique
  accounted := Accounted.commit fresh intended.accounted
  publishes := PublishesBindings.weaken _ (intended.publishes who)
  pending := ⟨Obligation.mk who name payload .here guard.weaken, List.mem_cons_self .., rfl,
    rfl,
    value, rfl, (SourceGuard.predicts_weaken _ _ _ _).trans rejected⟩

omit [DecidableEq Player] in
private theorem opened_of_ne_failure {α : Type} {accepted : Prop} [Decidable accepted]
    {disclose : Bool} {bound : PublicationResult α}
    (kept : (if accepted then (if disclose then bound else .failure) else .failure) ≠
      .failure) :
    (if accepted then (if disclose then bound else .failure) else .failure) = bound := by
  by_cases holds : accepted <;> cases disclose <;> simp_all

/-- A reveal either fails a reveal of the indebted player or keeps the debt. -/
theorem Indebted.reveal {who owner : Player} {payload : L.Ty} {name published : VarId}
    (indebted : config.Indebted who unresolved) (fresh : published ∉ Γ.map Prod.fst)
    (source : HasVar Γ name (.commitment owner payload)) (disclose : Bool) :
    (owner = who ∧
        (revealSuccessor published source config disclose).state.get .here = .failure) ∨
      (revealSuccessor published source config disclose).Indebted who
        (unresolved.erase name) := by
  by_cases forfeited : owner = who ∧
      (revealSuccessor published source config disclose).state.get .here = .failure
  · exact Or.inl forfeited
  right
  have opens : owner = who →
      (revealSuccessor published source config disclose).state.get .here =
        config.state.get source := by
    intro own
    exact opened_of_ne_failure fun failed => forfeited ⟨own, failed⟩
  obtain ⟨obligation, member, own, unrevealed, value, bound, rejected⟩ := indebted.pending
  by_cases completed :
      obligation.completedBy (published := published) config.revelations source = true
  · have ownerEq := Obligation.owner_eq_of_completedBy obligation config.revelations source
      completed
    have failed : (revealSuccessor published source config disclose).state.get .here =
        .failure := by
      simp only [revealSuccessor, Env.cons_get_here]
      cases disclose with
      | false => simp
      | true =>
          have accepts := Obligation.accepts_eq_predicts obligation.weaken
            (Revelations.reveal (published := published) config.revelations source)
            (Env.cons (Val := CellVal (Player := Player) L) (x := published)
              (τ := .publication payload) (bindingOf config source) config.state)
            (Registry.revealed_of_mem_completedBy _ _ _
              (List.mem_map_of_mem (List.mem_filter.mpr ⟨member, completed⟩)))
            (PublishesBindings.reveal indebted.unique source _ (fun _ => rfl)
              (own ▸ indebted.publishes)) (value := value) bound
          have rejectedHere := accepts.trans
            ((SourceGuard.predicts_weaken _ _ _ _).trans rejected)
          have rejects : (Registry.completedBy (published := published) config.registry
              config.revelations source).all
                (·.accepts (Revelations.reveal (published := published) config.revelations source)
                  (Env.cons (Val := CellVal (Player := Player) L) (x := published)
                    (τ := .publication payload) (bindingOf config source) config.state)) =
                false := by
            rw [List.all_eq_false]
            exact ⟨obligation.weaken,
              List.mem_map_of_mem (List.mem_filter.mpr ⟨member, completed⟩), by simp [rejectedHere]⟩
          simp [rejects]
    exact (forfeited ⟨ownerEq.symm.trans own, failed⟩).elim
  · have stillUnrevealed : (obligation.weaken (x := published)).revealed
        (Revelations.reveal (published := published) config.revelations source) = false := by
      simpa [Obligation.completedBy, unrevealed] using completed
    exact
      { unique := unique_cons fresh indebted.unique
        accounted := Accounted.reveal source indebted.unique indebted.accounted
        publishes := PublishesBindings.reveal indebted.unique source _ opens indebted.publishes
        pending := ⟨obligation.weaken, List.mem_map_of_mem member, own, stillUnrevealed, value,
          bound, (SourceGuard.predicts_weaken _ _ _ _).trans rejected⟩ }

/-- At the return point every commitment is revealed, so nobody is indebted. -/
theorem Indebted.not_resolved {who : Player} (indebted : config.Indebted who ∅) : False := by
  obtain ⟨obligation, _, _, unrevealed, _⟩ := indebted.pending
  have revealed : obligation.revealed config.revelations = true := by
    simp only [Obligation.revealed, Bool.and_eq_true]
    refine ⟨(indebted.accounted obligation.source).mpr (Finset.notMem_empty _), ?_⟩
    rw [SourceGuard.readsRevealed, GuardCode.allReads_iff]
    intro x τ member _
    cases obligation.guard.reads member with
    | publicData _ => rfl
    | publication _ => rfl
    | commitment cell => exact (indebted.accounted cell).mpr (Finset.notMem_empty _)
  rw [revealed] at unrevealed
  exact absurd unrevealed (by decide)

end Config

section Count

variable {Γ : SourceCtx Player L} {O : Finset VarId}

/-- The reveal cell a reveal instruction writes. -/
abbrev headRevealCell {published name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : published ∉ Γ.map Prod.fst} {source : HasVar Γ name (.commitment owner payload)}
    {unresolved : name ∈ O}
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)) :
    RevealCell
      (SourceProgram.reveal published owner name fresh source unresolved next).terminalCtx :=
  ⟨owner, payload, published, terminalRef next .here⟩

theorem failedReveals_reveal_of_not_failed {published name : VarId} {owner : Player}
    {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (who : Player) (outcome : PublicOutcome next)
    (kept : (headRevealCell (fresh := fresh) (source := source) (unresolved := unresolved)
      next).failed outcome = false) :
    failedReveals (.reveal published owner name fresh source unresolved next) who outcome =
      failedReveals next who outcome := by
  simp [failedReveals, revealCells, kept]

theorem failedReveals_reveal_le {published name : VarId} {owner : Player}
    {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (who : Player) (outcome : PublicOutcome next) :
    failedReveals next who outcome ≤
      failedReveals (.reveal published owner name fresh source unresolved next) who outcome := by
  simp only [failedReveals, revealCells, List.filter_cons]
  split <;> simp

theorem failedReveals_reveal_pos {published name : VarId} {owner : Player}
    {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (outcome : PublicOutcome next)
    (failed : (headRevealCell (fresh := fresh) (source := source) (unresolved := unresolved)
      next).failed outcome = true) :
    1 ≤ failedReveals (.reveal published owner name fresh source unresolved next) owner
      outcome := by
  simp [failedReveals, revealCells, failed]

end Count

namespace ProtocolState

/-- The cells of a program's entry context at one of its program points. -/
def base : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → State L Γ
  | _, _, .ret _ => fun config => config.state
  | _, _, .sample _ _ _ next => Sum.elim (fun config => config.state)
      (fun rest _ _ cell => (base next rest).get (.there cell))
  | _, _, .commit _ _ _ _ next => Sum.elim (fun config => config.state)
      (fun rest _ _ cell => (base next rest).get (.there cell))
  | _, _, .reveal _ _ _ _ _ _ next => Sum.elim (fun config => config.state)
      (fun rest _ _ cell => (base next rest).get (.there cell))

@[simp] theorem base_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    base program (entry program config) = config.state := by
  cases program <;> rfl

/-- A step never changes a cell that already exists. -/
theorem base_step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → (target : ProtocolState program) →
    target ∈ (step program state joint).support → base program target = base program state
  | _, _, .ret _, _, _, _, reached => by
      rw [step, PMF.mem_support_pure_iff] at reached
      rw [reached]
  | _, _, .sample _ _ _ next, state, joint, target, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          change (fun _ _ cell => (base next (entry next _)).get (.there cell)) = config.state
          rw [base_entry]
          rfl
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          simp only [base, Sum.elim_inr, base_step next rest joint after supported]
  | _, _, .commit _ _ _ _ next, state, joint, target, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          change (fun _ _ cell => (base next (entry next _)).get (.there cell)) = config.state
          rw [base_entry]
          rfl
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          simp only [base, Sum.elim_inr, base_step next rest joint after supported]
  | _, _, .reveal _ _ _ _ _ _ next, state, joint, target, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          change (fun _ _ cell => (base next (entry next _)).get (.there cell)) = config.state
          rw [base_entry]
          rfl
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          simp only [base, Sum.elim_inr, base_step next rest joint after supported]

/-- A terminal store extends the entry cells of every program point it was read
from. -/
theorem initialState_of_readout : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    {terminal : State L program.terminalCtx} → readout program state = some terminal →
    initialState program terminal = base program state
  | _, _, .ret _, _, _, read => by
      cases read
      rfl
  | _, _, .sample _ _ _ next, state, terminal, read => by
      cases state with
      | inl _ => cases read
      | inr rest =>
          simp only [initialState, base, Sum.elim_inr, initialState_of_readout next rest read]
  | _, _, .commit _ _ _ _ next, state, terminal, read => by
      cases state with
      | inl _ => cases read
      | inr rest =>
          simp only [initialState, base, Sum.elim_inr, initialState_of_readout next rest read]
  | _, _, .reveal _ _ _ _ _ _ next, state, terminal, read => by
      cases state with
      | inl _ => cases read
      | inr rest =>
          simp only [initialState, base, Sum.elim_inr, initialState_of_readout next rest read]

/-- A terminal program point has a terminal store. -/
theorem exists_readout_of_terminal : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    terminal program state → ∃ terminal, readout program state = some terminal
  | _, _, .ret _, config, _ => ⟨config.state, rfl⟩
  | _, _, .sample _ _ _ next, state, stopped => by
      cases state with
      | inl _ => exact stopped.elim
      | inr rest => exact exists_readout_of_terminal next rest stopped
  | _, _, .commit _ _ _ _ next, state, stopped => by
      cases state with
      | inl _ => exact stopped.elim
      | inr rest => exact exists_readout_of_terminal next rest stopped
  | _, _, .reveal _ _ _ _ _ _ next, state, stopped => by
      cases state with
      | inl _ => exact stopped.elim
      | inr rest => exact exists_readout_of_terminal next rest stopped

/-- A program point the intended game can be at: an intended configuration whose
remaining guards are satisfiable, and an opened value in every reveal cell
already written. -/
def Intended : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Prop
  | _, _, .ret _ => fun config => Config.Intended ∅ config
  | _, O, .sample name fresh law next =>
      Sum.elim (fun config => Config.Intended O config ∧
          GuardsSatisfiableFrom (.sample name fresh law next) config)
        (Intended next)
  | _, O, .commit name owner fresh guard next =>
      Sum.elim (fun config => Config.Intended O config ∧
          GuardsSatisfiableFrom (.commit name owner fresh guard next) config)
        (Intended next)
  | _, O, .reveal published owner name fresh source unresolved next =>
      Sum.elim (fun config => Config.Intended O config ∧
          GuardsSatisfiableFrom (.reveal published owner name fresh source unresolved next) config)
        (fun rest => (∃ value, (base next rest).get .here = .success value) ∧ Intended next rest)

/-- A program point at which `who` owes a failed reveal: either one of its
reveals has failed, or it is indebted at the current configuration. -/
def Indebted (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Prop
  | _, _, .ret _ => fun config => Config.Indebted who ∅ config
  | _, O, .sample _ _ _ next => Sum.elim (Config.Indebted who O) (Indebted who next)
  | _, O, .commit _ _ _ _ next => Sum.elim (Config.Indebted who O) (Indebted who next)
  | _, O, .reveal _ owner _ _ _ _ next =>
      Sum.elim (Config.Indebted who O)
        (fun rest => (owner = who ∧ (base next rest).get .here = .failure) ∨
          Indebted who next rest)

theorem intended_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ)
    (intended : config.Intended O) (satisfiable : GuardsSatisfiableFrom program config) :
    Intended program (entry program config) := by
  cases program with
  | ret => exact intended
  | sample => exact ⟨intended, satisfiable⟩
  | commit => exact ⟨intended, satisfiable⟩
  | reveal => exact ⟨intended, satisfiable⟩

theorem indebted_entry {who : Player} {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ)
    (indebted : config.Indebted who O) : Indebted who program (entry program config) := by
  cases program with
  | ret => exact indebted
  | sample => exact indebted
  | commit => exact indebted
  | reveal => exact indebted

/-- Every step, whatever anyone plays, keeps a player's debt. -/
theorem indebted_step (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → (target : ProtocolState program) →
    Indebted who program state → target ∈ (step program state joint).support →
      Indebted who program target
  | _, _, .ret _, _, _, _, indebted, reached => by
      rw [step, PMF.mem_support_pure_iff] at reached
      rw [reached]
      exact indebted
  | _, _, .sample _ fresh _ next, state, joint, target, indebted, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          exact indebted_entry next _ (Config.Indebted.sample indebted fresh value)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact indebted_step who next rest joint after indebted supported
  | _, _, .commit _ _ fresh guard next, state, joint, target, indebted, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          exact indebted_entry next _ (Config.Indebted.commit indebted fresh guard _)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact indebted_step who next rest joint after indebted supported
  | _, _, .reveal _ _ _ fresh source _ next, state, joint, target, indebted, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          rcases Config.Indebted.reveal indebted fresh source _ with forfeited | indebted
          · left
            rw [base_entry]
            exact forfeited
          · exact Or.inr (indebted_entry next _ indebted)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases indebted with ⟨own, failed⟩ | indebted
          · exact Or.inl ⟨own, (base_step next rest joint after supported).symm ▸ failed⟩
          · exact Or.inr (indebted_step who next rest joint after indebted supported)

/-- Every step of the intended game keeps the intended invariant. -/
theorem intended_step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → (target : ProtocolState program) →
    Intended program state →
    (∀ who, ProtocolView.intendedMenu who program (observe who program state) (joint who)) →
    target ∈ (step program state joint).support → Intended program target
  | _, _, .ret _, _, _, _, intended, _, reached => by
      rw [step, PMF.mem_support_pure_iff] at reached
      rw [reached]
      exact intended
  | _, _, .sample _ fresh _ next, state, joint, target, intended, legal, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, supported, rfl⟩ := reached
          exact intended_entry next _ (intended.1.sample fresh value) (intended.2 value supported)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact intended_step next rest joint after intended legal supported
  | _, _, .commit (payload := payload) name owner fresh guard next, state, joint, target,
      intended, legal, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          have ownerLegal := legal owner
          revert ownerLegal
          cases chosen : joint owner with
          | none => exact fun inactive => (inactive rfl).elim
          | some action =>
              rintro ⟨_, value, offered, rfl⟩
              have accepted := (mem_intendedValues_self guard _ intended.2.1 value).mp offered
              rw [OwnAction.binding_commit]
              exact intended_entry next _ (intended.1.commit fresh guard value accepted)
                (intended.2.2 value accepted)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact intended_step next rest joint after intended legal supported
  | _, _, .reveal published owner name fresh source _ next, state, joint, target, intended,
      legal, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          have ownerLegal := legal owner
          revert ownerLegal
          cases chosen : joint owner with
          | none => exact fun inactive => (inactive rfl).elim
          | some action =>
              rintro ⟨_, rfl⟩
              obtain ⟨kept, opened⟩ := intended.1.reveal fresh source
              refine ⟨?_, intended_entry next _ kept intended.2⟩
              rw [base_entry]
              exact opened
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ⟨(base_step next rest joint after supported).symm ▸ intended.1,
            intended_step next rest joint after intended.2 legal supported⟩

/-- **Leaving the intended game.** A step at which `who` takes a source action
the intended game does not offer, from a point of the intended game, leaves
`who` owing a failed reveal: a withholding fails at once, and a value the guard
is predicted to reject leaves an indebted obligation. -/
theorem indebted_of_deviation (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (∀ site, admission site = .values) → (state : ProtocolState program) →
    Intended program state → (joint : Player → Option (OwnAction Player L)) →
    (action : OwnAction Player L) → joint who = some action →
    ProtocolView.actor who program (observe who program state) = some who →
    action ∈ ProtocolView.available who program admission (observe who program state) →
    action ∉ ProtocolView.intendedAvailable who program (observe who program state) →
    ∀ target ∈ (step program state joint).support, Indebted who program target
  | _, _, .ret _, _, _, _, _, _, _, _, acts, _, _, _, _ => by
      simp [ProtocolView.actor] at acts
  | _, _, .sample _ _ _ next, admission, values, state, intended, joint, action, chosen, acts,
      available, new, target, reached => by
      cases state with
      | inl config => simp [ProtocolView.actor, observe] at acts
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact indebted_of_deviation who next admission values rest intended joint action chosen
            acts available new after supported
  | _, _, .commit (payload := payload) name owner fresh guard next, admission, values, state,
      intended, joint, action, chosen, acts, available, new, target, reached => by
      cases state with
      | inl config =>
          have same : owner = who := by simpa [ProtocolView.actor, observe] using acts
          subst same
          obtain ⟨choice, admits, rfl⟩ := available
          rw [values none] at admits
          cases choice with
          | failure => simp at admits
          | success value =>
              have rejected : guard.predicts (sourceObserve owner config.state) value = false := by
                have notIntended :
                    value ∉ intendedValues owner guard (sourceObserve owner config.state) :=
                  fun offered => new ⟨value, offered, rfl⟩
                rw [mem_intendedValues_self guard _ intended.2.1] at notIntended
                simpa using notIntended
              simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
              subst reached
              rw [chosen, OwnAction.binding_commit]
              exact indebted_entry next _ (intended.1.indebted_commit fresh guard value rejected)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact indebted_of_deviation who next (fun site => admission (some site))
            (fun site => values (some site)) rest intended joint action chosen acts available new
            after supported
  | _, _, .reveal published owner name fresh source _ next, admission, values, state, intended,
      joint, action, chosen, acts, available, new, target, reached => by
      cases state with
      | inl config =>
          have same : owner = who := by simpa [ProtocolView.actor, observe] using acts
          subst same
          obtain ⟨disclose, rfl⟩ := available
          cases disclose with
          | true => exact (new rfl).elim
          | false =>
              simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
              subst reached
              rw [chosen]
              refine Or.inl ⟨rfl, ?_⟩
              rw [base_entry]
              simp [revealSuccessor, OwnAction.disclosure]
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact Or.inr (indebted_of_deviation who next admission values rest intended.2 joint
            action chosen acts available new after supported)

/-- **No forfeit in the intended game.** No reveal fails on a terminal store read
from a point of the intended game. -/
theorem failedReveals_eq_zero_of_intended (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    Intended program state → {terminal : State L program.terminalCtx} →
    readout program state = some terminal →
      failedReveals program who (publicOutcome program terminal) = 0
  | _, _, .ret _, _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, state, intended, terminal, read => by
      cases state with
      | inl _ => cases read
      | inr rest => exact failedReveals_eq_zero_of_intended who next rest intended read
  | _, _, .commit _ _ _ _ next, state, intended, terminal, read => by
      cases state with
      | inl _ => cases read
      | inr rest => exact failedReveals_eq_zero_of_intended who next rest intended read
  | _, _, .reveal _ _ _ _ _ _ next, state, intended, terminal, read => by
      cases state with
      | inl _ => cases read
      | inr rest =>
          obtain ⟨⟨value, opened⟩, rest_intended⟩ := intended
          have holds : terminal.get (terminalRef next .here) = .success value :=
            (terminalRef_get next terminal .here).trans
              ((congrArg (fun state => state.get .here)
                (initialState_of_readout next rest read)).trans opened)
          rw [failedReveals_reveal_of_not_failed who _ ?_]
          · exact failedReveals_eq_zero_of_intended who next rest rest_intended read
          · exact RevealCell.failed_publicOutcome_of_success next _ terminal holds

/-- **A debt is paid.** Every terminal store read from a point at which `who` is
indebted records a failed reveal of `who`. -/
theorem failedReveals_pos_of_indebted (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    Indebted who program state → {terminal : State L program.terminalCtx} →
    readout program state = some terminal →
      1 ≤ failedReveals program who (publicOutcome program terminal)
  | _, _, .ret _, _, indebted, _, _ => (Config.Indebted.not_resolved indebted).elim
  | _, _, .sample _ _ _ next, state, indebted, terminal, read => by
      cases state with
      | inl _ => cases read
      | inr rest => exact failedReveals_pos_of_indebted who next rest indebted read
  | _, _, .commit _ _ _ _ next, state, indebted, terminal, read => by
      cases state with
      | inl _ => cases read
      | inr rest => exact failedReveals_pos_of_indebted who next rest indebted read
  | _, _, .reveal _ _ _ _ _ _ next, state, indebted, terminal, read => by
      cases state with
      | inl _ => cases read
      | inr rest =>
          rcases indebted with ⟨own, failed⟩ | indebted
          · have holds : terminal.get (terminalRef next .here) = .failure :=
              (terminalRef_get next terminal .here).trans
                ((congrArg (fun state => state.get .here)
                  (initialState_of_readout next rest read)).trans failed)
            subst own
            refine failedReveals_reveal_pos (publicOutcome next terminal) ?_
            simp [RevealCell.failed, publicOutcome, sourcePublicEnv_get_publicRef, holds,
              PublicationResult.isSuccess]
          · exact (failedReveals_pos_of_indebted who next rest indebted read).trans
              (failedReveals_reveal_le who _)

end ProtocolState

end Vegas.SourceProgram
