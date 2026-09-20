/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Semantics

/-! # Policies that bind a value

A source policy may bind an unopenable candidate, which is how the source
represents what a native player does when it commits to something that will
never open. Once an outcome is the public result, that action carries no public
content of its own: a cell bound to failure publishes failure whatever its
owner later decides, exactly as a bound value that is never disclosed does.

This module names the policies that never bind failure, shows that class is
inhabited, and proves the semantic fact the redundancy rests on. The strategic
statement — that every policy has a value-binding one with the same public
outcome law — is a separate edge and is not proved here.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A policy that never binds an unopenable candidate. -/
def ValueBinding {who : Player} : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → BehavioralPolicy who p → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample _ _ _ k, policy => ValueBinding k policy
  | _, _, .commit _ owner _ _ k, policy =>
      (∀ (own : owner = who) view, PublicationResult.failure ∉ (policy.1 own view).support) ∧
        ValueBinding k policy.2
  | _, _, .reveal _ _ _ _ _ _ k, policy => ValueBinding k policy.2

/-- Bind the canonical value of every payload and disclose nothing. -/
def bindingPolicy (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → BehavioralPolicy who p
  | _, _, .ret _ => PUnit.unit
  | _, _, .sample _ _ _ k => bindingPolicy who k
  | _, _, .commit (payload := payload) _ _ _ _ k =>
      (fun _ _ => FinDist.pure (.success (L.someValue payload)), bindingPolicy who k)
  | _, _, .reveal _ _ _ _ _ _ k =>
      (fun _ _ => FinDist.pure false, bindingPolicy who k)

theorem valueBinding_bindingPolicy (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    ValueBinding p (bindingPolicy who p)
  | _, _, .ret _ => trivial
  | _, _, .sample _ _ _ k => valueBinding_bindingPolicy who k
  | _, _, .commit _ _ _ _ k =>
      ⟨fun _ _ => by simp [bindingPolicy], valueBinding_bindingPolicy who k⟩
  | _, _, .reveal _ _ _ _ _ _ k => valueBinding_bindingPolicy who k

/-- The value-binding policies are inhabited for every program. -/
theorem exists_valueBinding (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (p : SourceProgram Player L Γ O) :
    ∃ policy : BehavioralPolicy who p, ValueBinding p policy :=
  ⟨bindingPolicy who p, valueBinding_bindingPolicy who p⟩

/-! ## Pure policies

A pure policy chooses an action outright rather than a law over actions. These
are what a predraw produces, and they are the policies whose own past decisions
can be recomputed rather than remembered, which is what lets a translation
detect the bindings it replaced. -/

/-- A policy that acts without randomizing. -/
def PurePolicy (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Type
  | _, _, .ret _ => PUnit
  | _, _, .sample _ _ _ k => PurePolicy who k
  | Γ, _, .commit (payload := payload) _ owner _ _ k =>
      ((owner = who) → DecisionView who Γ → PublicationResult (L.Val payload)) ×
        PurePolicy who k
  | Γ, _, .reveal _ owner _ _ _ _ k =>
      ((owner = who) → DecisionView who Γ → Bool) × PurePolicy who k

/-- Read a pure policy as a behavioral one. -/
def PurePolicy.toBehavioral {who : Player} : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → PurePolicy who p → BehavioralPolicy who p
  | _, _, .ret _, _ => PUnit.unit
  | _, _, .sample _ _ _ k, policy => toBehavioral k policy
  | _, _, .commit _ _ _ _ k, policy =>
      (fun own view => FinDist.pure (policy.1 own view), toBehavioral k policy.2)
  | _, _, .reveal _ _ _ _ _ _ k, policy =>
      (fun own view => FinDist.pure (policy.1 own view), toBehavioral k policy.2)

/-- The decision view one step earlier: drop the newest cell, and drop the
newest own action when that step was this player's own. How far back a view has
to be carried is fixed by position in the program, which is why a pure policy
can recompute a decision it made earlier instead of remembering it. -/
def DecisionView.back {who : Player} {Γ : SourceCtx Player L} {x : VarId}
    {c : CellTy Player L} (ownStep : Bool) (view : DecisionView who ((x, c) :: Γ)) :
    DecisionView who Γ :=
  (⟨fun _ cell h => view.1.cells _ cell (.there h)⟩,
    if ownStep then view.2.dropLast else view.2)

/-- Which private cells hold a binding the translation put there, as a function
of the translated player's current view. -/
abbrev PatchMap (who : Player) (Γ : SourceCtx Player L) :=
  ∀ {n : VarId} {o : Player} {pay : L.Ty}, HasVar Γ n (.privateData o pay) →
    DecisionView who Γ → Bool

/-- The view the original policy would have held, read off the translated one. -/
abbrev ViewMap (who : Player) (Γ : SourceCtx Player L) :=
  DecisionView who Γ → DecisionView who Γ

/-- Carry the view map across a public sample. -/
def ViewMap.afterSample {who : Player} {Γ : SourceCtx Player L} (unpatch : ViewMap who Γ)
    (name : VarId) (payload : L.Ty) :
    ViewMap who ((name, .publicData payload) :: Γ) := fun view =>
  let earlier := unpatch (view.back false)
  (⟨fun _ cell h =>
    match h with
    | .here => view.1.cells name (.publicData payload) .here
    | .there h' => earlier.1.cells _ cell h'⟩, earlier.2)

/-- Carry the patch map across a public sample. -/
def PatchMap.afterSample {who : Player} {Γ : SourceCtx Player L} (patched : PatchMap who Γ)
    (name : VarId) (payload : L.Ty) :
    PatchMap who ((name, .publicData payload) :: Γ) := fun h view =>
  match h with
  | .there h' => patched h' (view.back false)

/-- Carry the view map across a binding, undoing a replacement at the new cell.
`original` is the binding the untranslated policy would have chosen. -/
def ViewMap.afterCommit {who : Player} {Γ : SourceCtx Player L} (unpatch : ViewMap who Γ)
    (ownStep : Bool) (cellName : VarId) (owner : Player) (payload : L.Ty)
    (original : DecisionView who Γ → Option (PublicationResult (L.Val payload))) :
    ViewMap who ((cellName, .privateData owner payload) :: Γ) := fun view =>
  let earlier := unpatch (view.back ownStep)
  let replaced : Bool := original (view.back ownStep) = some .failure
  (⟨fun _ cell h =>
    match h with
    | .here => if replaced then some .failure else view.1.cells cellName _ .here
    | .there h' => earlier.1.cells _ cell h'⟩,
    if ownStep then
      earlier.2 ++ ((original (view.back ownStep)).toList.map
        (OwnAction.commit owner cellName payload))
    else earlier.2)

/-- Carry the patch map across a binding, recording whether it was replaced. -/
def PatchMap.afterCommit {who : Player} {Γ : SourceCtx Player L} (patched : PatchMap who Γ)
    (ownStep : Bool) (cellName : VarId) (owner : Player) (payload : L.Ty)
    (original : DecisionView who Γ → Option (PublicationResult (L.Val payload))) :
    PatchMap who ((cellName, .privateData owner payload) :: Γ) := fun h view =>
  match h with
  | .here => original (view.back ownStep) = some .failure
  | .there h' => patched h' (view.back ownStep)

/-- Carry the view map across a publication, restoring the disclosure decision
the untranslated policy would have made. -/
def ViewMap.afterReveal {who : Player} {Γ : SourceCtx Player L} (unpatch : ViewMap who Γ)
    (ownStep : Bool) (published cellName : VarId) (owner : Player) (payload : L.Ty)
    (original : DecisionView who Γ → Option Bool) :
    ViewMap who ((published, .publication payload) :: Γ) := fun view =>
  let earlier := unpatch (view.back ownStep)
  (⟨fun _ cell h =>
    match h with
    | .here => view.1.cells published (.publication payload) .here
    | .there h' => earlier.1.cells _ cell h'⟩,
    if ownStep then
      earlier.2 ++ ((original (view.back ownStep)).toList.map (OwnAction.reveal owner cellName))
    else earlier.2)

/-- Carry the patch map across a publication. -/
def PatchMap.afterReveal {who : Player} {Γ : SourceCtx Player L} (patched : PatchMap who Γ)
    (ownStep : Bool) (published : VarId) (payload : L.Ty) :
    PatchMap who ((published, .publication payload) :: Γ) := fun h view =>
  match h with
  | .there h' => patched h' (view.back ownStep)

/-- Replace every unopenable binding by the canonical value of its payload, and
refuse to open exactly the cells that were replaced. Both are decided by
recomputing the original policy's decision at the view it held, which the two
carried maps reconstruct: `patched` says which bindings were replaced, and
`unpatch` undoes the replacement in the view before the original sees it.

The translation lands in `ValueBinding`. That it preserves the public outcome
law is the edge's deviation certificate and is not proved here. -/
def PurePolicy.bindValuesFrom {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    ViewMap who Γ → PatchMap who Γ → PurePolicy who p → PurePolicy who p
  | _, _, .ret _, _, _, _ => PUnit.unit
  | _, _, .sample (payload := payload) sampleName _ _ k, unpatch, patched, policy =>
      bindValuesFrom k (unpatch.afterSample sampleName payload)
        (patched.afterSample sampleName payload) policy
  | _, _, .commit (payload := payload) cellName owner _ _ k, unpatch, patched, policy =>
      let ownStep : Bool := decide (owner = who)
      let original : DecisionView who _ → Option (PublicationResult (L.Val payload)) :=
        fun view => if own : owner = who then some (policy.1 own (unpatch view)) else none
      (fun own view =>
        match policy.1 own (unpatch view) with
        | .failure => .success (L.someValue payload)
        | .success value => .success value,
       bindValuesFrom k (unpatch.afterCommit ownStep cellName owner payload original)
        (patched.afterCommit ownStep cellName owner payload original) policy.2)
  | _, _, .reveal (payload := payload) published owner cellName _ source _ k,
      unpatch, patched, policy =>
      let ownStep : Bool := decide (owner = who)
      let original : DecisionView who _ → Option Bool :=
        fun view => if own : owner = who then some (policy.1 own (unpatch view)) else none
      (fun own view => if patched source view then false else policy.1 own (unpatch view),
       bindValuesFrom k
        (unpatch.afterReveal ownStep published cellName owner payload original)
        (patched.afterReveal ownStep published payload) policy.2)

/-- The translation of a pure policy, starting from a context in which nothing
has been replaced yet. -/
def PurePolicy.bindValues {who : Player} {Γ : SourceCtx Player L} {O : Finset VarId}
    (p : SourceProgram Player L Γ O) (policy : PurePolicy who p) : PurePolicy who p :=
  bindValuesFrom p id (fun _ _ => false) policy

theorem valueBinding_bindValuesFrom {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    (unpatch : ViewMap who Γ) → (patched : PatchMap who Γ) → (policy : PurePolicy who p) →
    ValueBinding p
      (PurePolicy.toBehavioral p (PurePolicy.bindValuesFrom p unpatch patched policy))
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ k, _, _, policy => valueBinding_bindValuesFrom k _ _ policy
  | _, _, .commit _ _ _ _ k, unpatch, _, policy => by
      refine ⟨fun own view => ?_, valueBinding_bindValuesFrom k _ _ policy.2⟩
      simp only [PurePolicy.toBehavioral, PurePolicy.bindValuesFrom, FinDist.mem_support_pure]
      cases policy.1 own (unpatch view) <;> simp
  | _, _, .reveal _ _ _ _ _ _ k, _, _, policy => valueBinding_bindValuesFrom k _ _ policy.2

/-- The translation of any pure policy never binds an unopenable candidate. -/
theorem valueBinding_bindValues {who : Player} {Γ : SourceCtx Player L} {O : Finset VarId}
    (p : SourceProgram Player L Γ O) (policy : PurePolicy who p) :
    ValueBinding p (PurePolicy.toBehavioral p (PurePolicy.bindValues p policy)) :=
  valueBinding_bindValuesFrom p _ _ policy

variable {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId} {owner : Player}
variable {payload : L.Ty}

/-! ## Relating a translated run to the original

The two runs differ only in the translated player's own bindings, and only where
the translation replaced one. Everything a payoff, a guard, or another player
can read agrees. -/

/-- The translated configuration, related to the original's. -/
structure Patched {who : Player} {Γ : SourceCtx Player L}
    (unpatch : ViewMap who Γ) (patched : PatchMap who Γ)
    (state state' : State L Γ) (history history' : History Player L) : Prop where
  /-- Public data agrees. -/
  publicEq : ∀ {x τ} (h : HasVar Γ x (.publicData τ)), state'.get h = state.get h
  /-- Publications agree. -/
  publicationEq : ∀ {x τ} (h : HasVar Γ x (.publication τ)), state'.get h = state.get h
  /-- Another player's binding agrees. -/
  foreignEq : ∀ {x o τ} (h : HasVar Γ x (.privateData o τ)), o ≠ who →
    state'.get h = state.get h
  /-- The translated player's bindings are the original's with failures
  replaced. -/
  ownEq : ∀ {x τ} (h : HasVar Γ x (.privateData who τ)),
    state'.get h =
      match state.get h with
      | .failure => .success (L.someValue τ)
      | .success value => .success value
  /-- Another player's own history agrees. -/
  historyEq : ∀ other, other ≠ who → history' other = history other
  /-- The carried view map really does undo the replacement. -/
  unpatchEq : unpatch (sourceObserve who state', history' who) =
    (sourceObserve who state, history who)
  /-- The carried patch map really does say which bindings were replaced. -/
  patchedEq : ∀ {x τ} (h : HasVar Γ x (.privateData who τ)),
    patched h (sourceObserve who state', history' who) = decide (state.get h = .failure)

omit [IExpr.ResultTypes L] in
@[simp] theorem back_sourceObserve {who : Player} {Γ : SourceCtx Player L} {x : VarId}
    {c : CellTy Player L} (value : CellVal L c) (state : State L Γ)
    (history : List (OwnAction Player L)) (ownStep : Bool) :
    DecisionView.back (who := who) (x := x) ownStep
        (sourceObserve who (Env.cons (x := x) value state), history) =
      (sourceObserve who state, if ownStep then history.dropLast else history) := by
  refine Prod.ext ?_ rfl
  refine congrArg SourceObservation.mk ?_
  funext n cell h
  cases cell <;> rfl

/-! ## Invariant preservation, step by step -/

omit [IExpr.ResultTypes L] in
theorem patched_sample {who : Player} {Γ : SourceCtx Player L}
    {unpatch : ViewMap who Γ} {patched : PatchMap who Γ}
    {state state' : State L Γ} {history history' : History Player L}
    (inv : Patched unpatch patched state state' history history')
    (name : VarId) (payload : L.Ty) (value : L.Val payload) :
    Patched (who := who) (unpatch.afterSample name payload) (patched.afterSample name payload)
      (Env.cons (x := name) (Val := CellVal L) (τ := .publicData payload) value state)
      (Env.cons (x := name) (Val := CellVal L) (τ := .publicData payload) value state')
      history history' where
  publicEq := fun h => match h with
    | .here => rfl
    | .there h' => inv.publicEq h'
  publicationEq := fun h => match h with | .there h' => inv.publicationEq h'
  foreignEq := fun h hne => match h with | .there h' => inv.foreignEq h' hne
  ownEq := fun h => match h with | .there h' => inv.ownEq h'
  historyEq := inv.historyEq
  unpatchEq := by
    simp only [ViewMap.afterSample, back_sourceObserve, Bool.false_eq_true, if_false]
    rw [inv.unpatchEq]
    refine Prod.ext ?_ rfl
    refine congrArg SourceObservation.mk ?_
    funext n cell h
    cases h with
    | here => rfl
    | there h' => cases cell <;> rfl
  patchedEq := fun h => match h with
    | .there h' => by
        simp only [PatchMap.afterSample, back_sourceObserve, Bool.false_eq_true, if_false]
        exact inv.patchedEq h'

omit [IExpr.ResultTypes L] in
/-- Invariant preservation across another player's binding. -/
theorem patched_commit_foreign {who : Player} {Γ : SourceCtx Player L}
    {unpatch : ViewMap who Γ} {patched : PatchMap who Γ}
    {state state' : State L Γ} {history history' : History Player L}
    (inv : Patched unpatch patched state state' history history')
    (cellName : VarId) (owner : Player) (payload : L.Ty) (foreign : owner ≠ who)
    (binding : PublicationResult (L.Val payload))
    (original : DecisionView who Γ → Option (PublicationResult (L.Val payload)))
    (noOriginal : ∀ view, original view = none) :
    Patched (who := who)
      (unpatch.afterCommit (decide (owner = who)) cellName owner payload original)
      (patched.afterCommit (decide (owner = who)) cellName owner payload original)
      (Env.cons (x := cellName) (Val := CellVal L) (τ := .privateData owner payload)
        binding state)
      (Env.cons (x := cellName) (Val := CellVal L) (τ := .privateData owner payload)
        binding state')
      (Function.update history owner
        (history owner ++ [OwnAction.commit owner cellName payload binding]))
      (Function.update history' owner
        (history' owner ++ [OwnAction.commit owner cellName payload binding])) where
  publicEq := fun h => match h with | .there h' => inv.publicEq h'
  publicationEq := fun h => match h with | .there h' => inv.publicationEq h'
  foreignEq := fun h hne => by
    cases h with
    | here => rfl
    | there h' => exact inv.foreignEq h' hne
  ownEq := fun h => by
    cases h with
    | here => exact absurd rfl foreign
    | there h' => exact inv.ownEq h'
  historyEq := by
    intro other hne
    by_cases same : other = owner
    · subst same
      simp only [Function.update_self, inv.historyEq other hne]
    · simp only [Function.update_of_ne same, inv.historyEq other hne]
  unpatchEq := by
    have hwho : decide (owner = who) = false := by simp [foreign]
    simp only [ViewMap.afterCommit, hwho, back_sourceObserve, Bool.false_eq_true, if_false,
      Function.update_of_ne (Ne.symm foreign), noOriginal, reduceCtorEq, decide_false]
    rw [inv.unpatchEq]
    refine Prod.ext ?_ rfl
    refine congrArg SourceObservation.mk ?_
    funext n cell h
    cases h with
    | here => simp [foreign]
    | there h' => cases cell <;> rfl
  patchedEq := fun h => by
    have hwho : decide (owner = who) = false := by simp [foreign]
    cases h with
    | here => exact absurd rfl foreign
    | there h' =>
        simp only [PatchMap.afterCommit, hwho, back_sourceObserve, Bool.false_eq_true, if_false,
          Function.update_of_ne (Ne.symm foreign)]
        exact inv.patchedEq h'

omit [IExpr.ResultTypes L] in
/-- Invariant preservation across the translated player's own binding. -/
theorem patched_commit_own {who : Player} {Γ : SourceCtx Player L}
    {unpatch : ViewMap who Γ} {patched : PatchMap who Γ}
    {state state' : State L Γ} {history history' : History Player L}
    (inv : Patched unpatch patched state state' history history')
    (cellName : VarId) (payload : L.Ty)
    (binding : PublicationResult (L.Val payload))
    (original : DecisionView who Γ → Option (PublicationResult (L.Val payload)))
    (hOriginal : original (sourceObserve who state', history' who) = some binding) :
    Patched (who := who)
      (unpatch.afterCommit (decide (who = who)) cellName who payload original)
      (patched.afterCommit (decide (who = who)) cellName who payload original)
      (Env.cons (x := cellName) (Val := CellVal L) (τ := .privateData who payload)
        binding state)
      (Env.cons (x := cellName) (Val := CellVal L) (τ := .privateData who payload)
        (match binding with
          | .failure => .success (L.someValue payload)
          | .success value => .success value) state')
      (Function.update history who
        (history who ++ [OwnAction.commit who cellName payload binding]))
      (Function.update history' who
        (history' who ++ [OwnAction.commit who cellName payload
          (match binding with
            | .failure => .success (L.someValue payload)
            | .success value => .success value)])) where
  publicEq := fun h => match h with | .there h' => inv.publicEq h'
  publicationEq := fun h => match h with | .there h' => inv.publicationEq h'
  foreignEq := fun h hne => by
    cases h with
    | here => exact absurd rfl hne
    | there h' => exact inv.foreignEq h' hne
  ownEq := fun h => by
    cases h with
    | here => cases binding <;> simp
    | there h' => exact inv.ownEq h'
  historyEq := by
    intro other hne
    simp only [Function.update_of_ne hne, inv.historyEq other hne]
  unpatchEq := by
    simp only [ViewMap.afterCommit, decide_true, back_sourceObserve, if_true,
      Function.update_self, List.dropLast_concat, hOriginal]
    rw [inv.unpatchEq]
    refine Prod.ext ?_ rfl
    refine congrArg SourceObservation.mk ?_
    funext n cell h
    cases h with
    | here => cases binding <;> simp
    | there h' => cases cell <;> rfl
  patchedEq := fun h => by
    cases h with
    | here =>
        simp only [PatchMap.afterCommit, decide_true, back_sourceObserve, if_true,
          Function.update_self, List.dropLast_concat, hOriginal, Env.cons_get_here]
        cases binding <;> simp
    | there h' =>
        simp only [PatchMap.afterCommit, decide_true, back_sourceObserve, if_true,
          Function.update_self, List.dropLast_concat, Env.cons_get_there]
        exact inv.patchedEq h'

omit [IExpr.ResultTypes L] in
/-- Invariant preservation across another player's publication. -/
theorem patched_reveal_foreign {who : Player} {Γ : SourceCtx Player L}
    {unpatch : ViewMap who Γ} {patched : PatchMap who Γ}
    {state state' : State L Γ} {history history' : History Player L}
    (inv : Patched unpatch patched state state' history history')
    (published cellName : VarId) (owner : Player) (payload : L.Ty) (foreign : owner ≠ who)
    (result : PublicationResult (L.Val payload)) (disclose : Bool)
    (original : DecisionView who Γ → Option Bool) :
    Patched (who := who)
      (unpatch.afterReveal (decide (owner = who)) published cellName owner payload original)
      (patched.afterReveal (decide (owner = who)) published payload)
      (Env.cons (x := published) (Val := CellVal L) (τ := .publication payload) result state)
      (Env.cons (x := published) (Val := CellVal L) (τ := .publication payload) result state')
      (Function.update history owner
        (history owner ++ [OwnAction.reveal owner cellName disclose]))
      (Function.update history' owner
        (history' owner ++ [OwnAction.reveal owner cellName disclose])) where
  publicEq := fun h => match h with | .there h' => inv.publicEq h'
  publicationEq := fun h => by
    cases h with
    | here => rfl
    | there h' => exact inv.publicationEq h'
  foreignEq := fun h hne => match h with | .there h' => inv.foreignEq h' hne
  ownEq := fun h => match h with | .there h' => inv.ownEq h'
  historyEq := by
    intro other hne
    by_cases same : other = owner
    · subst same
      simp only [Function.update_self, inv.historyEq other hne]
    · simp only [Function.update_of_ne same, inv.historyEq other hne]
  unpatchEq := by
    have hwho : decide (owner = who) = false := by simp [foreign]
    simp only [ViewMap.afterReveal, hwho, back_sourceObserve, Bool.false_eq_true, if_false,
      Function.update_of_ne (Ne.symm foreign)]
    rw [inv.unpatchEq]
    refine Prod.ext ?_ rfl
    refine congrArg SourceObservation.mk ?_
    funext n cell h
    cases h with
    | here => rfl
    | there h' => cases cell <;> rfl
  patchedEq := fun h => by
    have hwho : decide (owner = who) = false := by simp [foreign]
    cases h with
    | there h' =>
        simp only [PatchMap.afterReveal, hwho, back_sourceObserve, Bool.false_eq_true, if_false,
          Function.update_of_ne (Ne.symm foreign), Env.cons_get_there]
        exact inv.patchedEq h'

omit [IExpr.ResultTypes L] in
/-- Invariant preservation across the translated player's own publication. The
two runs may record different disclosure decisions; the carried view map
restores the original's. -/
theorem patched_reveal_own {who : Player} {Γ : SourceCtx Player L}
    {unpatch : ViewMap who Γ} {patched : PatchMap who Γ}
    {state state' : State L Γ} {history history' : History Player L}
    (inv : Patched unpatch patched state state' history history')
    (published cellName : VarId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (disclose translatedDisclose : Bool)
    (original : DecisionView who Γ → Option Bool)
    (hOriginal : original (sourceObserve who state', history' who) = some disclose) :
    Patched (who := who)
      (unpatch.afterReveal (decide (who = who)) published cellName who payload original)
      (patched.afterReveal (decide (who = who)) published payload)
      (Env.cons (x := published) (Val := CellVal L) (τ := .publication payload) result state)
      (Env.cons (x := published) (Val := CellVal L) (τ := .publication payload) result state')
      (Function.update history who (history who ++ [OwnAction.reveal who cellName disclose]))
      (Function.update history' who
        (history' who ++ [OwnAction.reveal who cellName translatedDisclose])) where
  publicEq := fun h => match h with | .there h' => inv.publicEq h'
  publicationEq := fun h => by
    cases h with
    | here => rfl
    | there h' => exact inv.publicationEq h'
  foreignEq := fun h hne => match h with | .there h' => inv.foreignEq h' hne
  ownEq := fun h => match h with | .there h' => inv.ownEq h'
  historyEq := by
    intro other hne
    simp only [Function.update_of_ne hne, inv.historyEq other hne]
  unpatchEq := by
    simp only [ViewMap.afterReveal, decide_true, back_sourceObserve, if_true,
      Function.update_self, List.dropLast_concat, hOriginal]
    rw [inv.unpatchEq]
    refine Prod.ext ?_ rfl
    refine congrArg SourceObservation.mk ?_
    funext n cell h
    cases h with
    | here => rfl
    | there h' => cases cell <;> rfl
  patchedEq := fun h => by
    cases h with
    | there h' =>
        simp only [PatchMap.afterReveal, decide_true, back_sourceObserve, if_true,
          Function.update_self, List.dropLast_concat, Env.cons_get_there]
        exact inv.patchedEq h'

/-! ## The public result sees only public cells -/

omit [DecidableEq Player] in
/-- Two states with the same public data and the same publications have the same
public result, whatever their private bindings are. -/
theorem sourcePublicEnv_congr :
    {Γ : SourceCtx Player L} → (left right : State L Γ) →
    (publicEq : ∀ {x τ} (h : HasVar Γ x (.publicData τ)), left.get h = right.get h) →
    (publicationEq : ∀ {x τ} (h : HasVar Γ x (.publication τ)), left.get h = right.get h) →
    sourcePublicEnv left = sourcePublicEnv right
  | [], _, _, _, _ => rfl
  | (_, .publicData _) :: tail, left, right, publicEq, publicationEq => by
      have tailEq := sourcePublicEnv_congr (Γ := tail)
        (fun _ _ h => left.get (HasVar.there h)) (fun _ _ h => right.get (HasVar.there h))
        (fun h => publicEq (HasVar.there h)) (fun h => publicationEq (HasVar.there h))
      simp only [sourcePublicEnv, publicEq HasVar.here, tailEq]
  | (_, .privateData _ _) :: tail, left, right, publicEq, publicationEq => by
      have tailEq := sourcePublicEnv_congr (Γ := tail)
        (fun _ _ h => left.get (HasVar.there h)) (fun _ _ h => right.get (HasVar.there h))
        (fun h => publicEq (HasVar.there h)) (fun h => publicationEq (HasVar.there h))
      simpa only [sourcePublicEnv] using tailEq
  | (_, .publication _) :: tail, left, right, publicEq, publicationEq => by
      have tailEq := sourcePublicEnv_congr (Γ := tail)
        (fun _ _ h => left.get (HasVar.there h)) (fun _ _ h => right.get (HasVar.there h))
        (fun h => publicEq (HasVar.there h)) (fun h => publicationEq (HasVar.there h))
      simp only [sourcePublicEnv, publicationEq HasVar.here, tailEq]

/-- A cell bound to failure publishes failure whatever its owner decides. The
disclosure decision is still recorded, because the owner may condition on it;
only the publication is settled in advance.

This is why binding an unopenable candidate adds nothing to the public result
that refusing to open a bound value does not already add. -/
theorem runWith_reveal_of_failure_bound
    {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.privateData owner payload)} {unresolved : name ∈ O}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (profile : BehavioralProfile
      (SourceProgram.reveal published owner name fresh source unresolved next))
    (state : State L Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (history : History Player L)
    (bound : state.get source = .failure) :
    runWith (.reveal published owner name fresh source unresolved next) profile state registry
        revelations history =
      (revealKernel profile (sourceObserve owner state, history owner)).bind fun disclose =>
        runWith next (afterReveal profile)
          (Env.cons (Val := CellVal (Player := Player) L) (x := published)
            (τ := .publication payload) PublicationResult.failure state)
          registry.weaken (revelations.reveal (published := published) source)
          (Function.update history owner
            (history owner ++ [OwnAction.reveal owner name disclose])) := by
  simp only [runWith, bound, ite_self]

end Vegas.SourceProgram
