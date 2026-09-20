/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Setup

/-! # Policies that bind a value

A source policy may bind an unopenable candidate, which is how the source
represents what a native player does when it commits to something that will
never open. Once an outcome is the public result, that action carries no public
content of its own: a cell bound to failure publishes failure whatever its
owner later decides, exactly as a bound value that is never disclosed does.

This module names the policies that never bind failure, shows that class is
inhabited, and proves that every *pure* policy has a value-binding one with the
same public outcome law, against any fixed opponents. That is the deviation
certificate the edge from the value-binding game needs, for the policies a
predraw would supply; carrying it to arbitrary behavioral policies is the
remaining step.
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

/-- The binding the untranslated policy would choose, when the cell is this
player's own. -/
def PurePolicy.commitChoice {who : Player} {Γ : SourceCtx Player L} (unpatch : ViewMap who Γ)
    (owner : Player) (payload : L.Ty)
    (kernel : (owner = who) → DecisionView who Γ → PublicationResult (L.Val payload)) :
    DecisionView who Γ → Option (PublicationResult (L.Val payload)) :=
  fun view => if own : owner = who then some (kernel own (unpatch view)) else none

/-- The disclosure the untranslated policy would choose, when the cell is this
player's own. -/
def PurePolicy.revealChoice {who : Player} {Γ : SourceCtx Player L} (unpatch : ViewMap who Γ)
    (owner : Player) (kernel : (owner = who) → DecisionView who Γ → Bool) :
    DecisionView who Γ → Option Bool :=
  fun view => if own : owner = who then some (kernel own (unpatch view)) else none

/-- Replace every unopenable binding by the canonical value of its payload, and
refuse to open exactly the cells that were replaced. Both are decided by
recomputing the original policy's decision at the view it held, which the two
carried maps reconstruct: `patched` says which bindings were replaced, and
`unpatch` undoes the replacement in the view before the original sees it.

The translation lands in `ValueBinding`, and preserves the public outcome law:
see `bindValues_publicOutcome_eq`. -/
def PurePolicy.bindValuesFrom {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    ViewMap who Γ → PatchMap who Γ → PurePolicy who p → PurePolicy who p
  | _, _, .ret _, _, _, _ => PUnit.unit
  | _, _, .sample (payload := payload) sampleName _ _ k, unpatch, patched, policy =>
      bindValuesFrom k (unpatch.afterSample sampleName payload)
        (patched.afterSample sampleName payload) policy
  | _, _, .commit (payload := payload) cellName owner _ _ k, unpatch, patched, policy =>
      let ownStep : Bool := decide (owner = who)
      let original := PurePolicy.commitChoice unpatch owner payload policy.1
      (fun own view =>
        match policy.1 own (unpatch view) with
        | .failure => .success (L.someValue payload)
        | .success value => .success value,
       bindValuesFrom k (unpatch.afterCommit ownStep cellName owner payload original)
        (patched.afterCommit ownStep cellName owner payload original) policy.2)
  | _, _, .reveal (payload := payload) published owner cellName _ source _ k,
      unpatch, patched, policy =>
      let ownStep : Bool := decide (owner = who)
      let original := PurePolicy.revealChoice unpatch owner policy.1
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
  /-- A binding the translation replaced was a failure, and now holds the
  canonical value. -/
  replacedEq : ∀ {x τ} (h : HasVar Γ x (.privateData who τ)),
    patched h (sourceObserve who state', history' who) = true →
      state.get h = .failure ∧ state'.get h = .success (L.someValue τ)
  /-- Every other binding of the translated player's agrees. Initial bindings
  are among these: the translation replaces only what a policy binds. -/
  keptEq : ∀ {x τ} (h : HasVar Γ x (.privateData who τ)),
    patched h (sourceObserve who state', history' who) = false →
      state'.get h = state.get h
  /-- Another player's own history agrees. -/
  historyEq : ∀ other, other ≠ who → history' other = history other
  /-- The carried view map really does undo the replacement. -/
  unpatchEq : unpatch (sourceObserve who state', history' who) =
    (sourceObserve who state, history who)

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
  replacedEq := fun h hp => match h with
    | .there h' => by
        simp only [PatchMap.afterSample, back_sourceObserve, Bool.false_eq_true,
          if_false] at hp
        exact inv.replacedEq h' hp
  keptEq := fun h hp => match h with
    | .there h' => by
        simp only [PatchMap.afterSample, back_sourceObserve, Bool.false_eq_true,
          if_false] at hp
        exact inv.keptEq h' hp
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
  replacedEq := fun h hp => by
    cases h with
    | here => exact absurd rfl foreign
    | there h' =>
        simp only [PatchMap.afterCommit, show decide (owner = who) = false by simp [foreign],
          back_sourceObserve, Bool.false_eq_true, if_false,
          Function.update_of_ne (Ne.symm foreign)] at hp
        exact inv.replacedEq h' hp
  keptEq := fun h hp => by
    cases h with
    | here => exact absurd rfl foreign
    | there h' =>
        simp only [PatchMap.afterCommit, show decide (owner = who) = false by simp [foreign],
          back_sourceObserve, Bool.false_eq_true, if_false,
          Function.update_of_ne (Ne.symm foreign)] at hp
        exact inv.keptEq h' hp
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

omit [IExpr.ResultTypes L] in
/-- Invariant preservation across the translated player's own binding. -/
theorem patched_commit_own {who : Player} {Γ : SourceCtx Player L}
    {unpatch : ViewMap who Γ} {patched : PatchMap who Γ}
    {state state' : State L Γ} {history history' : History Player L}
    (inv : Patched unpatch patched state state' history history')
    (cellName : VarId) (payload : L.Ty)
    (binding translated : PublicationResult (L.Val payload))
    (hTranslated : translated =
      match binding with
      | .failure => .success (L.someValue payload)
      | .success value => .success value)
    (original : DecisionView who Γ → Option (PublicationResult (L.Val payload)))
    (hOriginal : original (sourceObserve who state', history' who) = some binding) :
    Patched (who := who)
      (unpatch.afterCommit (decide (who = who)) cellName who payload original)
      (patched.afterCommit (decide (who = who)) cellName who payload original)
      (Env.cons (x := cellName) (Val := CellVal L) (τ := .privateData who payload)
        binding state)
      (Env.cons (x := cellName) (Val := CellVal L) (τ := .privateData who payload)
        translated state')
      (Function.update history who
        (history who ++ [OwnAction.commit who cellName payload binding]))
      (Function.update history' who
        (history' who ++ [OwnAction.commit who cellName payload translated])) where
  publicEq := fun h => match h with | .there h' => inv.publicEq h'
  publicationEq := fun h => match h with | .there h' => inv.publicationEq h'
  foreignEq := fun h hne => by
    cases h with
    | here => exact absurd rfl hne
    | there h' => exact inv.foreignEq h' hne
  replacedEq := fun h hp => by
    subst hTranslated
    cases h with
    | here =>
        simp only [PatchMap.afterCommit, decide_true, back_sourceObserve, if_true,
          Function.update_self, List.dropLast_concat, hOriginal] at hp
        cases binding with
        | failure => exact ⟨rfl, rfl⟩
        | success value => simp at hp
    | there h' =>
        simp only [PatchMap.afterCommit, decide_true, back_sourceObserve, if_true,
          Function.update_self, List.dropLast_concat] at hp
        exact inv.replacedEq h' hp
  keptEq := fun h hp => by
    subst hTranslated
    cases h with
    | here =>
        simp only [PatchMap.afterCommit, decide_true, back_sourceObserve, if_true,
          Function.update_self, List.dropLast_concat, hOriginal] at hp
        cases binding with
        | failure => simp at hp
        | success value => rfl
    | there h' =>
        simp only [PatchMap.afterCommit, decide_true, back_sourceObserve, if_true,
          Function.update_self, List.dropLast_concat] at hp
        exact inv.keptEq h' hp
  historyEq := by
    intro other hne
    simp only [Function.update_of_ne hne, inv.historyEq other hne]
  unpatchEq := by
    subst hTranslated
    simp only [ViewMap.afterCommit, decide_true, back_sourceObserve, if_true,
      Function.update_self, List.dropLast_concat, hOriginal]
    rw [inv.unpatchEq]
    refine Prod.ext ?_ rfl
    refine congrArg SourceObservation.mk ?_
    funext n cell h
    cases h with
    | here => cases binding <;> simp
    | there h' => cases cell <;> rfl

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
  replacedEq := fun h hp => match h with
    | .there h' => by
        simp only [PatchMap.afterReveal, back_sourceObserve, Bool.false_eq_true, if_false,
          show decide (owner = who) = false by simp [foreign],
          Function.update_of_ne (Ne.symm foreign)] at hp
        exact inv.replacedEq h' hp
  keptEq := fun h hp => match h with
    | .there h' => by
        simp only [PatchMap.afterReveal, back_sourceObserve, Bool.false_eq_true, if_false,
          show decide (owner = who) = false by simp [foreign],
          Function.update_of_ne (Ne.symm foreign)] at hp
        exact inv.keptEq h' hp
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
  replacedEq := fun h hp => match h with
    | .there h' => by
        simp only [PatchMap.afterReveal, decide_true, back_sourceObserve, if_true,
          Function.update_self, List.dropLast_concat] at hp
        exact inv.replacedEq h' hp
  keptEq := fun h hp => match h with
    | .there h' => by
        simp only [PatchMap.afterReveal, decide_true, back_sourceObserve, if_true,
          Function.update_self, List.dropLast_concat] at hp
        exact inv.keptEq h' hp
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

/-! ## The certificate: the translation preserves the public outcome law -/

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem Revelation.result_congr {payload : L.Ty} (revelation : Revelation Γ payload)
    (left right : State L Γ)
    (publicationEq : ∀ {x τ} (h : HasVar Γ x (.publication τ)), left.get h = right.get h) :
    revelation.result left = revelation.result right := by
  cases revelation with
  | unrevealed => rfl
  | revealed cell => exact publicationEq cell

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem SourceGuardRead.result_congr {author : Player} {τ : L.Ty}
    (read : SourceGuardRead Γ author τ) (revelations : Revelations Γ)
    (left right : State L Γ)
    (publicEq : ∀ {x τ} (h : HasVar Γ x (.publicData τ)), left.get h = right.get h)
    (publicationEq : ∀ {x τ} (h : HasVar Γ x (.publication τ)), left.get h = right.get h) :
    read.result revelations left = read.result revelations right := by
  cases read with
  | publicData h => exact congrArg _ (publicEq h)
  | privateData h => exact Revelation.result_congr _ _ _ publicationEq
  | publication h => exact publicationEq h

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem Obligation.accepts_congr (obligation : Obligation Γ) (revelations : Revelations Γ)
    (left right : State L Γ)
    (publicEq : ∀ {x τ} (h : HasVar Γ x (.publicData τ)), left.get h = right.get h)
    (publicationEq : ∀ {x τ} (h : HasVar Γ x (.publication τ)), left.get h = right.get h) :
    obligation.accepts revelations left = obligation.accepts revelations right := by
  simp only [Obligation.accepts, SourceGuard.accepts,
    Revelation.result_congr _ left right publicationEq]
  refine congrArg _ ?_
  funext x τ h hx
  exact SourceGuardRead.result_congr _ _ left right publicEq publicationEq

omit [IExpr.ResultTypes L] in
/-- The two runs propose the same publication at the translated player's own
reveal: a replaced binding is refused, and any other binding is unchanged. -/
theorem proposal_eq {who : Player} {Γ : SourceCtx Player L}
    {unpatch : ViewMap who Γ} {patched : PatchMap who Γ}
    {state state' : State L Γ} {history history' : History Player L}
    (inv : Patched unpatch patched state state' history history')
    {name : VarId} {payload : L.Ty} (source : HasVar Γ name (.privateData who payload))
    (disclose : Bool) :
    (if (if patched source (sourceObserve who state', history' who) then false else disclose)
        then state'.get source else .failure) =
      (if disclose then state.get source else .failure) := by
  cases hp : patched source (sourceObserve who state', history' who) with
  | true => simp [(inv.replacedEq source hp).1]
  | false => simp [inv.keptEq source hp]

theorem bindValues_publicOutcome_eq {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    (unpatch : ViewMap who Γ) → (patched : PatchMap who Γ) → (policy : PurePolicy who p) →
    (profile profile' : BehavioralProfile p) →
    (∀ other, other ≠ who → profile' other = profile other) →
    profile who = PurePolicy.toBehavioral p policy →
    profile' who =
      PurePolicy.toBehavioral p (PurePolicy.bindValuesFrom p unpatch patched policy) →
    (state state' : State L Γ) → (registry : Registry Γ) → (revelations : Revelations Γ) →
    (history history' : History Player L) →
    Patched unpatch patched state state' history history' →
    (runWith p profile' state' registry revelations history').map (publicOutcome p) =
      (runWith p profile state registry revelations history).map (publicOutcome p)
  | _, _, .ret payoffs, _, _, _, profile, profile', _, _, _, state, state', registry,
      revelations, history, history', inv => by
      simp only [runWith, FinDist.map_pure]
      exact congrArg FinDist.pure
        (sourcePublicEnv_congr state' state inv.publicEq inv.publicationEq)
  | _, _, .sample sampleName fresh law k, unpatch, patched, policy, profile, profile',
      agree, isOrig, isTrans, state, state', registry, revelations, history, history', inv => by
      simp only [runWith, FinDist.map_bind]
      rw [sourcePublicEnv_congr state' state inv.publicEq inv.publicationEq]
      refine FinDist.bind_congr fun a _ => ?_
      exact bindValues_publicOutcome_eq k (unpatch.afterSample sampleName _)
        (patched.afterSample sampleName _) policy (afterSample profile) (afterSample profile')
        agree isOrig isTrans _ _ _ _ _ _ (patched_sample inv sampleName _ a)
  | _, _, .commit (payload := payload) cellName owner fresh guard k, unpatch, patched, policy,
      profile, profile', agree, isOrig, isTrans, state, state', registry, revelations,
      history, history', inv => by
      simp only [runWith, FinDist.map_bind]
      by_cases hw : owner = who
      · subst hw
        have hview : unpatch (sourceObserve owner state', history' owner) =
            (sourceObserve owner state, history owner) := inv.unpatchEq
        have hl : commitKernel profile' (sourceObserve owner state', history' owner) =
            FinDist.pure (match policy.1 rfl (sourceObserve owner state, history owner) with
              | .failure => .success (L.someValue payload)
              | .success value => .success value) := by
          rw [commitKernel, isTrans]
          simp only [PurePolicy.toBehavioral, PurePolicy.bindValuesFrom, hview]
        have hr : commitKernel profile (sourceObserve owner state, history owner) =
            FinDist.pure (policy.1 rfl (sourceObserve owner state, history owner)) := by
          rw [commitKernel, isOrig]
          rfl
        rw [hl, hr, FinDist.pure_bind, FinDist.pure_bind]
        refine bindValues_publicOutcome_eq k _ _ policy.2 (afterCommit profile)
          (afterCommit profile') (fun other hne => congrArg Prod.snd (agree other hne))
          (congrArg Prod.snd isOrig) (congrArg Prod.snd isTrans) _ _ _ _ _ _
          (patched_commit_own inv cellName payload
            (policy.1 rfl (sourceObserve owner state, history owner)) _ rfl
            (PurePolicy.commitChoice unpatch owner payload policy.1) ?_)
        simp [PurePolicy.commitChoice, hview]
      · have hobs : sourceObserve owner state' = sourceObserve owner state :=
          sourceObserve_congr owner state' state inv.publicEq inv.publicationEq
            (fun h => inv.foreignEq h hw)
        have hhist : history' owner = history owner := inv.historyEq owner hw
        have hkernel : commitKernel profile' (sourceObserve owner state', history' owner) =
            commitKernel profile (sourceObserve owner state, history owner) := by
          rw [commitKernel, commitKernel, hobs, hhist, agree owner hw]
        rw [hkernel]
        refine FinDist.bind_congr fun b _ => ?_
        exact bindValues_publicOutcome_eq k _ _ policy.2 (afterCommit profile)
          (afterCommit profile') (fun other hne => congrArg Prod.snd (agree other hne))
          (congrArg Prod.snd isOrig) (congrArg Prod.snd isTrans) _ _ _ _ _ _
          (patched_commit_foreign inv cellName owner payload hw b
            (PurePolicy.commitChoice unpatch owner payload policy.1)
            (fun view => dif_neg hw))
  | _, _, .reveal (payload := payload) published owner cellName fresh source unresolved k,
      unpatch, patched, policy, profile, profile', agree, isOrig, isTrans, state, state',
      registry, revelations, history, history', inv => by
      have haccept : ∀ (proposal : PublicationResult (L.Val payload)),
          (registry.completedBy (published := published) revelations source).all
              (·.accepts (revelations.reveal (published := published) source)
                (Env.cons (Val := CellVal (Player := Player) L) (x := published)
                  (τ := .publication payload) proposal state')) =
            (registry.completedBy (published := published) revelations source).all
              (·.accepts (revelations.reveal (published := published) source)
                (Env.cons (Val := CellVal (Player := Player) L) (x := published)
                  (τ := .publication payload) proposal state)) := by
        intro proposal
        refine congrArg (List.all _) (funext fun obligation => ?_)
        exact Obligation.accepts_congr obligation _ _ _
          (fun h => match h with
            | .there h' => inv.publicEq h')
          (fun h => match h with
            | .here => rfl
            | .there h' => inv.publicationEq h')
      simp only [runWith, FinDist.map_bind]
      by_cases hw : owner = who
      · subst hw
        have hview : unpatch (sourceObserve owner state', history' owner) =
            (sourceObserve owner state, history owner) := inv.unpatchEq
        have hl : revealKernel profile' (sourceObserve owner state', history' owner) =
            FinDist.pure (if patched source (sourceObserve owner state', history' owner) then
              false else policy.1 rfl (sourceObserve owner state, history owner)) := by
          rw [revealKernel, isTrans]
          simp only [PurePolicy.toBehavioral, PurePolicy.bindValuesFrom, hview]
        have hr : revealKernel profile (sourceObserve owner state, history owner) =
            FinDist.pure (policy.1 rfl (sourceObserve owner state, history owner)) := by
          rw [revealKernel, isOrig]
          rfl
        rw [hl, hr, FinDist.pure_bind, FinDist.pure_bind,
          proposal_eq inv source (policy.1 rfl (sourceObserve owner state, history owner)),
          haccept]
        exact bindValues_publicOutcome_eq k _ _ policy.2 (afterReveal profile)
          (afterReveal profile') (fun other hne => congrArg Prod.snd (agree other hne))
          (congrArg Prod.snd isOrig) (congrArg Prod.snd isTrans) _ _ _ _ _ _
          (patched_reveal_own inv published cellName payload _ _ _
            (PurePolicy.revealChoice unpatch owner policy.1) (by
              simp [PurePolicy.revealChoice, hview]))
      · have hobs : sourceObserve owner state' = sourceObserve owner state :=
          sourceObserve_congr owner state' state inv.publicEq inv.publicationEq
            (fun h => inv.foreignEq h hw)
        have hhist : history' owner = history owner := inv.historyEq owner hw
        have hkernel : revealKernel profile' (sourceObserve owner state', history' owner) =
            revealKernel profile (sourceObserve owner state, history owner) := by
          rw [revealKernel, revealKernel, hobs, hhist, agree owner hw]
        have hcell : state'.get source = state.get source := inv.foreignEq source hw
        rw [hkernel]
        refine FinDist.bind_congr fun disclose _ => ?_
        rw [hcell, haccept]
        exact bindValues_publicOutcome_eq k _ _ policy.2 (afterReveal profile)
          (afterReveal profile') (fun other hne => congrArg Prod.snd (agree other hne))
          (congrArg Prod.snd isOrig) (congrArg Prod.snd isTrans) _ _ _ _ _ _
          (patched_reveal_foreign inv published cellName owner payload hw _ disclose
            (PurePolicy.revealChoice unpatch owner policy.1))

/-! ## From a fixed start, and across a private setup law -/

omit [L.ResultTypes] in
/-- Before anything is bound, nothing has been replaced. -/
theorem patched_initial {who : Player} {Γ : SourceCtx Player L} (state : State L Γ) :
    Patched (who := who) id (fun _ _ => false) state state (fun _ => []) (fun _ => []) where
  publicEq := fun _ => rfl
  publicationEq := fun _ => rfl
  foreignEq := fun _ _ => rfl
  replacedEq := fun _ hp => absurd hp (by simp)
  keptEq := fun _ _ => rfl
  historyEq := fun _ _ => rfl
  unpatchEq := rfl

/-- A pure policy and its value-binding translation induce the same public
result law from any starting state, against unchanged opponents. -/
theorem bindValues_run_publicOutcome_eq {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (p : SourceProgram Player L Γ O) (profile : BehavioralProfile p)
    (policy : PurePolicy who p) (state : State L Γ) :
    (run p (Function.update profile who
        (PurePolicy.toBehavioral p (PurePolicy.bindValues p policy))) state).map
        (publicOutcome p) =
      (run p (Function.update profile who (PurePolicy.toBehavioral p policy)) state).map
        (publicOutcome p) :=
  bindValues_publicOutcome_eq p id (fun _ _ => false) policy _ _
    (fun other hne => by
      simp only [Function.update_of_ne hne])
    (Function.update_self ..) (Function.update_self ..) state state _ _ _ _
    (patched_initial state)

/-- The same across a private setup law: one translation serves the whole law,
because it never consults the draw. -/
theorem bindValues_publicRun_eq {who : Player} (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) (policy : PurePolicy who setup.program) :
    setup.publicRun (Function.update profile who
        (PurePolicy.toBehavioral setup.program (PurePolicy.bindValues setup.program policy))) =
      setup.publicRun (Function.update profile who
        (PurePolicy.toBehavioral setup.program policy)) := by
  simp only [Setup.publicRun, Setup.run, FinDist.map_bind]
  exact FinDist.bind_congr fun initial _ =>
    bindValues_run_publicOutcome_eq setup.program profile policy initial

/-- Every pure policy is matched by a policy that binds a value and has the
same public result law, against unchanged opponents. Binding an unopenable
candidate buys a pure deviator nothing. -/
theorem exists_valueBinding_publicRun_eq {who : Player}
    (setup : Setup (Player := Player) (L := L)) (profile : BehavioralProfile setup.program)
    (policy : PurePolicy who setup.program) :
    ∃ alternative : BehavioralPolicy who setup.program, ValueBinding setup.program alternative ∧
      setup.publicRun (Function.update profile who alternative) =
        setup.publicRun (Function.update profile who
          (PurePolicy.toBehavioral setup.program policy)) :=
  ⟨PurePolicy.toBehavioral setup.program (PurePolicy.bindValues setup.program policy),
    valueBinding_bindValues setup.program policy,
    bindValues_publicRun_eq setup profile policy⟩

/-! ## The value-binding game

The game a source program presents once a binding must carry a value. Only the
strategies change: the program, the setup law and the public outcome are the
same, so the two games are compared by the identity on outcomes. -/

/-- A policy that never binds an unopenable candidate, as a strategy. -/
def ValueBindingPolicy (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (p : SourceProgram Player L Γ O) : Type :=
  {policy : BehavioralPolicy who p // ValueBinding p policy}

instance {who : Player} {Γ : SourceCtx Player L} {O : Finset VarId}
    {p : SourceProgram Player L Γ O} : Inhabited (ValueBindingPolicy who p) :=
  ⟨bindingPolicy who p, valueBinding_bindingPolicy who p⟩

/-- The policies underlying a value-binding profile. -/
def valueBindingProfile {Γ : SourceCtx Player L} {O : Finset VarId}
    {p : SourceProgram Player L Γ O} (profile : ∀ who, ValueBindingPolicy who p) :
    BehavioralProfile p := fun who => (profile who).val

namespace Setup

/-- The value-binding game of a setup. -/
def valueBindingGame (setup : Setup (Player := Player) (L := L)) : GameForm Player where
  sig :=
    { Strategy := fun who => ValueBindingPolicy who setup.program
      Outcome := SourceProgram.PublicOutcome setup.program }
  play profile := setup.publicRun (valueBindingProfile profile)

@[simp] theorem valueBindingGame_play (setup : Setup (Player := Player) (L := L))
    (profile : Profile setup.valueBindingGame.sig) :
    setup.valueBindingGame.play profile = setup.publicRun (valueBindingProfile profile) := rfl

/-- Replacing one strategy of a value-binding profile replaces one policy. -/
@[simp] theorem valueBindingProfile_update (setup : Setup (Player := Player) (L := L))
    (profile : Profile setup.valueBindingGame.sig) (who : Player)
    (replacement : setup.valueBindingGame.sig.Strategy who) :
    valueBindingProfile (Profile.update profile who replacement) =
      Function.update (valueBindingProfile profile) who replacement.val := by
  funext actor
  by_cases h : actor = who
  · subst h; simp [valueBindingProfile]
  · simp [valueBindingProfile, Profile.update_of_ne _ _ h, Function.update_of_ne h]

end Setup

end Vegas.SourceProgram
