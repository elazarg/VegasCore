/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Basic
import Vegas.Foundation.DefaultHistory
import GameTheory.Core.Form

/-! # Source policies and exact execution

Policies decide only while their owner has not publicly defaulted.
Execution follows source order and interprets chance through the exact finite
law carried by source syntax. Each retained guard obligation is checked once, at
the reveal that publishes the last of its inputs; a rejected check makes that
publication fail. Execution produces the detailed terminal state, which is what
the laws below are stated over. The public game interpretation projects to
public results; the parameter interpretation additionally retains initial types.
The public terminal projection retains both typed values and default status.
Executable transfers are evaluated separately from policy execution.
-/

noncomputable section
namespace Vegas
open GameTheory GameTheory.Math.Probability

def sourcePublicEnv {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L] :
    {Γ : SourceCtx Player L} → State L Γ → Env L.Val (SourcePublicCtx L Γ)
  | [], _ => Env.empty L.Val
  | (_, .publicData _) :: _, s => Env.cons (s.get .here)
      (sourcePublicEnv fun _ _ h => s.get (HasVar.there h))
  | (_, .commitment _ _) :: tail, s => sourcePublicEnv (Player := Player) (L := L)
      (R := R) (Γ := tail) (fun _ _ h => s.get (HasVar.there h))
  | (_, .privateInput _ _) :: tail, s => sourcePublicEnv (Player := Player) (L := L)
      (R := R) (Γ := tail) (fun _ _ h => s.get (HasVar.there h))
  | (_, .publication τ) :: _, s =>
      Env.cons ((R.valueEquiv τ).symm (s.get .here))
        (sourcePublicEnv fun _ _ h => s.get (HasVar.there h))

def SourceObservationVal {Player : Type} (L : IExpr) :
    CellTy Player L → Type
  | .publicData τ => L.Val τ
  | .publication τ => PublicationResult (L.Val τ)
  | .commitment owner τ => Option (CellVal L (.commitment owner τ))
  | .privateInput _ τ => Option (L.Val τ)

structure SourceObservation {Player : Type} (L : IExpr) (who : Player)
    (Γ : SourceCtx Player L) where
  cells : Env (SourceObservationVal L) Γ

def sourceObserve {Player : Type} [DecidableEq Player] {L : IExpr} (who : Player) :
    {Γ : SourceCtx Player L} → State L Γ → SourceObservation L who Γ
  | _, s => ⟨fun _ cell h => match cell with
      | .publicData _ => s.get h
      | .publication _ => s.get h
      | .commitment owner _ => if owner = who then some (s.get h) else none
      | .privateInput owner _ => if owner = who then some (s.get h) else none⟩

section SourceObserve

variable {Player : Type} [DecidableEq Player] {L : IExpr} {Γ : SourceCtx Player L}

@[simp] theorem sourceObserve_publicData (who : Player) (state : State L Γ)
    {x : VarId} {τ : L.Ty} (h : HasVar Γ x (.publicData τ)) :
    (sourceObserve who state).cells x (.publicData τ) h = state.get h := rfl

@[simp] theorem sourceObserve_publication (who : Player) (state : State L Γ)
    {x : VarId} {τ : L.Ty} (h : HasVar Γ x (.publication τ)) :
    (sourceObserve who state).cells x (.publication τ) h = state.get h := rfl

@[simp] theorem sourceObserve_commitment (who : Player) (state : State L Γ)
    {x : VarId} {owner : Player} {τ : L.Ty} (h : HasVar Γ x (.commitment owner τ)) :
    (sourceObserve who state).cells x (.commitment owner τ) h =
      if owner = who then some (state.get h) else none := rfl

@[simp] theorem sourceObserve_privateInput (who : Player) (state : State L Γ)
    {x : VarId} {owner : Player} {τ : L.Ty} (h : HasVar Γ x (.privateInput owner τ)) :
    (sourceObserve who state).cells x (.privateInput owner τ) h =
      if owner = who then some (state.get h) else none := rfl

/-- A player's source observation depends only on public data, publication
results, and that player's own inputs and commitments. -/
theorem sourceObserve_congr (who : Player) (left right : State L Γ)
    (publicEq : ∀ {x τ} (h : HasVar Γ x (.publicData τ)), left.get h = right.get h)
    (publicationEq : ∀ {x τ} (h : HasVar Γ x (.publication τ)), left.get h = right.get h)
    (inputEq : ∀ {x τ} (h : HasVar Γ x (.privateInput who τ)), left.get h = right.get h)
    (ownEq : ∀ {x τ} (h : HasVar Γ x (.commitment who τ)), left.get h = right.get h) :
    sourceObserve who left = sourceObserve who right := by
  have cellsEq : (sourceObserve who left).cells = (sourceObserve who right).cells := by
    funext x cell h
    cases cell with
    | publicData τ =>
        rw [sourceObserve_publicData, sourceObserve_publicData, publicEq h]
    | publication τ =>
        rw [sourceObserve_publication, sourceObserve_publication, publicationEq h]
    | commitment owner τ =>
        rw [sourceObserve_commitment, sourceObserve_commitment]
        by_cases same : owner = who
        · subst same
          simp [ownEq h]
        · simp [same]
    | privateInput owner τ =>
        rw [sourceObserve_privateInput, sourceObserve_privateInput]
        by_cases same : owner = who
        · subst same
          simp [inputEq h]
        · simp [same]
  calc sourceObserve who left = ⟨(sourceObserve who left).cells⟩ := rfl
    _ = ⟨(sourceObserve who right).cells⟩ := by rw [cellsEq]
    _ = sourceObserve who right := rfl

end SourceObserve


namespace SourceProgram
variable {Player : Type} [DecidableEq Player] {L : IExpr} [resultTypes : IExpr.ResultTypes L]
variable {Γ : SourceCtx Player L} {O : Finset VarId} {name x : VarId} {owner : Player}
variable {payload : L.Ty} {c : CellTy Player L}

inductive OwnAction (Player : Type) (L : IExpr) where
  | commit (owner : Player) (name : VarId) (payload : L.Ty)
      (choice : Option (PublicationResult (L.Val payload)))
  | reveal (owner : Player) (name : VarId) (disclose : Bool)

abbrev History (Player : Type) (L : IExpr) := Player → List (OwnAction Player L)
/-- The cells, public default status and actual own choices visible to a player. -/
structure DecisionView (who : Player) (Γ : SourceCtx Player L) where
  observation : SourceObservation L who Γ
  defaults : DefaultHistory Player
  history : List (OwnAction Player L)

/-- The current public default set, derived from its complete public history. -/
def DecisionView.defaulted {who : Player} (view : DecisionView who Γ) : Finset Player :=
  view.defaults.defaulted

/-- A policy prescribing a law over actions at every decision point this player
owns. Reducible on purpose: its projections have to line up at reducible
transparency, or rewriting under a `.1`/`.2` silently declines to fire. -/
abbrev BehavioralPolicy (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Type
  | _, _, .ret _ => PUnit
  | _, _, .sample _ _ _ k => BehavioralPolicy who k
  | Γ, _, .commit (payload := payload) _ owner _ _ k =>
      ((owner = who) → (view : DecisionView who Γ) → who ∉ view.defaulted →
        PMF (Option (PublicationResult (L.Val payload)))) × BehavioralPolicy who k
  | Γ, _, .reveal _ owner _ _ _ _ k =>
      ((owner = who) → (view : DecisionView who Γ) → who ∉ view.defaulted → PMF Bool) ×
        BehavioralPolicy who k

/-- One policy per player. A profile here is a plain function, so a deviation
updates it at one coordinate; the game-form layer says the same thing as
`Profile.update`, which is definitionally equal. Bridge lemmas rewrite toward
the plain function update, because that is the form the laws below are stated
in. -/
abbrev BehavioralProfile {Γ : SourceCtx Player L} {O : Finset VarId}
    (p : SourceProgram Player L Γ O) := ∀ who, BehavioralPolicy who p

/-! ## Pure policies

A pure policy chooses an action outright rather than a law over actions. These
are what a predraw produces, and they are the policies whose own past decisions
can be recomputed rather than remembered. -/

/-- A policy that acts without randomizing. Reducible for the same reason as
`BehavioralPolicy`. -/
abbrev PurePolicy (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Type
  | _, _, .ret _ => PUnit
  | _, _, .sample _ _ _ k => PurePolicy who k
  | Γ, _, .commit (payload := payload) _ owner _ _ k =>
      ((owner = who) → (view : DecisionView who Γ) → who ∉ view.defaulted →
        Option (PublicationResult (L.Val payload))) ×
        PurePolicy who k
  | Γ, _, .reveal _ owner _ _ _ _ k =>
      ((owner = who) → (view : DecisionView who Γ) → who ∉ view.defaulted → Bool) × PurePolicy who k

/-- Read a pure policy as a behavioral one. -/
def PurePolicy.toBehavioral {who : Player} : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → PurePolicy who p → BehavioralPolicy who p
  | _, _, .ret _, _ => PUnit.unit
  | _, _, .sample _ _ _ k, policy => toBehavioral k policy
  | _, _, .commit _ _ _ _ k, policy =>
      (fun own view active => PMF.pure (policy.1 own view active), toBehavioral k policy.2)
  | _, _, .reveal _ _ _ _ _ _ k, policy =>
      (fun own view active => PMF.pure (policy.1 own view active), toBehavioral k policy.2)

/-- Failure actions make the policy space inhabited without any payload or
guard satisfiability assumption. -/
def failurePolicy (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → BehavioralPolicy who p
  | _, _, .ret _ => PUnit.unit
  | _, _, .sample _ _ _ k => failurePolicy who k
  | _, _, .commit _ _ _ _ k =>
      (fun _ _ _ => PMF.pure none, failurePolicy who k)
  | _, _, .reveal _ _ _ _ _ _ k =>
      (fun _ _ _ => PMF.pure false, failurePolicy who k)

def failureProfile (p : SourceProgram Player L Γ O) : BehavioralProfile p :=
  fun who => failurePolicy who p

def afterSample {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {law : L.DistExpr (SourcePublicCtx L Γ) payload}
    {k : SourceProgram Player L ((name, .publicData payload) :: Γ) O}
    (p : BehavioralProfile (SourceProgram.sample name (payload := payload) fresh law k)) :
    BehavioralProfile k := fun who => p who
def afterCommit {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {k : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}
    (p : BehavioralProfile (SourceProgram.commit name owner (payload := payload) fresh guard k)) :
    BehavioralProfile k := fun who => (p who).2
def afterReveal {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {k : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (p : BehavioralProfile
      (SourceProgram.reveal published owner name (payload := payload) fresh source unresolved k)) :
    BehavioralProfile k := fun who => (p who).2

def commitKernel {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst} {g : SourceGuard L Γ owner name payload}
    {k : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}
    (p : BehavioralProfile (SourceProgram.commit name owner fresh g k)) :
    (view : DecisionView owner Γ) → owner ∉ view.defaulted →
      PMF (Option (PublicationResult (L.Val payload))) :=
  (p owner).1 rfl

def revealKernel {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {k : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (p : BehavioralProfile (SourceProgram.reveal published owner name fresh source unresolved k)) :
    (view : DecisionView owner Γ) → owner ∉ view.defaulted → PMF Bool :=
  (p owner).1 rfl

@[reducible] def terminalCtx : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → SourceCtx Player L
  | terminal, _, .ret _ => terminal
  | _, _, .sample _ _ _ k => terminalCtx k
  | _, _, .commit _ _ _ _ k => terminalCtx k
  | _, _, .reveal _ _ _ _ _ _ k => terminalCtx k

def terminalPayoffs : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) →
    List (Player × L.Expr (SourcePublicCtx L (terminalCtx p)) L.int)
  | _, _, .ret u => by simpa [terminalCtx] using u
  | _, _, .sample _ _ _ k => terminalPayoffs k
  | _, _, .commit _ _ _ _ k => terminalPayoffs k
  | _, _, .reveal _ _ _ _ _ _ k => terminalPayoffs k

/-- A guard retained at the commitment of its subject. -/
structure Obligation (Γ : SourceCtx Player L) where
  owner : Player
  subject : VarId
  payload : L.Ty
  source : HasVar Γ subject (.commitment owner payload)
  guard : SourceGuard L Γ owner subject payload

namespace Obligation

omit [DecidableEq Player] [IExpr.ResultTypes L]

/-- Whether the subject and every input read by the guard's code are published. -/
def revealed (obligation : Obligation (Player := Player) (L := L) Γ)
    (revelations : Revelations Γ) : Bool :=
  (revelations obligation.source).isRevealed && obligation.guard.readsRevealed revelations

/-- Decide the obligation on the published results of its subject and inputs. -/
def accepts (obligation : Obligation (Player := Player) (L := L) Γ)
    (revelations : Revelations Γ) (state : State L Γ) : Bool :=
  obligation.guard.accepts ((revelations obligation.source).result state) revelations state

def weaken {x c} (obligation : Obligation (Player := Player) (L := L) Γ) :
    Obligation ((x, c) :: Γ) where
  owner := obligation.owner; subject := obligation.subject; payload := obligation.payload
  source := .there obligation.source; guard := obligation.guard.weaken

@[simp] theorem revealed_weaken {x c} (obligation : Obligation (Player := Player) (L := L) Γ)
    (revelations : Revelations Γ) :
    (obligation.weaken (x := x) (c := c)).revealed revelations.weaken =
      obligation.revealed revelations := by
  simp [revealed, weaken]

/-- Whether a reveal of `source` completes the obligation: some input was
unpublished before the reveal, and all of them are published after it. -/
def completedBy {published : VarId} (obligation : Obligation (Player := Player) (L := L) Γ)
    (revelations : Revelations Γ) (source : HasVar Γ name (.commitment owner payload)) :
    Bool :=
  !obligation.revealed revelations &&
    (obligation.weaken (x := published)).revealed
      (revelations.reveal (published := published) source)

/-- An obligation accepts when every successful result among its subject and
code-read inputs agrees with an assignment on which its code holds. -/
theorem accepts_of_compatible (obligation : Obligation (Player := Player) (L := L) Γ)
    (revelations : Revelations Γ) (state : State L Γ)
    (subjectValue : L.Val obligation.payload)
    (get : (x : VarId) → (σ : L.Ty) →
      HasVar ((obligation.subject, obligation.payload) :: obligation.guard.schema) x σ →
        x ∈ L.exprDeps obligation.guard.code → L.Val σ)
    (subjectEq : ∀ hx, get obligation.subject obligation.payload .here hx = subjectValue)
    (subjectAgrees : ∀ value,
      (revelations obligation.source).result state = .success value → value = subjectValue)
    (readsAgree : ∀ {x τ} (h : HasVar obligation.guard.schema x τ)
      (hx : x ∈ L.exprDeps obligation.guard.code) (value : L.Val τ),
        (obligation.guard.reads h).result revelations state = .success value →
          value = get x τ (.there h) hx)
    (valid : L.toBool (L.evalDeps obligation.guard.code get) = true) :
    obligation.accepts revelations state = true :=
  obligation.guard.accepts_of_compatible _ _ subjectValue get subjectEq subjectAgrees
    readsAgree valid

end Obligation

abbrev Registry (Γ : SourceCtx Player L) := List (Obligation (Player := Player) (L := L) Γ)

namespace Registry

omit [DecidableEq Player] [IExpr.ResultTypes L]

def weaken {x c} (registry : Registry (Player := Player) (L := L) Γ) : Registry ((x, c) :: Γ) :=
  registry.map Obligation.weaken

/-- The obligations a reveal completes, in the context after the reveal. -/
def completedBy {published : VarId} (registry : Registry (Player := Player) (L := L) Γ)
    (revelations : Revelations Γ) (source : HasVar Γ name (.commitment owner payload)) :
    Registry ((published, .publication payload) :: Γ) :=
  (registry.filter (·.completedBy (published := published) revelations source)).map
    Obligation.weaken

/-- Every obligation a reveal completes has all of its inputs published. -/
theorem revealed_of_mem_completedBy {published : VarId}
    (registry : Registry (Player := Player) (L := L) Γ) (revelations : Revelations Γ)
    (source : HasVar Γ name (.commitment owner payload))
    {obligation : Obligation ((published, .publication payload) :: Γ)}
    (member : obligation ∈ registry.completedBy revelations source) :
    obligation.revealed (revelations.reveal (published := published) source) = true := by
  obtain ⟨original, filtered, rfl⟩ := List.mem_map.mp member
  have completed := (List.mem_filter.mp filtered).2
  simp only [Obligation.completedBy, Bool.and_eq_true] at completed
  exact completed.2

end Registry

/-- The authoritative execution configuration, including public absorbing default. -/
structure Config (Player : Type) (L : IExpr) (Γ : SourceCtx Player L) where
  state : State L Γ
  registry : Registry Γ
  revelations : Revelations Γ
  history : History Player L
  defaults : DefaultHistory Player

/-- The authoritative public default set is derived from the event record. -/
def Config.defaulted (config : Config Player L Γ) : Finset Player :=
  config.defaults.defaulted

/-- Initial hidden binding failure is not public default. -/
def Config.initial (state : State L Γ) : Config Player L Γ :=
  ⟨state, [], Revelations.initial Γ, fun _ => [], ⟨[]⟩⟩

/-- Every player sees the same public default status and its own action recall. -/
def Config.view (who : Player) (config : Config Player L Γ) : DecisionView who Γ :=
  ⟨sourceObserve who config.state, config.defaults, config.history who⟩

omit resultTypes in
@[simp] theorem Config.view_defaulted (who : Player) (config : Config Player L Γ) :
    (config.view who).defaulted = config.defaulted := rfl

/-- A public sample leaves defaults and strategic recall unchanged. -/
def sampleSuccessor (name : VarId) (config : Config Player L Γ) (value : L.Val payload) :
    Config Player L ((name, .publicData payload) :: Γ) :=
  ⟨Env.cons value config.state, Registry.weaken config.registry,
    Revelations.weaken config.revelations, config.history, config.defaults.record none⟩

/-- A missing binding publicly defaults its owner; an accepted unopenable
binding stays hidden. Already defaulted owners make no new strategic choice. -/
def commitSuccessor {owner : Player} (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : Config Player L Γ)
    (choice : Option (PublicationResult (L.Val payload))) :
    Config Player L ((name, .commitment owner payload) :: Γ) :=
  let effective := if owner ∈ config.defaulted then none else choice
  ⟨Env.cons (effective.getD .failure) config.state,
    { owner := owner, subject := name, payload := payload, source := .here,
      guard := guard.weaken } :: Registry.weaken config.registry,
    Revelations.weaken config.revelations,
    if owner ∈ config.defaulted then config.history else
      Function.update config.history owner
        (config.history owner ++ [OwnAction.commit owner name payload effective]),
    config.defaults.record
      (if owner ∈ config.defaulted then none else if effective.isNone then some owner else none)⟩

/-- A publication runs all newly completed checks on the actual proposal.
Failure defaults its owner; automatic failure retains guard bookkeeping. -/
def revealSuccessor {owner : Player} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (disclose : Bool) :
    Config Player L ((published, .publication payload) :: Γ) :=
  let effective := if owner ∈ config.defaulted then false else disclose
  let proposal : PublicationResult (L.Val payload) :=
    if effective then config.state.get source else .failure
  let revealed : Revelations ((published, .publication payload) :: Γ) :=
    Revelations.reveal (published := published) config.revelations source
  let accepted :=
    if (Registry.completedBy (published := published) config.registry config.revelations
        source).all (·.accepts revealed (Env.cons proposal config.state))
      then proposal else .failure
  ⟨Env.cons accepted config.state, Registry.weaken config.registry, revealed,
    if owner ∈ config.defaulted then config.history else
      Function.update config.history owner
        (config.history owner ++ [OwnAction.reveal owner name effective]),
    config.defaults.record
      (if owner ∈ config.defaulted then none else if accepted.isFailure then some owner else none)⟩

/-- Execute exactly one authoritative source semantics, retaining its complete
terminal configuration. No callback exists at a defaulted owner's instruction. -/
def runFrom : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → BehavioralProfile program → Config Player L Γ →
      PMF (Config Player L program.terminalCtx)
  | _, _, .ret _, _, config => PMF.pure config
  | _, _, .sample name _ law next, profile, config =>
      (L.evalDist law (sourcePublicEnv config.state)).bind fun value =>
        runFrom next (afterSample profile) (sampleSuccessor name config value)
  | _, _, .commit name owner _ guard next, profile, config =>
      (if inactive : owner ∈ config.defaulted then PMF.pure none
        else commitKernel profile (config.view owner) inactive).bind fun choice =>
          runFrom next (afterCommit profile) (commitSuccessor name guard config choice)
  | _, _, .reveal published owner _ _ source _ next, profile, config =>
      (if inactive : owner ∈ config.defaulted then PMF.pure false
        else revealKernel profile (config.view owner) inactive).bind fun disclose =>
          runFrom next (afterReveal profile) (revealSuccessor published source config disclose)

/-- Start with no public defaults, regardless of hidden input binding results. -/
def run (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (state : State L Γ) : PMF (Config Player L program.terminalCtx) :=
  runFrom program profile (Config.initial state)

section Successors

omit [IExpr.ResultTypes L]

variable {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}

@[simp] theorem Config.initial_defaulted (state : State L Γ) :
    (Config.initial state).defaulted = (∅ : Finset Player) := rfl

/-- Equality of any player's views entails equality of public default status. -/
theorem Config.defaulted_eq_of_view_eq (who : Player) (left right : Config Player L Γ)
    (same : left.view who = right.view who) : left.defaulted = right.defaulted :=
  congrArg DecisionView.defaulted same

@[simp] theorem sampleSuccessor_defaulted (sampleName : VarId) (config : Config Player L Γ)
    (value : L.Val payload) :
    (sampleSuccessor sampleName config value).defaulted = config.defaulted := rfl

/-- No binding decision restores an already defaulted player. -/
theorem commitSuccessor_defaulted_mono {owner : Player} (bindingName : VarId)
    (guard : SourceGuard L Γ owner bindingName payload) (config : Config Player L Γ)
    (choice : Option (PublicationResult (L.Val payload))) :
    config.defaulted ⊆ (commitSuccessor bindingName guard config choice).defaulted := by
  exact config.defaults.defaulted_mono _

/-- Accepting any hidden binding result leaves public default status unchanged. -/
theorem commitSuccessor_defaulted_of_accepted {owner : Player} (bindingName : VarId)
    (guard : SourceGuard L Γ owner bindingName payload) (config : Config Player L Γ)
    (value : PublicationResult (L.Val payload)) :
    (commitSuccessor bindingName guard config (some value)).defaulted = config.defaulted := by
  by_cases inactive : owner ∈ config.defaulted <;> simp_all [commitSuccessor, Config.defaulted]

/-- An accepted unopenable binding does not reveal itself through exclusion. -/
theorem commitSuccessor_unopenable_opaque {owner : Player} (bindingName : VarId)
    (guard : SourceGuard L Γ owner bindingName payload) (config : Config Player L Γ) :
    (commitSuccessor bindingName guard config (some .failure)).defaulted = config.defaulted :=
  commitSuccessor_defaulted_of_accepted bindingName guard config .failure

/-- Omitting an owned binding publicly defaults that owner. -/
theorem commitSuccessor_defaulted_of_omission {owner : Player} (bindingName : VarId)
    (guard : SourceGuard L Γ owner bindingName payload) (config : Config Player L Γ) :
    (commitSuccessor bindingName guard config none).defaulted = insert owner config.defaulted := by
  by_cases inactive : owner ∈ config.defaulted <;> simp_all [commitSuccessor, Config.defaulted]

/-- The next binding of a defaulted owner fails under every requested action. -/
theorem commitSuccessor_binding_of_defaulted {owner : Player} (bindingName : VarId)
    (guard : SourceGuard L Γ owner bindingName payload) (config : Config Player L Γ)
    (inactive : owner ∈ config.defaulted) (choice : Option (PublicationResult (L.Val payload))) :
    (commitSuccessor bindingName guard config choice).state.get .here = .failure := by
  simp [commitSuccessor, inactive]

/-- Automatic completion records no action the owner did not choose. -/
theorem commitSuccessor_history_of_defaulted {owner : Player} (bindingName : VarId)
    (guard : SourceGuard L Γ owner bindingName payload) (config : Config Player L Γ)
    (inactive : owner ∈ config.defaulted) (choice : Option (PublicationResult (L.Val payload))) :
    (commitSuccessor bindingName guard config choice).history = config.history := by
  simp [commitSuccessor, inactive]

/-- Every publication preserves prior defaults, independently of the guard verdict. -/
theorem revealSuccessor_defaulted_mono {owner : Player} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ)
    (disclose : Bool) :
    config.defaulted ⊆ (revealSuccessor published source config disclose).defaulted := by
  exact config.defaults.defaulted_mono _

/-- Each publication records its first public default, or an empty completion entry. -/
theorem revealSuccessor_defaults {owner : Player} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ)
    (disclose : Bool) :
    (revealSuccessor published source config disclose).defaults = config.defaults.record
      (if owner ∈ config.defaulted then none else
        if ((revealSuccessor published source config disclose).state.get .here).isFailure then
          some owner else none) := rfl

/-- A failed accepted publication inserts its owner in public default status. -/
theorem revealSuccessor_defaulted_of_failure {owner : Player} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ)
    (disclose : Bool)
    (failed : (revealSuccessor published source config disclose).state.get .here = .failure) :
    (revealSuccessor published source config disclose).defaulted =
      insert owner config.defaulted := by
  unfold Config.defaulted
  rw [revealSuccessor_defaults, failed]
  by_cases inactive : owner ∈ config.defaulted <;>
    simp_all [Config.defaulted, PublicationResult.isFailure]

/-- Withholding fails a publication under arbitrary guards and prior state. -/
theorem revealSuccessor_result_of_withholding {owner : Player} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ) :
    (revealSuccessor published source config false).state.get .here = .failure := by
  simp [revealSuccessor]

/-- Withholding publicly defaults its owner. -/
theorem revealSuccessor_defaulted_of_withholding {owner : Player} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ) :
    (revealSuccessor published source config false).defaulted = insert owner config.defaulted :=
  revealSuccessor_defaulted_of_failure published source config false
    (revealSuccessor_result_of_withholding published source config)

/-- A defaulted owner's publication fails under every requested action. -/
theorem revealSuccessor_result_of_defaulted {owner : Player} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ)
    (inactive : owner ∈ config.defaulted) (disclose : Bool) :
    (revealSuccessor published source config disclose).state.get .here = .failure := by
  simp [revealSuccessor, inactive]

/-- Automatic publication records no strategic action. -/
theorem revealSuccessor_history_of_defaulted {owner : Player} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ)
    (inactive : owner ∈ config.defaulted) (disclose : Bool) :
    (revealSuccessor published source config disclose).history = config.history := by
  simp [revealSuccessor, inactive]

/-- A defaulted owner's publication still resolves the outstanding binding. -/
theorem revealSuccessor_revelations {owner : Player} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ)
    (disclose : Bool) :
    @Eq (Revelations ((published, .publication payload) :: Γ))
      (@Config.revelations Player L _ (revealSuccessor published source config disclose))
      (@Revelations.reveal Player L Γ owner payload name published
        (@Config.revelations Player L Γ config) source) := rfl

/-- A defaulted owner's publication retains the guard registry with correct weakening. -/
theorem revealSuccessor_registry {owner : Player} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ)
    (disclose : Bool) :
    (revealSuccessor published source config disclose).registry = config.registry.weaken := rfl

include resultTypes

theorem runFrom_sample {fresh : name ∉ Γ.map Prod.fst}
    {law : L.DistExpr (SourcePublicCtx L Γ) payload}
    {next : SourceProgram Player L ((name, .publicData payload) :: Γ) O}
    (profile : BehavioralProfile (SourceProgram.sample name fresh law next))
    (config : Config Player L Γ) :
    runFrom (SourceProgram.sample name fresh law next) profile config =
      (L.evalDist law (sourcePublicEnv config.state)).bind fun value =>
        runFrom next (afterSample profile) (sampleSuccessor name config value) := rfl

theorem runFrom_commit {owner : Player} {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}
    (profile : BehavioralProfile (SourceProgram.commit name owner fresh guard next))
    (config : Config Player L Γ) :
    runFrom (SourceProgram.commit name owner fresh guard next) profile config =
      (if inactive : owner ∈ config.defaulted then PMF.pure none
        else commitKernel profile (config.view owner) inactive).bind fun choice =>
          runFrom next (afterCommit profile) (commitSuccessor name guard config choice) := rfl

theorem runFrom_reveal {published : VarId} {owner : Player}
    {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (profile : BehavioralProfile
      (SourceProgram.reveal published owner name fresh source unresolved next))
    (config : Config Player L Γ) :
    runFrom (SourceProgram.reveal published owner name fresh source unresolved next)
        profile config =
      (if inactive : owner ∈ config.defaulted then PMF.pure false
        else revealKernel profile (config.view owner) inactive).bind fun disclose =>
          runFrom next (afterReveal profile)
            (revealSuccessor published source config disclose) := rfl

end Successors

/-- Every supported source continuation preserves all public defaults. -/
theorem runFrom_defaulted_mono : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (profile : BehavioralProfile program) →
    (config : Config Player L Γ) → ∀ final ∈ (runFrom program profile config).support,
      config.defaulted ⊆ final.defaulted
  | _, _, .ret _, _, config, final, reached => by
      have same := (PMF.mem_support_pure_iff _ _).mp reached
      subst final
      exact Finset.Subset.refl config.defaulted
  | _, _, .sample name _ law next, profile, config, final, reached => by
      simp only [runFrom, PMF.support_bind, Set.mem_iUnion] at reached
      obtain ⟨value, _, reached⟩ := reached
      exact runFrom_defaulted_mono next (afterSample profile)
        (sampleSuccessor name config value) final reached
  | _, _, .commit name _ _ guard next, profile, config, final, reached => by
      simp only [runFrom, PMF.support_bind, Set.mem_iUnion] at reached
      obtain ⟨choice, _, reached⟩ := reached
      exact (commitSuccessor_defaulted_mono name guard config choice).trans
        (runFrom_defaulted_mono next (afterCommit profile)
          (commitSuccessor name guard config choice) final reached)
  | _, _, .reveal published _ _ _ source _ next, profile, config, final, reached => by
      simp only [runFrom, PMF.support_bind, Set.mem_iUnion] at reached
      obtain ⟨disclose, _, reached⟩ := reached
      exact (revealSuccessor_defaulted_mono published source config disclose).trans
        (runFrom_defaulted_mono next (afterReveal profile)
          (revealSuccessor published source config disclose) final reached)

section Steps

variable {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}

theorem afterSample_update {fresh : name ∉ Γ.map Prod.fst}
    {law : L.DistExpr (SourcePublicCtx L Γ) payload}
    {k : SourceProgram Player L ((name, .publicData payload) :: Γ) O}
    (profile : BehavioralProfile (SourceProgram.sample name fresh law k)) (who : Player)
    (policy : BehavioralPolicy who (SourceProgram.sample name fresh law k)) :
    afterSample (Function.update profile who policy) =
      Function.update (afterSample profile) who policy := rfl

theorem afterCommit_update {owner : Player} {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {k : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}
    (profile : BehavioralProfile (SourceProgram.commit name owner fresh guard k))
    (who : Player)
    (policy : BehavioralPolicy who (SourceProgram.commit name owner fresh guard k)) :
    afterCommit (Function.update profile who policy) =
      Function.update (afterCommit profile) who policy.2 := by
  funext actor
  by_cases h : actor = who
  · subst h; simp [afterCommit]
  · simp [afterCommit, Function.update_of_ne h]

theorem afterReveal_update {published : VarId} {owner : Player}
    {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {k : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (profile : BehavioralProfile
      (SourceProgram.reveal published owner name fresh source unresolved k))
    (who : Player)
    (policy : BehavioralPolicy who
      (SourceProgram.reveal published owner name fresh source unresolved k)) :
    afterReveal (Function.update profile who policy) =
      Function.update (afterReveal profile) who policy.2 := by
  funext actor
  by_cases h : actor = who
  · subst h; simp [afterReveal]
  · simp [afterReveal, Function.update_of_ne h]

end Steps

/-- The public terminal result retains both expression-readable values and default status. -/
structure PublicOutcome (program : SourceProgram Player L Γ O) where
  values : Env L.Val (SourcePublicCtx L program.terminalCtx)
  defaults : DefaultHistory Player

/-- Current public defaults are read from the public terminal history. -/
def PublicOutcome.defaulted {program : SourceProgram Player L Γ O}
    (outcome : PublicOutcome program) : Finset Player := outcome.defaults.defaulted

/-- Public default status is never discarded by the terminal projection. -/
def publicOutcome (program : SourceProgram Player L Γ O)
    (config : Config Player L program.terminalCtx) : PublicOutcome program :=
  ⟨sourcePublicEnv config.state, config.defaults⟩

@[simp] theorem publicOutcome_defaulted (program : SourceProgram Player L Γ O)
    (config : Config Player L program.terminalCtx) :
    (publicOutcome program config).defaulted = config.defaulted := rfl

def gameSignature (p : SourceProgram Player L Γ O) : GameSignature Player where
  Strategy := fun who => BehavioralPolicy who p
  Outcome := PublicOutcome p

def gameForm (p : SourceProgram Player L Γ O) (s : State L Γ) :
    GameForm Player where
  sig := gameSignature p
  play profile := (run p profile s).map (publicOutcome p)

def evaluatePayoffs (p : SourceProgram Player L Γ O)
    (s : State L (terminalCtx p)) : List (Player × Int) :=
  (terminalPayoffs p).map fun e =>
    (e.1, L.toInt (L.eval e.2 (sourcePublicEnv s)))

end SourceProgram
end Vegas
