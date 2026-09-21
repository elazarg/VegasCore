/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Basic
import GameTheory.Core.Form

/-! # Source policies and exact execution

Observation-local policies choose immutable bindings and disclosure decisions.
Execution follows source order and interprets chance through the exact finite
law carried by source syntax. Each retained guard obligation is checked once, at
the reveal that publishes the last of its inputs; a rejected check makes that
publication fail. Execution produces the detailed terminal state, which is what
the laws below are stated over; the game form's *outcome* is its public
projection, so no utility can depend on what a player kept to itself.
`evaluatePayoffs` is a separate, explicit settlement projection and does not
itself impose utilities.
-/

noncomputable section
namespace Vegas
open GameTheory GameTheory.Math.Probability

def sourcePublicEnv {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L] :
    {Γ : SourceCtx Player L} → State L Γ → Env L.Val (SourcePublicCtx L Γ)
  | [], _ => Env.empty L.Val
  | (_, .publicData _) :: _, s => Env.cons (s.get .here)
      (sourcePublicEnv fun _ _ h => s.get (HasVar.there h))
  | (_, .privateData _ _) :: tail, s => sourcePublicEnv (Player := Player) (L := L)
      (R := R) (Γ := tail) (fun _ _ h => s.get (HasVar.there h))
  | (_, .publication τ) :: _, s =>
      Env.cons ((R.valueEquiv τ).symm (s.get .here))
        (sourcePublicEnv fun _ _ h => s.get (HasVar.there h))

def SourceObservationVal {Player : Type} (L : IExpr) :
    CellTy Player L → Type
  | .publicData τ => L.Val τ
  | .publication τ => PublicationResult (L.Val τ)
  | .privateData owner τ => Option (CellVal L (.privateData owner τ))

structure SourceObservation {Player : Type} (L : IExpr) (who : Player)
    (Γ : SourceCtx Player L) where
  cells : Env (SourceObservationVal L) Γ

def sourceObserve {Player : Type} [DecidableEq Player] {L : IExpr} (who : Player) :
    {Γ : SourceCtx Player L} → State L Γ → SourceObservation L who Γ
  | _, s => ⟨fun _ cell h => match cell with
      | .publicData _ => s.get h
      | .publication _ => s.get h
      | .privateData owner _ => if owner = who then some (s.get h) else none⟩

section SourceObserve

variable {Player : Type} [DecidableEq Player] {L : IExpr} {Γ : SourceCtx Player L}

@[simp] theorem sourceObserve_publicData (who : Player) (state : State L Γ)
    {x : VarId} {τ : L.Ty} (h : HasVar Γ x (.publicData τ)) :
    (sourceObserve who state).cells x (.publicData τ) h = state.get h := rfl

@[simp] theorem sourceObserve_publication (who : Player) (state : State L Γ)
    {x : VarId} {τ : L.Ty} (h : HasVar Γ x (.publication τ)) :
    (sourceObserve who state).cells x (.publication τ) h = state.get h := rfl

@[simp] theorem sourceObserve_privateData (who : Player) (state : State L Γ)
    {x : VarId} {owner : Player} {τ : L.Ty} (h : HasVar Γ x (.privateData owner τ)) :
    (sourceObserve who state).cells x (.privateData owner τ) h =
      if owner = who then some (state.get h) else none := rfl

/-- A player's source observation depends only on public data, publication
results, and that player's own private cells. -/
theorem sourceObserve_congr (who : Player) (left right : State L Γ)
    (publicEq : ∀ {x τ} (h : HasVar Γ x (.publicData τ)), left.get h = right.get h)
    (publicationEq : ∀ {x τ} (h : HasVar Γ x (.publication τ)), left.get h = right.get h)
    (ownEq : ∀ {x τ} (h : HasVar Γ x (.privateData who τ)), left.get h = right.get h) :
    sourceObserve who left = sourceObserve who right := by
  have cellsEq : (sourceObserve who left).cells = (sourceObserve who right).cells := by
    funext x cell h
    cases cell with
    | publicData τ =>
        rw [sourceObserve_publicData, sourceObserve_publicData, publicEq h]
    | publication τ =>
        rw [sourceObserve_publication, sourceObserve_publication, publicationEq h]
    | privateData owner τ =>
        rw [sourceObserve_privateData, sourceObserve_privateData]
        by_cases same : owner = who
        · subst same
          simp [ownEq h]
        · simp [same]
  calc sourceObserve who left = ⟨(sourceObserve who left).cells⟩ := rfl
    _ = ⟨(sourceObserve who right).cells⟩ := by rw [cellsEq]
    _ = sourceObserve who right := rfl

end SourceObserve


namespace SourceProgram
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable {Γ : SourceCtx Player L} {O : Finset VarId} {name x : VarId} {owner : Player}
variable {payload : L.Ty} {c : CellTy Player L}

inductive OwnAction (Player : Type) (L : IExpr) where
  | commit (owner : Player) (name : VarId) (payload : L.Ty)
      (choice : PublicationResult (L.Val payload))
  | reveal (owner : Player) (name : VarId) (disclose : Bool)

abbrev History (Player : Type) (L : IExpr) := Player → List (OwnAction Player L)
abbrev DecisionView (who : Player) (Γ : SourceCtx Player L) :=
  SourceObservation L who Γ × List (OwnAction Player L)

/-- A policy prescribing a law over actions at every decision point this player
owns. Reducible on purpose: its projections have to line up at reducible
transparency, or rewriting under a `.1`/`.2` silently declines to fire. -/
abbrev BehavioralPolicy (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Type
  | _, _, .ret _ => PUnit
  | _, _, .sample _ _ _ k => BehavioralPolicy who k
  | Γ, _, .commit (payload := payload) _ owner _ _ k =>
      ((owner = who) → DecisionView who Γ →
        FinDist (PublicationResult (L.Val payload))) × BehavioralPolicy who k
  | Γ, _, .reveal _ owner _ _ _ _ k =>
      ((owner = who) → DecisionView who Γ → FinDist Bool) ×
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

/-- Failure actions make the policy space inhabited without any payload or
guard satisfiability assumption. -/
def failurePolicy (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → BehavioralPolicy who p
  | _, _, .ret _ => PUnit.unit
  | _, _, .sample _ _ _ k => failurePolicy who k
  | _, _, .commit _ _ _ _ k =>
      (fun _ _ => FinDist.pure .failure, failurePolicy who k)
  | _, _, .reveal _ _ _ _ _ _ k =>
      (fun _ _ => FinDist.pure false, failurePolicy who k)

def failureProfile (p : SourceProgram Player L Γ O) : BehavioralProfile p :=
  fun who => failurePolicy who p

theorem behavioralProfile_nonempty (p : SourceProgram Player L Γ O) :
    Nonempty (BehavioralProfile p) := ⟨failureProfile p⟩

def afterSample {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {law : L.DistExpr (SourcePublicCtx L Γ) payload}
    {k : SourceProgram Player L ((name, .publicData payload) :: Γ) O}
    (p : BehavioralProfile (SourceProgram.sample name (payload := payload) fresh law k)) :
    BehavioralProfile k := fun who => p who
def afterCommit {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {k : SourceProgram Player L ((name, .privateData owner payload) :: Γ) (insert name O)}
    (p : BehavioralProfile (SourceProgram.commit name owner (payload := payload) fresh guard k)) :
    BehavioralProfile k := fun who => (p who).2
def afterReveal {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.privateData owner payload)} {unresolved : name ∈ O}
    {k : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (p : BehavioralProfile
      (SourceProgram.reveal published owner name (payload := payload) fresh source unresolved k)) :
    BehavioralProfile k := fun who => (p who).2

def commitKernel {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst} {g : SourceGuard L Γ owner name payload}
    {k : SourceProgram Player L ((name, .privateData owner payload) :: Γ) (insert name O)}
    (p : BehavioralProfile (SourceProgram.commit name owner fresh g k)) :
    DecisionView owner Γ → FinDist (PublicationResult (L.Val payload)) :=
  (p owner).1 rfl

def revealKernel {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.privateData owner payload)} {unresolved : name ∈ O}
    {k : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (p : BehavioralProfile (SourceProgram.reveal published owner name fresh source unresolved k)) :
    DecisionView owner Γ → FinDist Bool :=
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
  source : HasVar Γ subject (.privateData owner payload)
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

@[simp] theorem accepts_weaken {x c} (obligation : Obligation (Player := Player) (L := L) Γ)
    (revelations : Revelations Γ) (head : CellVal L c) (state : State L Γ) :
    (obligation.weaken (x := x)).accepts revelations.weaken (Env.cons head state) =
      obligation.accepts revelations state := by
  simp [accepts, weaken]

/-- Whether a reveal of `source` completes the obligation: some input was
unpublished before the reveal, and all of them are published after it. -/
def completedBy {published : VarId} (obligation : Obligation (Player := Player) (L := L) Γ)
    (revelations : Revelations Γ) (source : HasVar Γ name (.privateData owner payload)) :
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
    (revelations : Revelations Γ) (source : HasVar Γ name (.privateData owner payload)) :
    Registry ((published, .publication payload) :: Γ) :=
  (registry.filter (·.completedBy (published := published) revelations source)).map
    Obligation.weaken

/-- Every obligation a reveal completes has all of its inputs published. -/
theorem revealed_of_mem_completedBy {published : VarId}
    (registry : Registry (Player := Player) (L := L) Γ) (revelations : Revelations Γ)
    (source : HasVar Γ name (.privateData owner payload))
    {obligation : Obligation ((published, .publication payload) :: Γ)}
    (member : obligation ∈ registry.completedBy revelations source) :
    obligation.revealed (revelations.reveal (published := published) source) = true := by
  obtain ⟨original, filtered, rfl⟩ := List.mem_map.mp member
  have completed := (List.mem_filter.mp filtered).2
  simp only [Obligation.completedBy, Bool.and_eq_true] at completed
  exact completed.2

end Registry

def runWith : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → BehavioralProfile p → State L Γ →
    Registry Γ → Revelations Γ → History Player L → FinDist (State L (terminalCtx p))
  | _, _, .ret _, _, s, _, _, _ => FinDist.pure s
  | _, _, .sample _ _ d k, profile, s, r, revelations, history =>
      (L.evalDist d (sourcePublicEnv s)).bind fun a =>
        runWith k (afterSample profile) (Env.cons a s) r.weaken revelations.weaken history
  | _, _, .commit name owner _ g k, profile, s, r, revelations, history =>
      (commitKernel profile (sourceObserve owner s, history owner)).bind fun b =>
        let obligation : Obligation _ :=
          { owner := owner, subject := name, payload := _, source := .here, guard := g.weaken }
        let history' := Function.update history owner
          (history owner ++ [OwnAction.commit owner name _ b])
        runWith k (afterCommit profile) (Env.cons b s) (obligation :: r.weaken)
          revelations.weaken history'
  | _, _, .reveal published owner name _ h _ k, profile, s, r, revelations, history =>
      (revealKernel profile (sourceObserve owner s, history owner)).bind fun disclose =>
        let proposal := if disclose then s.get h else .failure
        let revealed : Revelations _ := revelations.reveal (published := published) h
        let accepted :=
          if (r.completedBy (published := published) revelations h).all
            (·.accepts revealed (Env.cons proposal s))
          then proposal else .failure
        let history' := Function.update history owner
          (history owner ++ [OwnAction.reveal owner name disclose])
        runWith k (afterReveal profile) (Env.cons accepted s) r.weaken revealed history'

def run (p : SourceProgram Player L Γ O) (profile : BehavioralProfile p) (s : State L Γ) :=
  runWith p profile s [] (Revelations.initial Γ) (fun _ => [])

/-! ## Execution as a configuration transformer

The same steps `runWith` takes, named: what a program point threads, what each
constructor does to it, and that replacing one player's policy commutes with
taking a step. Reasoning about a run proceeds by these rather than by unfolding
`runWith` at each use. -/

/-- Everything `runWith` threads through a program point. -/
structure Config (Player : Type) (L : IExpr) (Γ : SourceCtx Player L) where
  /-- The cells bound so far. -/
  state : State L Γ
  /-- The obligations retained so far. -/
  registry : Registry Γ
  /-- What has been published so far. -/
  revelations : Revelations Γ
  /-- What each player did so far. -/
  history : History Player L

/-- Run a program from a configuration. -/
def runFrom {Γ : SourceCtx Player L} {O : Finset VarId} (p : SourceProgram Player L Γ O)
    (profile : BehavioralProfile p) (config : Config Player L Γ) :
    FinDist (State L (terminalCtx p)) :=
  runWith p profile config.state config.registry config.revelations config.history

/-- What a player sees at a configuration. -/
def Config.view {Γ : SourceCtx Player L} (who : Player)
    (config : Config Player L Γ) : DecisionView who Γ :=
  (sourceObserve who config.state, config.history who)

section Successors

variable {Γ : SourceCtx Player L} {name : VarId} {payload : L.Ty}

/-- The configuration a public sample reaches. -/
def sampleSuccessor (name : VarId) (config : Config Player L Γ) (value : L.Val payload) :
    Config Player L ((name, .publicData payload) :: Γ) :=
  ⟨Env.cons value config.state, Registry.weaken config.registry,
    Revelations.weaken config.revelations, config.history⟩

/-- The configuration a binding reaches. -/
def commitSuccessor {owner : Player} (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : Config Player L Γ)
    (choice : PublicationResult (L.Val payload)) :
    Config Player L ((name, .privateData owner payload) :: Γ) :=
  ⟨Env.cons choice config.state,
    { owner := owner, subject := name, payload := payload, source := .here,
      guard := guard.weaken } :: Registry.weaken config.registry,
    Revelations.weaken config.revelations,
    Function.update config.history owner
      (config.history owner ++ [OwnAction.commit owner name payload choice])⟩

/-- The configuration a publication reaches, guards included. -/
def revealSuccessor {owner : Player} (published : VarId)
    (source : HasVar Γ name (.privateData owner payload))
    (config : Config Player L Γ) (disclose : Bool) :
    Config Player L ((published, .publication payload) :: Γ) :=
  let proposal : PublicationResult (L.Val payload) :=
    if disclose then config.state.get source else .failure
  let revealed : Revelations ((published, .publication payload) :: Γ) :=
    Revelations.reveal (published := published) config.revelations source
  ⟨Env.cons
      (if (Registry.completedBy (published := published) config.registry config.revelations
          source).all (·.accepts revealed (Env.cons proposal config.state))
        then proposal else .failure)
      config.state,
    Registry.weaken config.registry, revealed,
    Function.update config.history owner
      (config.history owner ++ [OwnAction.reveal owner name disclose])⟩

variable {O : Finset VarId}

theorem runFrom_sample {fresh : name ∉ Γ.map Prod.fst}
    {law : L.DistExpr (SourcePublicCtx L Γ) payload}
    {k : SourceProgram Player L ((name, .publicData payload) :: Γ) O}
    (profile : BehavioralProfile (SourceProgram.sample name fresh law k))
    (config : Config Player L Γ) :
    runFrom (SourceProgram.sample name fresh law k) profile config =
      (L.evalDist law (sourcePublicEnv config.state)).bind fun value =>
        runFrom k (afterSample profile) (sampleSuccessor name config value) := rfl

theorem runFrom_commit {owner : Player} {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {k : SourceProgram Player L ((name, .privateData owner payload) :: Γ) (insert name O)}
    (profile : BehavioralProfile (SourceProgram.commit name owner fresh guard k))
    (config : Config Player L Γ) :
    runFrom (SourceProgram.commit name owner fresh guard k) profile config =
      (commitKernel profile (Config.view owner config)).bind fun choice =>
        runFrom k (afterCommit profile) (commitSuccessor name guard config choice) := rfl

theorem runFrom_reveal {published : VarId} {owner : Player}
    {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.privateData owner payload)} {unresolved : name ∈ O}
    {k : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (profile : BehavioralProfile
      (SourceProgram.reveal published owner name fresh source unresolved k))
    (config : Config Player L Γ) :
    runFrom (SourceProgram.reveal published owner name fresh source unresolved k)
        profile config =
      (revealKernel profile (Config.view owner config)).bind fun disclose =>
        runFrom k (afterReveal profile) (revealSuccessor published source config disclose) := rfl

end Successors

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
    {k : SourceProgram Player L ((name, .privateData owner payload) :: Γ) (insert name O)}
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
    {source : HasVar Γ name (.privateData owner payload)} {unresolved : name ∈ O}
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

/-- Guards cannot override an honest disclosure: when the bound value keeps every
obligation the reveal completes compatible, the owner's choice alone decides the
reveal, publishing the value on disclosure and failure on withholding. This is
one disclosure; `GuardsAccept` asks for the acceptance it derives, at every
reveal, and `run_successful` is the whole-run consequence. -/
theorem runWith_reveal_compatible {published name : VarId} {owner : Player}
    {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.privateData owner payload)} {unresolved : name ∈ O}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (profile : BehavioralProfile (.reveal published owner name fresh source unresolved next))
    (state : State L Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (history : History Player L)
    (value : L.Val payload) (bound : state.get source = .success value)
    (compatible : ∀ obligation ∈ registry.completedBy (published := published) revelations source,
      ∃ (subjectValue : L.Val obligation.payload)
        (get : (x : VarId) → (σ : L.Ty) →
          HasVar ((obligation.subject, obligation.payload) :: obligation.guard.schema) x σ →
            x ∈ L.exprDeps obligation.guard.code → L.Val σ),
        (∀ hx, get obligation.subject obligation.payload .here hx = subjectValue) ∧
        (∀ value', (revelations.reveal (published := published) source obligation.source).result
          (Env.cons (Val := CellVal (Player := Player) L) (x := published)
            (τ := .publication payload) (PublicationResult.success value) state) =
              .success value' → value' = subjectValue) ∧
        (∀ {x τ} (h : HasVar obligation.guard.schema x τ)
          (hx : x ∈ L.exprDeps obligation.guard.code) (value' : L.Val τ),
            (obligation.guard.reads h).result (revelations.reveal (published := published) source)
              (Env.cons (Val := CellVal (Player := Player) L) (x := published)
            (τ := .publication payload) (PublicationResult.success value) state) = .success value' →
                value' = get x τ (.there h) hx) ∧
        L.toBool (L.evalDeps obligation.guard.code get) = true) :
    runWith (.reveal published owner name fresh source unresolved next) profile state registry
        revelations history =
      (revealKernel profile (sourceObserve owner state, history owner)).bind fun disclose =>
        runWith next (afterReveal profile)
          (Env.cons (if disclose then PublicationResult.success value else .failure) state)
          registry.weaken (revelations.reveal (published := published) source)
          (Function.update history owner
            (history owner ++ [OwnAction.reveal owner name disclose])) := by
  have accepted : (registry.completedBy (published := published) revelations source).all
      (·.accepts (revelations.reveal (published := published) source)
        (Env.cons (Val := CellVal (Player := Player) L) (x := published)
            (τ := .publication payload) (PublicationResult.success value) state)) = true := by
    refine List.all_eq_true.mpr fun obligation member => ?_
    obtain ⟨subjectValue, get, subjectEq, subjectAgrees, readsAgree, valid⟩ :=
      compatible obligation member
    exact obligation.accepts_of_compatible _ _ subjectValue get subjectEq subjectAgrees
      readsAgree valid
  simp only [runWith]
  congr 1
  funext disclose
  cases disclose with
  | false => simp
  | true => simp [bound, accepted]

def Initial.run (initial : Initial (Player := Player) (L := L))
    (profile : BehavioralProfile initial.program) :=
  SourceProgram.run initial.program profile initial.state

/-- What a completed program produces: its publications and public samples,
and nothing a player kept to itself. This is exactly the context settlement
reads, so no payoff can depend on more than an outcome records. -/
abbrev PublicOutcome (p : SourceProgram Player L Γ O) :=
  Env L.Val (SourcePublicCtx L (terminalCtx p))

/-- The public result of a terminal state. -/
def publicOutcome (p : SourceProgram Player L Γ O) (s : State L (terminalCtx p)) :
    PublicOutcome p :=
  sourcePublicEnv s

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
