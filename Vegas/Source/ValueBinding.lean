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

variable {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId} {owner : Player}
variable {payload : L.Ty}

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
