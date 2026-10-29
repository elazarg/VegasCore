/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Setup

/-! # Binding policies without opaque unusable candidates

The value interface permits public omission and successful value bindings.
It excludes an accepted unusable binding. Its behavioral policies and game
presentation use the sole source evaluator and public outcome.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A policy that never admits an opaque unusable candidate; public omission is allowed. -/
def ValueBinding {who : Player} : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → BehavioralPolicy who p → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample _ _ _ k, policy => ValueBinding k policy
  | _, _, .commit _ owner _ _ k, policy =>
      (∀ (own : owner = who) view active,
        some PublicationResult.failure ∉ (policy.1 own view active).support) ∧
        ValueBinding k policy.2
  | _, _, .reveal _ _ _ _ _ _ k, policy => ValueBinding k policy.2

/-- Bind the canonical value of every payload and disclose nothing. -/
def bindingPolicy (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → BehavioralPolicy who p
  | _, _, .ret _ => PUnit.unit
  | _, _, .sample _ _ _ k => bindingPolicy who k
  | _, _, .commit (payload := payload) _ _ _ _ k =>
      (fun _ _ _ => PMF.pure (some (.success (L.someValue payload))), bindingPolicy who k)
  | _, _, .reveal _ _ _ _ _ _ k =>
      (fun _ _ _ => PMF.pure false, bindingPolicy who k)

theorem valueBinding_bindingPolicy (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    ValueBinding p (bindingPolicy who p)
  | _, _, .ret _ => trivial
  | _, _, .sample _ _ _ k => valueBinding_bindingPolicy who k
  | _, _, .commit _ _ _ _ k =>
      ⟨fun _ _ _ => by simp [bindingPolicy], valueBinding_bindingPolicy who k⟩
  | _, _, .reveal _ _ _ _ _ _ k => valueBinding_bindingPolicy who k

/-! ## The value-binding game

The game a source program presents when accepted bindings must carry a value. Only the
strategies change: the program, the setup law and the public outcome are the
same, so the two games are compared by the identity on outcomes. -/

/-- A policy that never binds an unopenable candidate, as a strategy. Reducible
so that the game's strategy type and this one are the same term to a rewrite. -/
@[reducible] def ValueBindingPolicy (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
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

/-- The value-binding game of a setup. Reducible so that `sig.Strategy` reduces
to `ValueBindingPolicy`, which is what rewriting through the game's laws needs.
-/
@[reducible] def valueBindingGame (setup : Setup (Player := Player) (L := L)) :
    GameForm Player where
  sig :=
    { Strategy := fun who => ValueBindingPolicy who setup.program
      Outcome := SourceProgram.PublicOutcome setup.program }
  play profile := setup.publicRun (valueBindingProfile profile)

@[simp] theorem valueBindingGame_play (setup : Setup (Player := Player) (L := L))
    (profile : Profile setup.valueBindingGame.sig) :
    setup.valueBindingGame.play profile = setup.publicRun (valueBindingProfile profile) := rfl

end Setup

end Vegas.SourceProgram
