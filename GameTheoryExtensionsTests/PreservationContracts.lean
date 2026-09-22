/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.IrreversibleFailure

/-! # Experiments with preservation contracts

Ordinary propositions indexed by a fixed translation suffice to separate
semantics, requested properties, and evidence. This test module is an API
experiment, not a production certificate hierarchy or a Vegas SPE theorem.
The SPE instance below uses the canonical predicate through the checked
irreversible-failure example. Production strategic maps must additionally be
playerwise; predicate transport does not establish that fact.
-/

namespace GameTheoryExtensionsTests.PreservationContracts

universe u v w k

/-- A scope is an explicit collection of analysis contexts. Contexts can carry
utilities and observation choices; the translation is fixed before them. -/
def PreservesOn {S : Type u} {T : Type v} {K : Type k}
    (compile : S → T) (sourceClaim : K → S → Prop)
    (targetClaim : K → T → Prop) (scope : K → Prop) : Prop :=
  ∀ context, scope context → ∀ source, sourceClaim context source →
    targetClaim context (compile source)

theorem identity {S : Type u} {K : Type k}
    (claim : K → S → Prop) (scope : K → Prop) :
    PreservesOn id claim claim scope := fun _ _ _ proof => proof

/-- Composition shares the exact middle claim and intersects the scopes. -/
theorem compose {S : Type u} {T : Type v} {U : Type w} {K : Type k}
    {first : S → T} {second : T → U}
    {sourceClaim : K → S → Prop} {middleClaim : K → T → Prop}
    {targetClaim : K → U → Prop} {firstScope secondScope : K → Prop}
    (firstProof : PreservesOn first sourceClaim middleClaim firstScope)
    (secondProof : PreservesOn second middleClaim targetClaim secondScope) :
    PreservesOn (second ∘ first) sourceClaim targetClaim
      (fun context => firstScope context ∧ secondScope context) :=
  fun context admitted source proof =>
    secondProof context admitted.2 (first source)
      (firstProof context admitted.1 source proof)

/-- Multiple requested properties must refer to the same concrete map. -/
theorem conjunction {S : Type u} {T : Type v} {K : Type k}
    {compile : S → T} {sourceFirst sourceSecond : K → S → Prop}
    {targetFirst targetSecond : K → T → Prop} {scope : K → Prop}
    (first : PreservesOn compile sourceFirst targetFirst scope)
    (second : PreservesOn compile sourceSecond targetSecond scope) :
    PreservesOn compile
      (fun context source => sourceFirst context source ∧ sourceSecond context source)
      (fun context target => targetFirst context target ∧ targetSecond context target) scope :=
  fun context admitted source proof =>
    ⟨first context admitted source proof.1, second context admitted source proof.2⟩

theorem restrictScope {S : Type u} {T : Type v} {K : Type k}
    {compile : S → T} {sourceClaim : K → S → Prop} {targetClaim : K → T → Prop}
    {broad narrow : K → Prop} (included : ∀ context, narrow context → broad context)
    (proof : PreservesOn compile sourceClaim targetClaim broad) :
    PreservesOn compile sourceClaim targetClaim narrow :=
  fun context admitted => proof context (included context admitted)

/-- Failure to find evidence is distinct from evidence that a claim is false. -/
inductive Validation (claim : Prop) where
  | certified (proof : claim)
  | refuted (proof : ¬ claim)
  | unresolved (obligation : String)

def Validation.isCertified {claim : Prop} : Validation claim → Bool
  | .certified _ => true
  | .refuted _ | .unresolved _ => false

theorem accepted_sound {claim : Prop} (result : Validation claim)
    (accepted : result.isCertified = true) : claim := by
  cases result with
  | certified proof => exact proof
  | refuted _ => simp [Validation.isCertified] at accepted
  | unresolved _ => simp [Validation.isCertified] at accepted

/-- A registry of separate existential capability flags can certify two
incompatible translations. Their evidence cannot be combined. -/
theorem separate_maps_do_not_bundle :
    (∃ compile : Unit → Bool, ∀ source, compile source = false) ∧
    (∃ compile : Unit → Bool, ∀ source, compile source = true) ∧
    ¬ (∃ compile : Unit → Bool,
      (∀ source, compile source = false) ∧ (∀ source, compile source = true)) := by
  refine ⟨⟨fun _ => false, fun _ => rfl⟩, ⟨fun _ => true, fun _ => rfl⟩, ?_⟩
  rintro ⟨compile, first, second⟩
  have impossible := (first ()).symm.trans (second ())
  cases impossible

/-- A certificate for one context cannot be reused for a larger scope. -/
theorem scoped_does_not_imply_uniform :
    PreservesOn (fun _ : Unit => false) (fun (_ : Bool) _ => True)
      (fun context target => target = context) (fun context => context = false) ∧
    ¬ PreservesOn (fun _ : Unit => false) (fun (_ : Bool) _ => True)
      (fun context target => target = context) (fun _ => True) := by
  constructor
  · intro context admitted _ _
    exact admitted.symm
  · intro proof
    have impossible := proof true trivial () trivial
    cases impossible

open GameTheory
open IrreversibleFailure

def sourceSPE (prefer : Bool) (profile : Profile (model true).strategicSignature) : Prop :=
  (model true).IsSubgamePerfect (terminates true) profile (payoff true prefer)

def targetSPE (prefer : Bool) (profile : Profile (model false).strategicSignature) : Prop :=
  (model false).IsSubgamePerfect (terminates false) profile (payoff false prefer)

/-- Adding an SPE request cannot manufacture a missing elision certificate. -/
theorem no_uniform_elision_certificate :
    ¬ ∃ compile : Profile (model true).strategicSignature →
        Profile (model false).strategicSignature,
      PreservesOn compile sourceSPE targetSPE (fun _ => True) := by
  rintro ⟨compile, proof⟩
  apply no_utility_independent_spe_compiler
  exact ⟨compile, fun prefer => proof prefer trivial sourceProfile⟩

/-- Keeping the full semantic interface needs no elision claim. This is only
the identity edge; the full-interface-to-runtime edge remains a separate duty. -/
theorem explicit_interface_certificate :
    PreservesOn id targetSPE targetSPE (fun _ => True) :=
  identity targetSPE (fun _ => True)

/-- A proper off-path root survives a restriction on prescribed behavior. -/
theorem full_interface_has_failure_root : (model false).IsSubgameRoot failedRoot :=
  failedRoot_subgame

end GameTheoryExtensionsTests.PreservationContracts
