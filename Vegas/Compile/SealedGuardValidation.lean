/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPublicStore
import Vegas.EventGraph.GuardValidation
import Interaction.SealedOpeningValidation

/-! # Compiling opening-time guard validation

The public opening validator follows the reveal's producer and evaluates its
retained guard code against public initial fields and included opening events.
It never reads the candidate catalog. Missing or ill-typed reads reject the
opening. Commitment acceptance remains the candidate host's opaque selection.

These are local compiler/handler laws, not a generalization of the whole-program
`SealedFragment` strategic theorem. Public read availability, agreement with the
commitment's source context, and legal timeout defaults remain obligations of
that generalization. Private guard dependencies require additional machinery.
-/

namespace Vegas.EventGraph.Graph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- The compiled public guard check for a value-bearing opening. The producer
must be an actual graph commitment, and the claimed value must have its type. -/
def sealedOpeningValidator (G : Graph Player L) (ty : L.Ty) :
    SealedResolution.PublicOpeningValidator Player (L.Val ty) := fun node events claimed =>
  match G.node? node with
  | some (.reveal source) =>
      if source < G.initialFields.length then false
      else
        match G.node? (source - G.initialFields.length) with
        | some (.commit _ guard) =>
            (((⟨ty, claimed⟩ : TypedValue L).as? guard.ty).bind fun value =>
              guard.evalValidationStore? value (G.publicSealedStore ty events)).getD false
        | _ => false
  | _ => false

/-- A correctly linked reveal checks the producer's guard using only the
public event reconstruction. No supported-fragment or universally true guard
premise is needed to compile this check. -/
theorem sealedOpeningValidator_reveal (G : Graph Player L)
    (node producer : Nat) (owner : Player) (guard : EventGuard L)
    (hnode : G.node? node = some (.reveal (G.nodeTarget producer)))
    (hproducer : G.node? producer = some (.commit owner guard))
    (events : List (SealedProgram.Event Player (L.Val guard.ty)))
    (value : L.Val guard.ty) :
    G.sealedOpeningValidator guard.ty node events value =
      (guard.evalValidationStore? value (G.publicSealedStore guard.ty events)).getD false := by
  simp [sealedOpeningValidator, hnode, nodeTarget, hproducer, TypedValue.as?]

/-- At a source-agreeing public context, opening validation is exactly the
graph guard predicate, including for guards that reject some choices. -/
theorem sealedOpeningValidator_eq_guard (G : Graph Player L)
    (node producer : Nat) (owner : Player) (guard : EventGuard L)
    (hnode : G.node? node = some (.reveal (G.nodeTarget producer)))
    (hproducer : G.node? producer = some (.commit owner guard))
    (hpublic : guard.PubliclyValidatable G)
    (events : List (SealedProgram.Event Player (L.Val guard.ty)))
    (value : L.Val guard.ty) (store : Store L) (env : ReadEnv L guard.choiceReads)
    (henv : ReadEnv.ofStore? store guard.choiceReads = some env)
    (hagrees : ∀ ref, G.fieldRefPublic ref →
      Store.getAs (G.publicSealedStore guard.ty events) ref.field ref.ty =
        Store.getAs store ref.field ref.ty) :
    G.sealedOpeningValidator guard.ty node events value = guard.eval value env := by
  rw [G.sealedOpeningValidator_reveal node producer owner guard hnode hproducer events value,
    guard.evalValidationStore?_eq_some_of_public G hpublic value env store
      (G.publicSealedStore guard.ty events) henv hagrees]
  rfl

end Vegas.EventGraph.Graph

/-- info: 'Vegas.EventGraph.Graph.sealedOpeningValidator_eq_guard'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.Graph.sealedOpeningValidator_eq_guard
