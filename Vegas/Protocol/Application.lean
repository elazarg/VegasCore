/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.OrderedProtocol
import Vegas.EventGraph.GuardValidation
import Vegas.Protocol.Code

/-! # Hosting typed protocol code in the generic ordered runtime

This adapter erases source types to `TypedValue` tags while retaining executable
guard and chance code in ideal capabilities. It supplies no source alternative:
deadlines and resolution values are explicit caller-provided protocol metadata.
In particular, raw commitment candidates remain distinct from legal graph
values until an authenticated opening is decoded and validated.
-/

noncomputable section

namespace Vegas.Protocol

open GameTheory.Math.Probability
open Vegas.EventGraph
open Interaction

variable {Player : Type} {L : IExpr}

/-- Host choices which do not follow from retained graph syntax. A missing
resolution remains missing; the adapter never fabricates a default. -/
structure Hosting (code : Code Player L) where
  deadline : (site : Fin code.operations.length) → Nat
  resolution? : (site : Fin code.operations.length) → Option (TypedValue L)
  bindingMode : (site : Fin code.operations.length) → OrderedProtocol.BindingMode
  disclosureMode : (site : Fin code.operations.length) → OrderedProtocol.DisclosureMode

namespace Code

/-- Erase typed field references to the graph's exact numeric field ids. -/
def readFields (refs : Finset (FieldRef L)) : List OrderedProtocol.Field :=
  refs.toList.map FieldRef.field

/-- Classify a graph field in the uncompressed initial/operation layout.
Well-formed graph lowering ensures reveal sources are in one of these ranges. -/
def runtimeOrigin (code : Code Player L) (field : Nat) : OrderedProtocol.FieldOrigin :=
  if field < code.initial.length then .initial field
  else .operation (field - code.initial.length)

/-- Guard retained at a commit-produced field, when that field denotes a
commit in this code. -/
def commitGuardAt? (code : Code Player L) (field : Nat) : Option (EventGuard L) :=
  match classifyField? Player L code field with
  | some (.operation site) =>
      match code.operations[site]? with
      | some (.commit _ guard) => some guard
      | _ => none
  | some (.initial _) | none => none

/-- Reads needed by a reveal opening validator. Initial-field reveals are
automatic and need only their source field; commit-produced reveals use the
producer guard's executable validation footprint. -/
def revealReads (code : Code Player L) (source : FieldRef L) : List OrderedProtocol.Field :=
  match code.commitGuardAt? source.field with
  | some guard => readFields guard.validationReads
  | none => [source.field]

def operationReads (code : Code Player L) : Operation Player L → List OrderedProtocol.Field
  | .chance dist => readFields dist.reads
  | .commit _ guard => readFields guard.validationReads
  | .reveal source => code.revealReads source

def operationKind (code : Code Player L) (hosting : Hosting code)
    (site : Fin code.operations.length) : OrderedProtocol.SiteKind Player :=
  match code.operations.get site with
  | .chance _ => .chance
  | .commit owner _ => .commit owner (hosting.bindingMode site)
  | .reveal source =>
      .reveal (code.runtimeOrigin source.field) (hosting.disclosureMode site)

/-- One typed operation erased to generic runtime code. Resolution remains an
explicit hosting choice and is not inferred from type defaults. -/
def runtimeSite (code : Code Player L) (hosting : Hosting code)
    (site : Fin code.operations.length) :
    OrderedProtocol.Site Player L.Ty (TypedValue L) :=
  let operation := code.operations.get site
  { kind := code.operationKind hosting site
    tag := operation.ty
    reads := code.operationReads operation
    resolution? := hosting.resolution? site
    deadline := hosting.deadline site }

/-- Public runtime code. Initial values remain absent. -/
def runtimeCode (code : Code Player L) (hosting : Hosting code) :
    OrderedProtocol.Code Player L.Ty (TypedValue L) where
  initial := code.initial.map fun field =>
    { owner := field.owner
      tag := field.ty
      automaticPublic := field.owner.isNone }
  sites := List.ofFn (code.runtimeSite hosting)

/-- Separate ideal setup passed to `OrderedProtocol.Runtime.initial?`. -/
def runtimeInitialInputs (code : Code Player L) (input : code.InitialInput) :
    List (OrderedProtocol.InitialInput L.Ty (TypedValue L)) :=
  List.ofFn fun slot =>
    { tag := (code.initial.get slot).ty
      value := ⟨(code.initial.get slot).ty, input slot⟩ }

end Code

/-- View a generic finite runtime snapshot as the existing typed graph store.
Wrong tags remain observable as failed `Store.getAs` lookups. -/
def typedStore (store : OrderedProtocol.Store (TypedValue L)) : EventGraph.Store L :=
  fun field => store.lookup field

private def hasTag (tag : L.Ty) (value : TypedValue L) : Bool :=
  decide (value.ty = tag)

private def validate (code : Code Player L) (site : Nat)
    (bound _effective : OrderedProtocol.Store (TypedValue L)) (raw : TypedValue L) :
    OrderedProtocol.Validation :=
  match code.operations[site]? with
  | some (.commit _ guard) =>
      if hty : raw.ty = guard.ty then
        let action : L.Val guard.ty := cast (congrArg L.Val hty) raw.value
        -- `bound` is the captured commit-time context. The effective snapshot
        -- is deliberately not substituted for it after earlier resolutions.
        match guard.evalValidationStore? action (typedStore bound) with
        | some true => .accept
        | some false => .reject
        | none => .unavailable
      else .reject
  | some (.chance _) | some (.reveal _) | none => .unavailable

private def sample (code : Code Player L) (site : Nat) (tag : L.Ty)
    (snapshot : OrderedProtocol.Store (TypedValue L)) :
    Option (FinDist (TypedValue L)) :=
  match code.operations[site]? with
  | some (.chance dist) =>
      if _htag : dist.ty = tag then
        match ReadEnv.ofStoreExec? (typedStore snapshot) dist.reads with
        | some reads => some <|
            (dist.eval reads).map fun value =>
              (⟨dist.ty, value⟩ : TypedValue L)
        | none => none
      else none
  | some (.commit _ _) | some (.reveal _) | none => none

/-- Ideal executable capabilities induced by retained graph code. Guard checks
use the captured bound snapshot. The effective snapshot remains a distinct
runtime argument; relating post-resolution contexts is a later correspondence
obligation, not asserted here. -/
def capabilities (code : Code Player L) :
    OrderedProtocol.Capabilities L.Ty (TypedValue L) where
  hasTag := hasTag
  validate site bound effective raw := validate code site bound effective raw
  sample site tag snapshot := sample code site tag snapshot
  sample_typed := by
    intro site tag snapshot law value hlaw hvalue
    unfold sample at hlaw
    split at hlaw <;> try contradiction
    next dist hoperation =>
      split at hlaw <;> try contradiction
      next htag =>
        split at hlaw <;> try contradiction
        next reads hreads =>
          cases hlaw
          rw [FinDist.support_map] at hvalue
          obtain ⟨source, _hsource, rfl⟩ := hvalue
          simp [hasTag, htag]

/-- Complete generic ordered runtime for public code and explicit hosting
metadata. This construction carries no Nash or source-settlement theorem. -/
def runtime (code : Code Player L) (hosting : Hosting code) :
    OrderedProtocol.Runtime Player L.Ty (TypedValue L) where
  code := code.runtimeCode hosting
  capabilities := capabilities code

end Vegas.Protocol
