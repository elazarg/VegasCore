/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.GraphBindingDiscipline
import Vegas.Expr.Simple
import VegasTests.SourceSetup

/-! # Binding payload discipline regressions -/

namespace VegasTests.GraphBindingDiscipline

open Vegas

private def liftPublicationEquiv {α β : Type} (e : α ≃ β) :
    PublicationResult α ≃ PublicationResult β where
  toFun
    | .failure => .failure
    | .success value => .success (e value)
  invFun
    | .failure => .failure
    | .success value => .success (e.symm value)
  left_inv value := by cases value <;> simp
  right_inv value := by cases value <;> simp

/-- A lawful but non-injective result constructor. In particular, option-bool
and result-bool payloads share the same graph result type. -/
private def aliasedResult : BaseTy → BaseTy
  | .result .bool => .result (.option .bool)
  | payload => .result payload

private def aliasedValueEquiv (payload : BaseTy) :
    Val (aliasedResult payload) ≃ PublicationResult (Val payload) := by
  cases payload with
  | int => exact Equiv.refl _
  | bool => exact Equiv.refl _
  | word => exact Equiv.refl _
  | range lo hi => exact Equiv.refl _
  | option payload => exact Equiv.refl _
  | result payload =>
      cases payload with
      | bool =>
          exact (liftPublicationEquiv PublicationResult.equivOption.symm).trans
            (Equiv.swap .failure (.success .failure))
      | int => exact Equiv.refl _
      | word => exact Equiv.refl _
      | range lo hi => exact Equiv.refl _
      | option payload => exact Equiv.refl _
      | result payload => exact Equiv.refl _

section Aliased

private local instance aliasedResultTypes : IExpr.ResultTypes simpleExpr where
  result := aliasedResult
  valueEquiv := aliasedValueEquiv

private abbrev BoundPayload : BaseTy := .option .bool
private abbrev ResolvedPayload : BaseTy := .result .bool

/-- The very same stored raw value is a timeout under the binding payload but
a successful publication under the aliased resolve payload. -/
theorem aliased_failure_decodes_as_success :
    aliasedValueEquiv ResolvedPayload
        ((aliasedValueEquiv BoundPayload).symm .failure) =
      .success .failure := by
  rfl

private def aliasedGraph : Graph Unit simpleExpr []
    [(2, .pub (aliasedResult ResolvedPayload)),
      (1, .sealed () (aliasedResult BoundPayload))] :=
  .bind 1 () (payload := BoundPayload) (by decide) <|
    .resolve 2 () 1 (payload := ResolvedPayload) (by decide) .here [] <|
      .ret []

/-- Merely matching the stored result type is insufficient: resolving a name
under a different payload interpretation is rejected by the origin witness. -/
theorem aliasedGraph_rejected :
    ¬ Graph.BindingDiscipline Graph.BindingOrigins.none aliasedGraph := by
  intro discipline
  have payloadEq : BoundPayload = ResolvedPayload :=
    discipline.1 BoundPayload (by simp [Graph.BindingOrigins.insert])
  simp [BoundPayload, ResolvedPayload] at payloadEq

end Aliased

/-- Real compiled setup graphs carry the positive certificate directly. -/
example : Graph.BindingDiscipline Graph.BindingOrigins.none
    VegasTests.SourceSetup.fairSetup.graph :=
  VegasTests.SourceSetup.fairSetup.graph_bindingDiscipline

end VegasTests.GraphBindingDiscipline
