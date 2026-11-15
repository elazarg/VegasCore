module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.Code

@[expose] public section

/-! # The commitment field consumed by a resolution node -/

namespace Vegas.EventGraph.EventCode

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L] {Field : Type} [DecidableEq Field]
  {layout : Field → EventField Player L}

def resolutionField? : {output : EventField Player L} → EventCode layout output → Option Field
  | _, .resolve _ _ binding _ => some binding.field
  | _, .bind .. | _, .sample .. => none

@[simp] theorem resolutionField?_cast {first second : EventField Player L}
    (equal : first = second) (code : EventCode layout first) :
    (cast (congrArg (EventCode layout) equal) code).resolutionField? = code.resolutionField? := by
  cases equal
  rfl

/-- A resolution-field match identifies the complete typed resolve node. -/
theorem eq_resolve_of_resolutionField {output : EventField Player L}
    (code : EventCode layout output) {owner : Player} {payload : L.Ty}
    (subject : FieldRef layout (.binding owner payload))
    (resolved : code.resolutionField? = some subject.field) :
    ∃ equal : output = .publication payload,
      ∃ checks : List (GuardCheck layout payload),
        cast (congrArg (EventCode layout) equal) code = .resolve owner payload subject checks := by
  cases code with
  | bind => cases resolved
  | sample => cases resolved
  | resolve other otherPayload binding checks =>
      have fields : binding.field = subject.field := Option.some.inj resolved
      have kinds : EventField.binding other otherPayload = .binding owner payload :=
        binding.layout_eq.symm.trans (fields ▸ subject.layout_eq)
      obtain ⟨rfl, rfl⟩ := EventField.binding.inj kinds
      have refs : binding = subject := by cases binding; cases subject; simp_all
      subst refs
      exact ⟨rfl, checks, rfl⟩

/-- A resolution subject is among the node's declared reads. -/
theorem resolutionField?_mem_readFields {output : EventField Player L}
    (code : EventCode layout output) (field : Field)
    (resolved : code.resolutionField? = some field) : field ∈ code.readFields := by
  cases code with
  | bind => cases resolved
  | sample => cases resolved
  | resolve owner payload binding checks =>
      have same : binding.field = field := Option.some.inj resolved
      rw [← same]
      exact Finset.mem_insert_self _ _

end Vegas.EventGraph.EventCode
