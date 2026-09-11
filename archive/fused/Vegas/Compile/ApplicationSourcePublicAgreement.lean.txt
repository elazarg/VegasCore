/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageStateRefinement
import Vegas.Compile.SourceExecution

/-! # Identifying source values through shared public memory -/

namespace Vegas.ApplicationImage.State

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Two source configurations represented by states with equal public memory
agree at every compiler field that is public in both graphs. The graphs may
differ; only the compiler allocation of the queried source binding is shared. -/
theorem publicSourceValue_eq_of_memory_eq
    {Γ : VCtx P L} {Gleft Gright : Graph P L}
    {build : BuildState P L Γ}
    {leftCurrent : CoupledState Gleft build}
    {rightCurrent : CoupledState Gright build}
    {left right : ApplicationImage.State P L}
    (hleft : left.Refines leftCurrent.graph.1)
    (hright : right.Refines rightCurrent.graph.1)
    (hmemory : left.memory = right.memory)
    {name : VarId} {ty : L.Ty} (source : VHasVar Γ name (.pub ty))
    (hleftPublic : Gleft.fieldRefPublic ⟨build.fieldOf source, ty⟩)
    (hrightPublic : Gright.fieldRefPublic ⟨build.fieldOf source, ty⟩) :
    leftCurrent.source.get source = rightCurrent.source.get source := by
  have hleftValue :
      Store.getAs left.memory.store (build.fieldOf source) ty =
        some (leftCurrent.source.get source) :=
    (hleft.memory.publicFields ⟨build.fieldOf source, ty⟩ hleftPublic).trans
      (leftCurrent.agrees source)
  have hrightValue :
      Store.getAs right.memory.store (build.fieldOf source) ty =
        some (rightCurrent.source.get source) :=
    (hright.memory.publicFields ⟨build.fieldOf source, ty⟩ hrightPublic).trans
      (rightCurrent.agrees source)
  rw [hmemory] at hleftValue
  exact Option.some.inj (hleftValue.symm.trans hrightValue)

end Vegas.ApplicationImage.State

/-- info: 'Vegas.ApplicationImage.State.publicSourceValue_eq_of_memory_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.State.publicSourceValue_eq_of_memory_eq
