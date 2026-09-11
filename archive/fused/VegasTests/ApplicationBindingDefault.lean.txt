/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationBindingDefault
import VegasTests.BindingSourceCoupling

/-! # Public-default readout and exact source continuation

The owner has privately prepared true; the certified fallback selects false.
Readout and source refinement use the recorded fallback, while private history
and preparation retain the owner's original choice. This exercises the state
operation, not a generated binding-expiry transaction or a profile-law claim.
-/

noncomputable section

namespace VegasTests.ApplicationBindingDefault

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
open VegasTests.PersistentDisclosure VegasTests.GeneratedPersistentDisclosure
open VegasTests.GeneratedBindingPolicy

def fallback : SourceDecisionSite.PublicFallback site where
  expr := .constBool false
  legal _ := rfl

def defaulted : Vegas.ApplicationImage.State TestPlayer simpleExpr :=
  (registered true).native.application.defaultBind code ⟨.bool, false⟩

theorem retains_private_preparation : defaulted.prepared.lookup (0, 0) =
    some ⟨.bool, true⟩ := rfl

/-- Existing owner history cannot replace the accepted public fallback. -/
theorem readout_uses_default :
    image.ownerReadStore 0 ((registered true).principalHistory 0)
      defaulted.memory 0 = some ⟨.bool, false⟩ := by
  exact image.ownerReadStore_defaultBind 0 ((registered true).principalHistory 0)
    (registered true).native.application code ⟨.bool, false⟩ (by rfl)

theorem default_is_public : defaulted.memory.accepted 0 =
    some (.publicDefault ⟨.bool, false⟩) :=
  (registered true).native.application.defaultBind_accepted code ⟨.bool, false⟩

theorem rejects_wrong_type_readout :
    Store.getAs (image.ownerReadStore 0 ((registered true).principalHistory 0)
      defaulted.memory) 0 .int = none := by
  simp [Store.getAs, readout_uses_default, TypedValue.as?]

/-- The fallback's actual value is reflected in the original source
continuation, independently of the conflicting private preparation. -/
theorem default_source_successor :
    ∃ next : CoupledAt GeneratedPersistentDisclosure.compiled.graph
        BindingSourceCoupling.nextBuild,
      next.current.source = source.env.cons false ∧ defaulted.Refines next.current.graph.1 := by
  have hrefines : (registered true).native.application.Refines
      BindingSourceCoupling.checkpoint.current.graph.1 :=
    (Vegas.ApplicationImage.State.initial_refines
      GeneratedPersistentDisclosure.compiled.graph).register 0 0 ⟨.bool, true⟩
  have hresult := SourceDecisionSite.PublicFallback.defaultBind_source_coupling
    (P := TestPlayer) (L := simpleExpr) (Γ := []) (name := 0) (who := 0) (ty := .bool)
    (.constBool true) _ fallback source.fresh compilerInitial
    BindingSourceCoupling.checkpoint (registered true).native.application hrefines
  exact hresult.2

theorem rejects_late_binding (serial : Nat) :
    image.handle defaulted ⟨(0, serial), .binding 0 (0, 0)⟩ = none := by
  have hcode : image.lookup 0 = some (.bind code) := by
    apply applicationPlan.image_lookup_of_mem (fun _ => 10) (.bind code)
    change _ ∈ [ApplicationInstruction.bind code, _, _, _, _, _]
    simp
  exact image.handle_binding_after_default (registered true).native.application 0 code hcode
    ⟨.bool, false⟩ (0, serial) (0, 0)

end VegasTests.ApplicationBindingDefault

/-- info: 'VegasTests.ApplicationBindingDefault.default_source_successor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationBindingDefault.default_source_successor
