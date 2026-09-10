/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

/-! # Public dispositions of a resolved binding

A runtime can resolve a binding by accepting an opaque reference or by
selecting a public fallback value. The public carrier records which occurred.
The value behind an opaque reference, including failure to recover any value,
belongs to the private verifier, not to this carrier.
-/

namespace Interaction

universe uHandle uValue

/-- Public evidence of binding resolution. A default contains its actual value
and provides no opaque-reference or commitment-verification evidence. -/
inductive BindingDisposition (Handle : Type uHandle) (Value : Type uValue) where
  | opaque (handle : Handle)
  | publicDefault (value : Value)
  deriving DecidableEq

namespace BindingDisposition

variable {Handle : Type uHandle} {Value : Type uValue}

/-- The opaque-only projection rejects public defaults instead of inventing
a reference for them. Consumers of defaults must handle that case explicitly. -/
def opaqueHandle? : BindingDisposition Handle Value → Option Handle
  | .opaque handle => some handle
  | .publicDefault _ => none

@[simp] theorem opaqueHandle?_opaque (handle : Handle) :
    (.opaque handle : BindingDisposition Handle Value).opaqueHandle? = some handle := rfl

@[simp] theorem opaqueHandle?_publicDefault (value : Value) :
    (.publicDefault value : BindingDisposition Handle Value).opaqueHandle? = none := rfl

theorem opaqueHandle?_eq_some_iff (binding : BindingDisposition Handle Value)
    (handle : Handle) : binding.opaqueHandle? = some handle ↔ binding = .opaque handle := by
  cases binding <;> simp [opaqueHandle?]

/-- Recognize an accepted opaque handle without deciding equality of payload
values. Public-default values need no equality instance for this query. -/
theorem bind_opaqueHandle?_eq_some_iff
    (binding : Option (BindingDisposition Handle Value)) (handle : Handle) :
    binding.bind opaqueHandle? = some handle ↔ binding = some (.opaque handle) := by
  cases binding <;> simp [opaqueHandle?_eq_some_iff]

end BindingDisposition

end Interaction
