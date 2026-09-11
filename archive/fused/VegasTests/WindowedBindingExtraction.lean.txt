/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingBlock
import VegasTests.GeneratedBindingPolicy

/-! # Canonical extraction from generated binding handlers -/

noncomputable section

namespace VegasTests.WindowedBindingExtraction

open Vegas
open VegasTests.PersistentDisclosure
open VegasTests.GeneratedPersistentDisclosure
open VegasTests.GeneratedBindingPolicy

def initial : ApplicationImage.State TestPlayer simpleExpr :=
  ApplicationImage.State.initial
    (ApplicationImage.Memory.initial GeneratedPersistentDisclosure.compiled.graph)

def missing : ApplicationImage.State TestPlayer simpleExpr :=
  initial.bind code (0, 0)

def illTyped : ApplicationImage.State TestPlayer simpleExpr :=
  (initial.register 0 0 ⟨.int, 7⟩).bind code (0, 0)

def overwritten : ApplicationImage.State TestPlayer simpleExpr :=
  (initial.register 0 0 ⟨.bool, true⟩).bind code (0, 0)
    |>.register 0 0 ⟨.bool, false⟩

/-- The generated native handler genuinely accepts a handle with no prepared
value; `missing` is not a manually asserted post-state. -/
theorem handle_accepts_missing_snapshot :
    image.handle initial ⟨(0, 0), .binding 0 (0, 0)⟩ = some missing := by
  rfl

theorem missing_uses_fallback :
    code.resolvedValue (ty := .bool) false missing = false := by
  rfl

/-- Wrong-typed preparation is also accepted and frozen by the generated
native handler. Canonical source extraction subsequently uses the fallback. -/
theorem handle_accepts_illTyped_snapshot :
    image.handle (initial.register 0 0 ⟨.int, 7⟩)
      ⟨(0, 0), .binding 0 (0, 0)⟩ = some illTyped := by
  rfl

theorem illTyped_uses_fallback :
    code.resolvedValue (ty := .bool) false illTyped = false := by
  rfl

/-- A later preparation cannot overwrite the verifier frozen by acceptance. -/
theorem accepted_value_survives_later_registration :
    code.resolvedValue (ty := .bool) false overwritten = true := by
  rfl

end VegasTests.WindowedBindingExtraction
