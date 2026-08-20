/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ClassicalEVM
import Vegas.Machine.Contract.BooleanEVMRuntime

/-!
# Checked-source Boolean EVM runtime compiler

This is the first source-to-runtime-bytecode backend. It is intentionally
partial: the source must have Boolean graph storage, no sample nodes, a
permissionless reveal policy, and guards accepted by the concrete Boolean
expression compiler. Handler generation, image-size checking, local-label
resolution, selector linking, and opcode emission are otherwise automatic.

The returned runtime image is actual EVM bytecode. A VM-semantics correctness
theorem remains separate; this module does not call successful emission a
semantic or game-preservation result.
-/

namespace Vegas.ClassicalCompiler

open Machine
open Machine.Contract

noncomputable section

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {source : WFProgram Player simpleExpr}

namespace EVMByteBackend

/-- Compile the supported Boolean/no-sample fragment all the way to linked EVM
runtime bytes. Unsupported guards, unresolved labels, or an oversized image
return `none`. -/
def compileBooleanNoSampleRuntime?
    (backend : EVMByteBackend source Address)
    (usesBool : EVM.UsesOnlyBoolStorage (Machine.compile source))
    (noSamples : EVM.HasNoSampleNodes (Machine.compile source))
    (_permissionlessReveals :
      backend.classical.reveals = TriggerPolicy.permissionless) :
    Option (EVM.RuntimeImage backend.selectors) :=
  match EVM.compileBooleanNoSampleHandlers? noSamples usesBool
      backend.classical.players backend.players backend.addresses with
  | none => none
  | some handlers => EVM.RuntimeImage.linkLocalChecked?
      backend.selectors handlers

end EVMByteBackend

end

end Vegas.ClassicalCompiler
