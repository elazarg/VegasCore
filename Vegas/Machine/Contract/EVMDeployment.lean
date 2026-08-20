/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Contract.EVMLocalAssembly
import Vegas.Machine.Contract.ClassicalEVMStorage

/-!
# Deployable EVM creation bytecode

Runtime bytecode is not a deployment artifact. A constructor must initialize
nonzero account storage, copy the appended runtime code into memory, and return
it. This module emits exactly that creation program.

Zero storage cells are omitted because fresh EVM account storage is zero. The
runtime offset is computed from the emitted initialization prefix; both it and
the runtime length use `PUSH4`, so construction checks the corresponding
32-bit offset bound.
-/

namespace Vegas.Machine.Contract.EVM

/-- Constructor `SSTORE`s for every nonzero cell in the finite certified
layout. -/
def compileStorageInitialization (slotCount : Nat)
    (storage : TotalStorage) : Assembly :=
  (List.range slotCount).flatMap fun slot =>
    let value := storage slot
    if value = 0 then []
    else
      [ .push (.word value),
        .push (.nat256 slot),
        .sstore ]

/-- Fixed 21-byte suffix of the constructor. It copies the appended runtime
from `runtimeOffset` and returns it as deployed code. -/
def deploymentCopyReturn (runtimeOffset runtimeSize : Nat) : Assembly :=
  [ .push (.nat32 runtimeSize),
    .push (.nat32 runtimeOffset),
    .push (.one (byte 0)),
    .codecopy,
    .push (.nat32 runtimeSize),
    .push (.one (byte 0)),
    .return ]

@[simp] theorem deploymentCopyReturn_byteLength
    (runtimeOffset runtimeSize : Nat) :
    (deploymentCopyReturn runtimeOffset runtimeSize).byteLength = 21 := by
  simp [deploymentCopyReturn, Assembly.byteLength, Instruction.byteLength]

/-- Actual EVM creation bytecode paired with the runtime image it deploys. -/
structure DeploymentImage (selectors : ClassicalSelectors) where
  runtime : RuntimeImage selectors
  slotCount : Nat
  initialStorage : TotalStorage
  offset_fits :
    (compileStorageInitialization slotCount initialStorage).byteLength + 21 <
      2 ^ 32

namespace DeploymentImage

variable {selectors : ClassicalSelectors}

/-- Constructor writes determined by the intended initial account state. -/
def initialization (image : DeploymentImage selectors) : Assembly :=
  compileStorageInitialization image.slotCount image.initialStorage

/-- Byte offset at which the appended runtime begins. -/
def runtimeOffset (image : DeploymentImage selectors) : Nat :=
  image.initialization.byteLength + 21

/-- The derived runtime offset is represented exactly by `PUSH4`. -/
theorem runtimeOffset_fits (image : DeploymentImage selectors) :
    image.runtimeOffset < 2 ^ 32 :=
  image.offset_fits

/-- The constructor assembly determined by the certified layout. -/
def creationAssembly (image : DeploymentImage selectors) : Assembly :=
  image.initialization ++
    deploymentCopyReturn image.runtimeOffset image.runtime.bytecode.length

/-- Deployable creation bytes: constructor followed by its runtime payload. -/
def bytecode (image : DeploymentImage selectors) : List Byte :=
  image.creationAssembly.emit ++ image.runtime.bytecode

/-- Build creation bytecode after checking its computed runtime offset. -/
def build? (runtime : RuntimeImage selectors) (slotCount : Nat)
    (storage : TotalStorage) : Option (DeploymentImage selectors) :=
  let initialization := compileStorageInitialization slotCount storage
  let runtimeOffset := initialization.byteLength + 21
  if hfits : runtimeOffset < 2 ^ 32 then
    some
      { runtime := runtime
        slotCount := slotCount
        initialStorage := storage
        offset_fits := hfits }
  else
    none

/-- The runtime begins at exactly the byte offset returned by the constructor
layout calculation. -/
@[simp] theorem creationAssembly_byteLength
    (image : DeploymentImage selectors) :
    image.creationAssembly.byteLength = image.runtimeOffset := by
  simp [DeploymentImage.creationAssembly, DeploymentImage.runtimeOffset]

/-- Creation bytecode is the constructor prefix followed by the exact runtime
bytes. -/
@[simp] theorem bytecode_length (image : DeploymentImage selectors) :
    image.bytecode.length =
      image.runtimeOffset + image.runtime.bytecode.length := by
  simp [DeploymentImage.bytecode]

/-- The prefix before the derived runtime offset is exactly the emitted
constructor. -/
@[simp] theorem bytecode_take_runtimeOffset
    (image : DeploymentImage selectors) :
    image.bytecode.take image.runtimeOffset = image.creationAssembly.emit := by
  rw [← image.creationAssembly_byteLength]
  simp [DeploymentImage.bytecode]

/-- The suffix at the derived runtime offset is exactly the linked runtime;
no offset calculation can select different bytes. -/
@[simp] theorem bytecode_drop_runtimeOffset
    (image : DeploymentImage selectors) :
    image.bytecode.drop image.runtimeOffset = image.runtime.bytecode := by
  rw [← image.creationAssembly_byteLength]
  simp [DeploymentImage.bytecode]

end DeploymentImage

end Vegas.Machine.Contract.EVM
