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

/-- Constructor `SSTORE`s for every nonzero cell in an ordered key list. -/
def compileStorageWrites (slots : List Nat)
    (storage : TotalStorage) : Assembly :=
  slots.flatMap fun slot =>
    let value := storage slot
    if value = 0 then []
    else
      [ .push (.word value),
        .push (.nat256 slot),
        .sstore ]

/-- Constructor `SSTORE`s for every nonzero cell in the finite certified
layout. -/
def compileStorageInitialization (slotCount : Nat)
    (storage : TotalStorage) : Assembly :=
  compileStorageWrites (List.range slotCount) storage

/-- Storage transformer denoted by an ordered constructor write list. -/
def applyStorageWrites (slots : List Nat) (target current : TotalStorage) :
    TotalStorage :=
  match slots with
  | [] => current
  | slot :: rest =>
      let next :=
        if target slot = 0 then current
        else Function.update current slot (target slot)
      applyStorageWrites rest target next

theorem applyStorageWrites_append (left right : List Nat)
    (target current : TotalStorage) :
    applyStorageWrites (left ++ right) target current =
      applyStorageWrites right target
        (applyStorageWrites left target current) := by
  induction left generalizing current with
  | nil => rfl
  | cons slot rest ih =>
      by_cases hzero : target slot = 0
      · simp [applyStorageWrites, hzero, ih]
      · simp [applyStorageWrites, ih]

/-- Starting from zero storage, ordered writes over `range slotCount` install
the target inside the range and leave every other key zero. -/
theorem applyStorageWrites_range_apply (slotCount : Nat)
    (target : TotalStorage) (key : Nat) :
    applyStorageWrites (List.range slotCount) target (fun _ => 0) key =
      if key < slotCount then target key else 0 := by
  induction slotCount with
  | zero => simp [applyStorageWrites]
  | succ slotCount ih =>
      rw [List.range_succ, applyStorageWrites_append]
      simp only [applyStorageWrites]
      by_cases hzero : target slotCount = 0
      · rw [if_pos hzero, ih]
        by_cases hkey : key = slotCount
        · subst key
          simp [hzero]
        · by_cases hlt : key < slotCount <;> simp [hlt] <;> omega
      · rw [if_neg hzero]
        by_cases hkey : key = slotCount
        · subst key
          simp [Function.update]
        · simp only [Function.update, hkey]
          rw [ih]
          by_cases hlt : key < slotCount <;> simp [hlt] <;> omega

/-- A finitely supported target is installed exactly by its constructor write
range. -/
theorem applyStorageWrites_range_eq_target (slotCount : Nat)
    (target : TotalStorage)
    (hzeroOutside : ∀ key, slotCount ≤ key → target key = 0) :
    applyStorageWrites (List.range slotCount) target (fun _ => 0) = target := by
  funext key
  rw [applyStorageWrites_range_apply]
  split
  · rfl
  · symm
    exact hzeroOutside key (Nat.le_of_not_gt ‹_›)

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
  slotCount_fits : slotCount ≤ 2 ^ 256
  initialStorage : TotalStorage
  storage_zero_outside :
    ∀ slot, slotCount ≤ slot → initialStorage slot = 0
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
    (slotCountFits : slotCount ≤ 2 ^ 256)
    (storage : TotalStorage)
    (storageZeroOutside : ∀ slot, slotCount ≤ slot → storage slot = 0) :
    Option (DeploymentImage selectors) :=
  let initialization := compileStorageInitialization slotCount storage
  let runtimeOffset := initialization.byteLength + 21
  if hfits : runtimeOffset < 2 ^ 32 then
    some
      { runtime := runtime
        slotCount := slotCount
        slotCount_fits := slotCountFits
        initialStorage := storage
        storage_zero_outside := storageZeroOutside
        offset_fits := hfits }
  else
    none

theorem build?_runtime {runtime : RuntimeImage selectors} {slotCount : Nat}
    {slotCountFits : slotCount ≤ 2 ^ 256}
    {storage : TotalStorage}
    {storageZeroOutside : ∀ slot, slotCount ≤ slot → storage slot = 0}
    {image : DeploymentImage selectors}
    (hbuild : build? runtime slotCount slotCountFits storage
      storageZeroOutside = some image) :
    image.runtime = runtime := by
  simp only [build?] at hbuild
  split at hbuild
  · cases hbuild
    rfl
  · contradiction

theorem build?_slotCount {runtime : RuntimeImage selectors} {slotCount : Nat}
    {slotCountFits : slotCount ≤ 2 ^ 256}
    {storage : TotalStorage}
    {storageZeroOutside : ∀ slot, slotCount ≤ slot → storage slot = 0}
    {image : DeploymentImage selectors}
    (hbuild : build? runtime slotCount slotCountFits storage
      storageZeroOutside = some image) :
    image.slotCount = slotCount := by
  simp only [build?] at hbuild
  split at hbuild
  · cases hbuild
    rfl
  · contradiction

theorem build?_initialStorage {runtime : RuntimeImage selectors}
    {slotCount : Nat} {storage : TotalStorage}
    {slotCountFits : slotCount ≤ 2 ^ 256}
    {storageZeroOutside : ∀ slot, slotCount ≤ slot → storage slot = 0}
    {image : DeploymentImage selectors}
    (hbuild : build? runtime slotCount slotCountFits storage
      storageZeroOutside = some image) :
    image.initialStorage = storage := by
  simp only [build?] at hbuild
  split at hbuild
  · cases hbuild
    rfl
  · contradiction

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
