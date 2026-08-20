/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Classical
import Vegas.Machine.Contract.ClassicalEVMBytes

/-!
# Checked source to deterministic EVM-byte contract artifact

This module assembles the ordinary classical compiler with the complete
four-entry-point EVM calldata codec.  The result has EVM-sized selector/word
bytes, blockchain-supplied caller context, deterministic receive/revert
behavior, canonical storage, and ordered oracle request actions.

It is deliberately named a byte-calldata artifact, not EVM bytecode. Retained
expression code, checks, state updates, and dispatch still need lowering to an
instruction IR and an emitter with a VM-level correctness theorem.
-/

noncomputable section

namespace Vegas.ClassicalCompiler

open Machine
open Machine.Contract
open Machine.Contract.Blockchain

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr}

/-- A deterministic contract paired with its complete EVM byte-calldata ABI. -/
structure EVMByteArtifact (source : WFProgram Player L) (Address : Type)
    [DecidableEq Address] where
  contract : ClassicalContract (Machine.compile source) Address
  abi : EVM.ClassicalABI (Machine.compile source) contract.codec.Word

namespace EVMByteArtifact

variable {source : WFProgram Player L}
variable (artifact : EVMByteArtifact source Address)

abbrev State := artifact.contract.State

/-- Canonical constructor state of the byte-calldata artifact. -/
def initial : artifact.State := artifact.contract.initial

/-- Deterministic byte-calldata receive function with the physical caller
supplied by blockchain context. -/
def receive (context : CallContext Address) (state : artifact.State)
    (calldata : EVM.ByteCalldata) :
    DeterministicResult artifact.State OracleProtocol.Request :=
  artifact.contract.receiveEVMBytes artifact.abi context state calldata

/-- Standard deterministic-contract packaging of the executable byte endpoint.
No entropy argument remains because chance is represented by oracle callback
calldata. -/
def toDeterministicContract :
    DeterministicContract Address EVM.ByteCalldata artifact.State
      OracleProtocol.Request Unit where
  initial := artifact.initial
  receive := fun _chain context state calldata _unit =>
    artifact.receive context state calldata

/-- Every encoded message reaches exactly the typed classical receive
function after caller contextualization. -/
@[simp] theorem receive_encode
    (context : CallContext Address) (state : artifact.State)
    (message :
      EVM.ClassicalMessage (Machine.compile source)
        artifact.contract.codec.Word) :
    artifact.receive context state (artifact.abi.encodeBytes message) =
      artifact.contract.receive state (message.contextualize context) := by
  exact artifact.contract.receiveEVMBytes_encode artifact.abi context state
    message

end EVMByteArtifact

/-- Backend choices needed to compile checked source to the executable
EVM-byte-calldata artifact. Node capacity is the concrete 256-bit bound; value
and player codecs provide lossless word representations for this program. -/
structure EVMByteBackend (source : WFProgram Player L) (Address : Type)
    [DecidableEq Address] where
  classical : Backend source Address
  selectors : EVM.ClassicalSelectors
  players : WireCodec Player EVM.Word
  nodesFit : EVM.NodesFitWord (Machine.compile source)
  values : WireCodec classical.codec.Word EVM.Word

namespace EVMByteBackend

variable {source : WFProgram Player L}
variable (backend : EVMByteBackend source Address)

/-- Compile the checked source and all supplied representation choices to one
deterministic byte-calldata artifact. -/
def compile : EVMByteArtifact source Address where
  contract := backend.classical.compile
  abi :=
    { selectors := backend.selectors
      players := backend.players
      nodes := EVM.nodeWordCodec (Machine.compile source) backend.nodesFit
      values := backend.values }

@[simp] theorem compile_contract :
    backend.compile.contract = backend.classical.compile :=
  rfl

@[simp] theorem compile_initial :
    backend.compile.initial = backend.classical.compile.initial :=
  rfl

/-- The final ordinary compiler endpoint is a deterministic contract over raw
EVM-shaped byte calldata. -/
def artifact := backend.compile.toDeterministicContract

end EVMByteBackend

end Vegas.ClassicalCompiler
