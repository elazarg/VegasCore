/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Contract.Authentication

/-!
# Player commit calldata

A player call on a word-oriented target carries a physical caller, claimed
semantic player, node id, and one target word.  Decoding inspects the graph row,
requires a commit owned by the claimed player, and decodes the word at the
guard's language type. Caller authentication remains the adjacent certified
registry check.

This is a logical word-level ABI, not byte serialization, gas accounting, or a
specific chain calling convention.
-/

namespace Vegas.Machine.Contract

open EventGraph

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

/-- Word-level player commit calldata. -/
structure PlayerCalldata (Player Address Word : Type) where
  caller : Address
  player : Player
  node : Nat
  value : Word

namespace PlayerCalldata

/-- Decode word-level calldata to the typed authenticated-call boundary. -/
def decode (program : Program Player L) (codec : StorageCodec L)
    (calldata : PlayerCalldata Player Address codec.Word) :
    Option (PlayerCall Player Address L) :=
  if hnode : calldata.node < program.graph.nodeCount then
    let node : Fin program.graph.nodeCount := ⟨calldata.node, hnode⟩
    match (program.graph.nodeRow node).sem with
    | .commit who guard =>
        if calldata.player = who then
          match codec.decodeValue guard.ty calldata.value with
          | none => none
          | some value =>
              some
                { caller := calldata.caller
                  player := calldata.player
                  node := calldata.node
                  value := { ty := guard.ty, value := value } }
        else
          none
    | .sample _ | .reveal _ => none
  else
    none

/-- Encode one valid semantic commit as caller-bearing target words. -/
def encodeCommit (registry : PlayerRegistry Player Address)
    (codec : StorageCodec L) {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    PlayerCalldata Player Address codec.Word where
  caller := registry.address who
  player := who
  node := action.node
  value := codec.encodeValue step.guard.ty step.value

omit [DecidableEq Address] in
/-- Valid semantic commits round-trip through word-level calldata decoding. -/
@[simp] theorem decode_encodeCommit
    (registry : PlayerRegistry Player Address)
    (codec : StorageCodec L) {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    decode program codec (encodeCommit registry codec action step) =
      some
        { caller := registry.address who
          player := who
          node := action.node
          value := { ty := step.guard.ty, value := step.value } } := by
  have hrow : program.graph.nodeRow action.node = step.row := by
    have hget :
        program.graph.nodes[(action.node : Nat)]? = some step.row :=
      step.row_get
    rw [program.graph.nodes_get?_nodeRow action.node] at hget
    exact Option.some.inj hget
  have hsem :
      (program.graph.nodeRow action.node).sem = .commit who step.guard := by
    rw [hrow]
    exact step.sem_eq
  simp [decode, encodeCommit, action.node.isLt, hsem,
    codec.decode_encode_value]

omit [DecidableEq Address] in
/-- The decoded call of a valid commit erases to exactly the original logical
request. -/
theorem request_of_decode_encodeCommit
    (registry : PlayerRegistry Player Address)
    (codec : StorageCodec L) {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    ∃ call : PlayerCall Player Address L,
      decode program codec (encodeCommit registry codec action step) =
        some call ∧
      call.request = Request.encode (.commit who action step) := by
  let call : PlayerCall Player Address L :=
    { caller := registry.address who
      player := who
      node := action.node
      value := { ty := step.guard.ty, value := step.value } }
  refine ⟨call, decode_encodeCommit registry codec action step, ?_⟩
  have hvalue :=
    TypedValue.eq_mk_of_as?_eq_some
      action.value step.guard.ty step.value step.value_ok
  simp [call, PlayerCall.request, Request.encode, ← hvalue]

/-- Decode, authenticate, and validate word-level calldata against canonical
raw storage. -/
def acceptsStore (registry : PlayerRegistry Player Address)
    (codec : StorageCodec L) (store : RawStore codec)
    (calldata : PlayerCalldata Player Address codec.Word) : Bool :=
  match decode program codec calldata with
  | none => false
  | some call =>
      PlayerCall.acceptsStore (program := program) registry codec store call

/-- Encoding a valid semantic commit produces accepted word-level calldata on
the encoded reachable state. -/
theorem acceptsStore_encodeState_encodeCommit
    (registry : PlayerRegistry Player Address)
    (codec : StorageCodec L) {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    acceptsStore (program := program) registry codec
        (RawStore.encodeState codec state)
        (encodeCommit registry codec action step) = true := by
  have hvalue :=
    TypedValue.eq_mk_of_as?_eq_some
      action.value step.guard.ty step.value step.value_ok
  unfold acceptsStore
  rw [decode_encodeCommit]
  dsimp only
  unfold PlayerCall.acceptsStore
  rw [Request.acceptsStore_encodeState]
  have hvalid :=
    Request.accepts_encode (AvailableEvent.commit who action step)
  simpa [PlayerCall.authenticated, PlayerCall.request, Request.encode,
    ← hvalue]
    using hvalid

end PlayerCalldata

end Vegas.Machine.Contract
