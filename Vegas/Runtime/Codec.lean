/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Basic

/-!
# Runtime value codecs

Event graphs store typed semantic values. Concrete runtimes usually store and
exchange untyped wire values. A backend supplies a `ValueCodec` to relate the
two without making the language or EventGraph IR runtime-specific.
-/

namespace Vegas

namespace Runtime

open EventGraph

variable {L : IExpr}

/-- A runtime-independent codec for dynamically typed EventGraph values.

`decode_encode` is the round-trip needed for compiling abstract graph values
to wire values. `encode_decode` is the soundness/canonicality direction needed
when a runtime wire value is decoded back into the graph semantics. -/
structure ValueCodec (L : IExpr) where
  Wire : Type
  encode : TypedValue L → Wire
  decode : Wire → Option (TypedValue L)
  decode_encode : ∀ value, decode (encode value) = some value
  encode_decode :
    ∀ {wire value}, decode wire = some value → encode value = wire

namespace ValueCodec

/-- Decode a wire value at a requested EventGraph type. -/
noncomputable def decodeAs? (codec : ValueCodec L)
    (wire : codec.Wire) (ty : L.Ty) : Option (L.Val ty) :=
  codec.decode wire >>= fun value => value.as? ty

@[simp] theorem decodeAs?_encode
    (codec : ValueCodec L) (value : TypedValue L) (ty : L.Ty) :
    codec.decodeAs? (codec.encode value) ty = value.as? ty := by
  simp [decodeAs?, codec.decode_encode]

/-- Runtime storage over encoded values. -/
abbrev WireStore (codec : ValueCodec L) : Type :=
  Nat → Option codec.Wire

/-- Encode an abstract EventGraph store into a wire-value store. -/
def encodeStore (codec : ValueCodec L) (store : Store L) :
    codec.WireStore :=
  fun field => store field |>.map codec.encode

/-- Decode a wire-value store into an abstract EventGraph store. -/
noncomputable def decodeStore (codec : ValueCodec L)
    (store : codec.WireStore) : Store L :=
  fun field => store field >>= codec.decode

@[simp] theorem decodeStore_encodeStore
    (codec : ValueCodec L) (store : Store L) :
    codec.decodeStore (codec.encodeStore store) = store := by
  funext field
  unfold decodeStore encodeStore
  cases store field with
  | none => rfl
  | some value =>
      simp [codec.decode_encode value]

theorem getAs_decodeStore_encodeStore
    (codec : ValueCodec L) (store : Store L)
    (field : Nat) (ty : L.Ty) :
    Store.getAs (codec.decodeStore (codec.encodeStore store)) field ty =
      Store.getAs store field ty := by
  rw [codec.decodeStore_encodeStore store]

theorem encode_decode_of_decode
    (codec : ValueCodec L) {wire : codec.Wire}
    {typed : TypedValue L}
    (hdecode : codec.decode wire = some typed) :
    codec.encode typed = wire :=
  codec.encode_decode hdecode

end ValueCodec

end Runtime

end Vegas
