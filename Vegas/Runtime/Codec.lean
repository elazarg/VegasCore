/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Basic

/-!
# Runtime value codecs

Event graphs store typed semantic values. Concrete runtimes usually store and
exchange untyped wire values. A backend supplies a `ValueCodec` encoding without
making the language or EventGraph IR runtime-specific.
-/

namespace Vegas

namespace Runtime

open EventGraph

variable {L : IExpr}

/-- A runtime-independent wire encoding for dynamically typed EventGraph
values. Refinement projects through the semantic configuration carried by a
runtime state, so adequacy requires only the concrete encoding operation. -/
structure ValueCodec (L : IExpr) where
  Wire : Type
  encode : TypedValue L → Wire

namespace ValueCodec

/-- Runtime storage over encoded values. -/
abbrev WireStore (codec : ValueCodec L) : Type :=
  Nat → Option codec.Wire

/-- Encode an abstract EventGraph store into a wire-value store. -/
def encodeStore (codec : ValueCodec L) (store : Store L) :
    codec.WireStore :=
  fun field => store field |>.map codec.encode

end ValueCodec

end Runtime

end Vegas
