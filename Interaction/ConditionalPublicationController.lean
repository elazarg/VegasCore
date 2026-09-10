/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.ConditionalPublicationRouting
import Interaction.BindingPublication

/-! # Voluntary controller encodings for conditional publication

Opaque and public-default bindings have distinct canonical packets.  Each
encoding remains strict: it decodes only the form it emits, so the
`ChoiceEncoding.decode_sound` contract is not weakened.
-/

namespace Interaction.ConditionalPublication

open MessageApplication

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- Voluntary choices for a public default use cleartext publication. -/
def defaultChoiceEncoding :
    ChoiceEncoding (Option Value) (Payload Principal Value) where
  encode
    | none => .decline
    | some value => .cleartext value
  decode
    | .decline => some none
    | .cleartext value => some (some value)
    | .opening _ _ | .expire | .malformed => none
  decode_encode value := by cases value <;> rfl
  decode_sound payload value hdecode := by
    cases payload with
    | decline => cases Option.some.inj hdecode; rfl
    | cleartext claimed => cases Option.some.inj hdecode; rfl
    | opening handle claimed | expire | malformed => cases hdecode

@[simp] theorem defaultChoiceEncoding_decode_expire
    : (defaultChoiceEncoding (Principal := Principal) (Value := Value)).decode .expire = none := rfl

/-- Route the strict public-default encoding to this publication endpoint. -/
def addressedDefaultChoiceEncoding (site : ConditionalPublication Principal) :
    ChoiceEncoding (Option Value) (Nat × Payload Principal Value) :=
  defaultChoiceEncoding.atEndpoint site.publicationNode

end Interaction.ConditionalPublication
