/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolution
import Interaction.SealedMemory

/-! # Local command memory through deadline resolution

The event projection forgets timing metadata, not wire observations or private
commands. The same registration encoding therefore reads the same first value
from either history. This projection does not assert equivalence of the two
runtime executions after a timeout.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

def eventView (runtime : SealedResolution Principal Value)
    (view : runtime.messageApplication.View) :
    (runtime.program.messageApplication (Value := Value)).View :=
  ⟨view.messages, view.application.events, view.receipts⟩

def eventHistory (runtime : SealedResolution Principal Value)
    (history : List runtime.messageApplication.PlayerEntry) :
    List (runtime.program.messageApplication (Value := Value)).PlayerEntry :=
  history.map fun entry => ⟨runtime.eventView entry.beforeView, entry.command⟩

theorem eventHistory_cache (runtime : SealedResolution Principal Value)
    (encoding : ChoiceEncoding Value runtime.messageApplication.PlayerCommand)
    (history : List runtime.messageApplication.PlayerEntry) :
    encoding.cachedValue (runtime.program.messageApplication (Value := Value))
        (runtime.eventHistory history) =
      encoding.cachedValue runtime.messageApplication history := by
  induction history with
  | nil => rfl
  | cons entry rest ih =>
      simp only [eventHistory, List.map_cons, ChoiceEncoding.cachedValue]
      cases encoding.decode entry.command
      · exact ih
      · rfl

end Interaction.SealedResolution
