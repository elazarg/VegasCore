/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionCompletion
import Interaction.SealedCandidateResolution

/-! # Normal completion in the candidate commitment host

The candidate validator rejects further application messages once every rule
has completed without timeout. The shared host persistence theorem then applies
under arbitrary later preparation, message delivery, inclusion, and clock calls.
-/

namespace Interaction.SealedResolution

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- Candidate admission cannot change a normally completed public result,
regardless of the catalog or the payload's claimed opening. -/
theorem candidateHandle_eq_none_of_complete_clear
    (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value))
    (hcomplete : runtime.complete state.visible = true) (hclear : state.visible.timeouts = [])
    (message : Message Principal (SealedProgram.Payload Principal Value)) :
    runtime.candidateHandle state message = none := by
  have hvalidator : runtime.program.candidateMessage? state.service state.visible.events message =
      none := by
    rcases message with ⟨id, payload⟩
    cases payload with
    | malformed | cleartext => rfl
    | commitment node handle | opening node handle claimed =>
        cases hrule : runtime.program.rules[node]? with
        | none => simp [SealedProgram.candidateMessage?, hrule]
        | some rule =>
            have hindex : node < runtime.program.rules.length :=
              (List.getElem?_eq_some_iff.mp hrule).1
            have hdone : SealedProgram.done state.visible.events node = true := by
              simpa [PublicState.completed, hclear] using
                runtime.complete_node state.visible node hcomplete hindex
            cases hkind : rule.kind <;>
              simp [SealedProgram.candidateMessage?, hrule, hkind, hdone]
  unfold candidateHandle
  split
  · rfl
  · simp only [hclear, SealedProgram.discharge_nil, hvalidator, Option.bind_eq_bind,
      Option.bind_none]

end Interaction.SealedResolution
