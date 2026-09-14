/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionPolicy
import Interaction.SealedCandidateResolution

/-! # Source policies hosted by the candidate commitment service

The generated rules and honest policy code are unchanged. The candidate host
has a different private application-state type, but the player's command,
observation, and history components are identical. The policy translation
below only reconstructs these records at the registered host's carrier type;
it neither queries the candidate catalog nor erases observable input.

Arbitrary replacements are policies of the candidate host, with its additional
candidate-selection behavior. Their strategic simulation does not follow from
this lossless retyping of the honest policy.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- The original sample-once sealed policy running in the candidate host.
All visible components are retained; no private host state is an input. -/
def compileCandidatePolicy (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player)
    (policy : SourceBehavioralPolicy source.core.prog who) :
    (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy :=
  fun history view => compilation.compileResolvingPolicy nullValue window who policy
    (history.map fun entry =>
      ⟨⟨entry.beforeView.messages, entry.beforeView.application, entry.beforeView.receipts⟩,
        entry.command⟩)
    ⟨view.messages, view.application, view.receipts⟩

/-- Changing commitment service does not introduce a cleartext commitment
optimization into the generated honest policies. -/
theorem compileCandidatePolicy_no_cleartext (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player)
    (policy : SourceBehavioralPolicy source.core.prog who)
    (history : List
      (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry)
    (view : (compilation.supported.resolvingRuntime nullValue window).candidateApplication.View)
    (node : Nat) (value : L.Val ty) :
    .submit (.cleartext node value) ∉
      (compilation.compileCandidatePolicy nullValue window who policy history view).support :=
  compilation.supported.resolvingPolicy_no_cleartext nullValue window who _ _ _ node value

end Vegas.SealedCompilation
