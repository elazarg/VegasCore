/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.DisclosureBehavioral
import Vegas.Source.ProtocolBehavioralPolicy

/-! # Support of effective source choices

A policy completed at unreachable views can support every admitted source
choice. The existing private-intention normalization then supports exactly
the effective representatives needed by the native service. Failed guarded
intentions may collapse to withholding; no full-support claim in the original
unquotiented disclosure menu is made for the normalized policy.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Bindings retain admitted values. A disclosure needs support only for
the Boolean choices fixed by the actual deferred guard normalization. -/
def BehavioralPolicy.SupportsEffectiveChoices {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → CommitmentInterface program →
    Registry Γ → Revelations Γ → BehavioralPolicy who program → Prop
  | _, _, .ret _, _, _, _, _ => True
  | _, _, .sample _ _ _ next, admission, registry, revelations, policy =>
      SupportsEffectiveChoices next admission registry.weaken revelations.weaken policy
  | _, _, .commit (payload := payload) name owner _ guard next,
      admission, registry, revelations, policy =>
      (∀ (own : owner = who) view choice, (admission none).Admits choice →
        choice ∈ (policy.1 own view).support) ∧
      SupportsEffectiveChoices next (fun site => admission (some site))
        (({ owner := owner, subject := name, payload := payload, source := .here,
            guard := guard.weaken } : Obligation _) :: registry.weaken)
        revelations.weaken policy.2
  | _, _, .reveal published owner _ _ selected _ next,
      admission, registry, revelations, policy =>
      (∀ (own : owner = who) view choice,
        effectiveDisclosureView published (own ▸ selected) registry revelations view.1 choice =
            choice → choice ∈ (policy.1 own view).support) ∧
      SupportsEffectiveChoices next admission registry.weaken
        (revelations.reveal selected) policy.2

end Vegas.SourceProgram
