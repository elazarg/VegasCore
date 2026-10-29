/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.DisclosureBehavioral
import Vegas.Source.CommitmentInterface

/-! # Support of authentic source choices

Bindings retain their admission interface. At a reveal, the supported choices
include every Boolean choice fixed by suppressing only unopenable bindings.
Authentic attempts remain in the menu even when their deferred guards reject.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Support every admitted binding and every authentic disclosure choice. -/
def BehavioralPolicy.SupportsAuthenticChoices {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → CommitmentInterface program →
    BehavioralPolicy who program → Prop
  | _, _, .ret _, _, _ => True
  | _, _, .sample _ _ _ next, admission, policy =>
      SupportsAuthenticChoices next admission policy
  | _, _, .commit _ owner _ _ next, admission, policy =>
      (∀ (own : owner = who) view active choice, (admission none).Admits choice →
        choice ∈ (policy.1 own view active).support) ∧
      SupportsAuthenticChoices next (fun site => admission (some site)) policy.2
  | _, _, .reveal _ owner _ _ selected _ next, admission, policy =>
      (∀ (own : owner = who) view active choice,
        (choice && ((view.observation.cells.get (own ▸ selected)).getD .failure).isSuccess) =
            choice → choice ∈ (policy.1 own view active).support) ∧
      SupportsAuthenticChoices next admission policy.2

end Vegas.SourceProgram
