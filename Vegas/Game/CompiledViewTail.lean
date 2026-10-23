/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.ProtocolViewSuffix
import Vegas.Game.ServiceRevealTail

/-! # Canonical source observation maps after disclosure phases -/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The exact disclosure telescope retains its source observation embedding,
whole decoder identity and original named-action interpretation. -/
def ProtocolViewSuffix.revealTailMany :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
      (lift : ProtocolState program → ProtocolState setup.program),
      ProtocolViewSuffix setup.program program refs embedding lift →
      ProtocolViewSuffix setup.program (Vegas.revealTail count program prefixed).tail
        (revealTailRefs setup count program prefixed refs embedding)
        (revealTailEmbedding setup count program prefixed embedding)
        (fun point => lift ((Vegas.revealTail count program prefixed).lift point)) := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed refs embedding lift aligned; exact aligned
  | succ count ih =>
      intro Γ names program prefixed refs embedding lift aligned
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal published owner name fresh selected unresolved next =>
          exact ih next prefixed _ _ (fun point => lift (Sum.inr point))
            (ProtocolViewSuffix.revealTail setup.program fresh selected unresolved next refs
              embedding lift aligned)

end Vegas
