/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRevealTail
import Vegas.Compile.CompiledReadoutSuffix

/-! # Exact compiler and terminal references after source-ordered disclosures -/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The node-table suffix follows the existing disclosure telescope, without
requiring an honest policy or matching the dynamic source guard registry. -/
theorem CompiledSuffix.revealTailMany :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (revelations : Revelations Γ) (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (before : ContextRefsBefore refs embedding) (offset : Nat),
    CompiledSuffix setup.program program refs revelations registry embedding before offset →
    CompiledSuffix setup.program (Vegas.revealTail count program prefixed).tail
      (revealTailRefs setup count program prefixed refs embedding)
      (revealTailRevelations count program prefixed revelations)
      (revealTailRegistry count program prefixed registry)
      (revealTailEmbedding setup count program prefixed embedding)
      (revealTailRefsBefore count program prefixed refs embedding before) (offset + count) := by
  intro count
  induction count with
  | zero =>
      intro Γ names program prefixed refs revelations registry embedding before offset aligned
      change CompiledSuffix setup.program program refs revelations registry embedding before
        (offset + 0)
      simpa only [Nat.add_zero] using aligned
  | succ count ih =>
      intro Γ names program prefixed refs revelations registry embedding before offset aligned
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal published owner name fresh selected unresolved next =>
          have step := aligned.revealTail setup.program fresh selected unresolved next refs
            revelations registry embedding before offset
          have later := ih next prefixed _ _ _ _ _ (offset + 1) step
          rw [show offset + (count + 1) = offset + 1 + count by omega]
          exact later

/-- The same traversal retains the actual whole-program terminal references,
including when some disclosed values failed. -/
theorem CompiledReadoutSuffix.revealTailMany :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program),
    CompiledReadoutSuffix setup.program program refs embedding →
    CompiledReadoutSuffix setup.program (Vegas.revealTail count program prefixed).tail
      (revealTailRefs setup count program prefixed refs embedding)
      (revealTailEmbedding setup count program prefixed embedding) := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed refs embedding aligned; exact aligned
  | succ count ih =>
      intro Γ names program prefixed refs embedding aligned
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal published owner name fresh selected unresolved next =>
          exact ih next prefixed _ _
            (aligned.revealTail setup.program fresh selected unresolved next refs embedding)

/-- Fresh publication names preserve distinct source names throughout the
existing disclosure telescope. -/
theorem RevealPrefix.names_nodup :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count),
    (Γ.map Prod.fst).Nodup →
      ((Vegas.revealTail count program prefixed).context.map Prod.fst).Nodup := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed unique; exact unique
  | succ count ih =>
      intro Γ names program prefixed unique
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal published owner name fresh selected unresolved next =>
          exact ih next prefixed (List.nodup_cons.mpr ⟨fresh, unique⟩)

end Vegas
