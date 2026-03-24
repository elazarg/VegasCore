import Vegas.MAID.DefsV

/-!
# Perfect Recall for VegasMAID

**Status: sorry'd interface — proof to be filled in later.**

The compiled VegasMAID has perfect recall, following directly from the
factored-observation structure (`obsParents = parents`).
-/

namespace Vegas

open MAID

variable {Player : Type} [DecidableEq Player] {L : IExpr} {B : MAIDBackend Player L}

/-- The compiled VegasMAID structure has perfect recall. -/
theorem compiledStruct_perfectRecallV
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False) :
    (compiledStruct B p env hl hd hfresh hpub).PerfectRecall (fp := B.fintypePlayer) := by
  sorry

end Vegas
