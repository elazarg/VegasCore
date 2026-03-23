import Vegas.MAID.Compile

/-!
# Compiled Perfect Recall

A well-formed Vegas program (`WF p`) compiles to a MAID struct with perfect
recall (`Struct.PerfectRecall`).

The two perfect recall conditions follow from the structure of well-formed
Vegas programs:

1. **Temporal ordering**: Decision nodes of the same player are linearly ordered
   by program position. This follows from the sequential structure of
   `VegasCore`: all commit sites appear along a single path, so same-player
   decision nodes are always comparable by ancestry in the compiled DAG.

2. **Full observation**: If decision node d₁ is an ancestor of d₂ (same player),
   then d₁ ∈ obsParents d₂ and obsParents d₁ ⊆ obsParents d₂. This follows
   from `ViewScoped` (guards respect visibility) combined with `RevealComplete`
   (all secrets are eventually revealed), which together ensure that at each
   decision point, the player can observe all prior same-player decisions and
   their observation contexts.
-/

namespace Vegas

open MAID

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A well-formed Vegas program compiles to a MAID struct with perfect recall. -/
theorem compiledStruct_perfectRecall
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hl : Legal p) (ha : DistinctActs p) (hd : NormalizedDists p)
    (hwf : WF p) :
    let _ : Fintype P := B.fintypePlayer
    (MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty).toStruct.PerfectRecall := by
  sorry

end Vegas
