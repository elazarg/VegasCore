# Autoproof Empirical Results

## 2026-03-22: Vegas Kuhn Theorem Infrastructure

**Task**: Implement 5 deliverables for Vegas Kuhn Theorem via MAID

**Tool**: Claude Opus 4.6 (no ChatGPT used)

**Results**:

| Deliverable | File | Status | Sorry count |
|---|---|---|---|
| PMF behavioral layer | `Vegas/StrategicPMF.lean` | **Fully proved** | 0 |
| Compiled perfect recall | `Vegas/MAID/PerfectRecall.lean` | Stub | 1 |
| Policy reflection + pure compilation | `Vegas/MAID/Reflection.lean` | Partial (def done, proofs sorry) | 3 |
| Vegas Kuhn theorem | `Vegas/MAID/Kuhn.lean` | Stub with structure | 2 |
| Module imports | `Vegas/MAID.lean` | Done | 0 |

**Total new lines**: ~550 Lean
**Total sorry**: 6 (across 3 files)
**Full build**: `lake build Vegas` passes (3179 jobs)

### What worked well
- Mirroring existing FDist infrastructure for PMF was fully mechanical
- The key bridge lemmas (`FDist.toPMF_bind`, `FDist.toPMF_pure`) were already in the codebase
- Inductive proofs on VegasCore (for agreement theorems) followed the existing patterns exactly
- `compilePureProfile` definition was straightforward once the pattern from `compiledPolicy` was understood

### What blocked
- **`reflectPolicy`**: Fundamental information mismatch — MAID obsParents include hidden variables but Vegas `ProgramBehavioralKernelPMF` only sees `ViewEnv` (visible variables). Needs either compiler change (use viewDeps for obsParents) or an additional theorem showing independence from hidden vars.
- **`compiledStruct_perfectRecall`**: Requires deep structural invariant about the compiler — tracking that ctxDeps grows monotonically and commit VarIds end up in subsequent ctxDeps.
- **`compilePureProfile_eq_pureToPolicy`**: Requires showing pureProfileOperational produces Dirac FDists at each decision node, which traces through compiler's kernel capture.

### Time breakdown
- Reading/understanding codebase: ~30%
- Writing StrategicPMF.lean: ~25%
- Writing stubs + compilePureProfile def: ~20%
- Attempting sorry'd proofs + analysis: ~25%
