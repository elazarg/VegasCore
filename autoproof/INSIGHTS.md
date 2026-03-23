# Autoproof Insights

## MAID obsParents information mismatch (2026-03-22)

**Problem**: The Vegas-to-MAID compiler uses `ctxDeps Γ` (ALL context variable
dependencies) as obsParents for decision nodes. But the Vegas behavioral kernel
(`ProgramBehavioralKernelPMF`) is indexed by `ViewEnv` (visible variables only).
This makes `reflectPolicy` (MAID Policy → Vegas behavioral profile) impossible
to define without either:

1. Changing the compiler to use `viewDeps who Γ` for decision node obsParents
2. Using a broader kernel type (full erased env instead of ViewEnv)
3. Proving an independence lemma (MAID policy is constant on hidden vars)

**Recommendation**: Option 1 is cleanest — change the compiler. The PerfectRecall
conditions still hold with viewDeps (verified informally). The MAID semantic
correctness proofs might need minor updates but the key bridge
(`maid_map_extract_eq_outcomeDist`) should be unaffected since it works with
the full operational profile, not the obsParents.

## Compiler invariant complexity (2026-03-22)

**Problem**: Proving `compiledStruct_perfectRecall` requires establishing
monotonicity invariants about the compiler state:
- `ctxDeps` grows as the context grows
- `lookupDeps` for existing variables is stable across `addVar`/`addNode`
- Commit VarIds appear in subsequent `ctxDeps`

**Insight**: These properties follow from the append-only structure of the `vars`
list and the first-match semantics of `lookupDepsAux`. But the formal proof
requires an induction on `ofProg` with a compound invariant tracking all these
properties simultaneously.

**Recommendation**: Define a `CompileInvariant` structure bundling the key
properties, then prove it's preserved by each step of `ofProg`. This is
boilerplate-heavy but structurally straightforward.

## FDist → PMF bridge is clean (2026-03-22)

**Insight**: The existing `FDist.toPMF_bind` and `FDist.toPMF_pure` lemmas make
the PMF behavioral layer proofs almost mechanical. The entire `StrategicPMF.lean`
file (280 lines, 0 sorry) was written in one pass by mirroring `Strategic.lean`
and using these bridge lemmas at sample/commit nodes.

**Pattern**: For any `outcomeDist*` function that uses `FDist.bind`/`FDist.pure`,
the PMF analogue uses `PMF.bind`/`PMF.pure`, and the agreement proof chains
`toPMF_bind` + `toPMF_pure` at each recursive step.

## compilePureProfile via support extraction (2026-03-22)

**Insight**: `compilePureProfile` can be defined without reconstructing the
Vegas-to-MAID mapping explicitly. Instead, evaluate the kernel with the
`pureProfileOperational` and pick a value from the FDist support. Since pure
profiles produce Dirac distributions, the support has exactly one element.

**Pattern**: `if h : fdist.support.Nonempty then h.choose else default`
This is a useful generic pattern for extracting deterministic values from
distributions that are known to be Dirac (by separate proof).
