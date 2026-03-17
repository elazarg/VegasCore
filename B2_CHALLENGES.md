# B2: Vegas → MAID Distribution Equality — Challenges Document

## 1. What we're proving

We have a compiler that translates programs in a typed game calculus ("Vegas")
into Multi-Agent Influence Diagrams (MAIDs). We want to prove that the compiled
MAID's joint distribution over outcomes equals the denotational semantics of the
source program. This is a **compiler correctness** theorem, stated as an equality
of probability distributions.

### Source language (Vegas)

Vegas programs (`Prog Player L Γ`) are typed, monadic programs over a
visibility-tagged context `Γ`. The constructors are:

```
| ret (u : PayoffExpr)           -- return payoffs
| letExpr x e k                  -- deterministic binding
| sample x τ m D k               -- draw from distribution D, bind result
| commit x who acts R k          -- player `who` chooses from `acts`
| reveal y who x hx k            -- reveal a hidden variable
```

The denotational semantics is `outcomeDist σ p env : FDist Outcome`, a finitely-
supported distribution over outcomes weighted in `ℚ≥0`. It is defined by
structural recursion on `Prog`, threading a profile `σ` (mapping each player's
decision sites to distributions over actions) and an environment `env`.

### Target (MAID)

A MAID is a DAG of nodes — chance, decision, utility — with conditional
probability distributions. The joint distribution over total assignments
`a : TAssign S` (a value at every node) is defined by Bayesian network
factorization:

```
assignProb S sem pol a = ∏ nd, (nodeDist S sem pol nd a) (a nd)
```

This is wrapped as `evalAssignDist : PMF (TAssign S)`, which is manifestly
independent of any topological ordering.

An equivalent fold-based evaluation (`evalFold`) processes nodes one at a time
along a topological order:

```
evalStep acc nd = acc.bind (fun a => (nodeDist nd a).bind (fun v => pure (update a nd v)))
evalFold = order.foldl evalStep (pure defaultAssign)
```

The theorem `evalAssignDist_eq_evalFold` connects the two.

### The compiler

`MAIDCompileState.ofProg B p hl ha hd ρ st` walks `p`, emitting MAID nodes
with sequential IDs `0, 1, 2, ...`. Each constructor maps to:

| Vegas construct | MAID node(s) | Count |
|:----------------|:-------------|:------|
| `sample`        | 1 chance     | 1     |
| `commit`        | 1 decision   | 1     |
| `ret`           | utility nodes| |Player| |
| `letExpr`       | (none)       | 0     |
| `reveal`        | (none)       | 0     |

The compiler threads an environment-reconstruction function
`ρ : RawNodeEnv L → VisEnv L Γ` that recovers the full Vegas environment from
the MAID's partial assignment at each program point.

### The theorem

```lean
∃ (pol : Policy S) (extract : TAssign S → Outcome),
  PMF.map extract (evalAssignDist S sem pol) =
    (outcomeDist σ p env).toPMF h
```

That is: there exists a MAID policy (derived from the Vegas profile `σ`) and an
outcome-extraction function such that the MAID's marginal over outcomes equals
the Vegas semantics, both viewed as `PMF Outcome`.

## 2. Proof strategy: fold-based induction

We reduce `evalAssignDist` to `evalFold` along the natural topological order
`[0, 1, ..., n−1]` (valid because the compiler assigns IDs in order, and
parent IDs are always smaller). The fold's step-by-step structure then mirrors
the structural recursion of `outcomeDist`. We prove an inductive invariant:
after compiling sub-program `p`, the fold over the newly emitted nodes
transforms the accumulator in a way that corresponds to `outcomeDist σ p`.

**Why fold-based instead of product-based:** The product formula
`∏ nd, P(xₙ|parents(xₙ))` is the canonical Bayesian network definition and
doesn't depend on order. Proving Vegas has this factorization directly is
conceptually cleaner but requires reasoning about the sum-product structure
(summing over all assignments that yield a given outcome, showing the product
factors correctly). The fold-based approach avoids this: since the fold processes
nodes in exactly the order the compiler emits them, each step corresponds to
exactly one `FDist.bind` or identity operation in `outcomeDist`. The induction is
mechanical, at the cost of going through the fold ↔ product equivalence.

## 3. The hard parts

### 3.1. Weight system mismatch (`ℚ≥0` vs `ℝ≥0∞`)

Vegas uses `FDist α = α →₀ ℚ≥0` (finitely supported, computable). MAIDs use
`PMF α` (Mathlib's probability mass function, weights in `ℝ≥0∞`, sums via
`tsum`). The bridge is `FDist.toPMF : FDist α → (totalWeight = 1) → PMF α`,
which casts each `ℚ≥0` weight to `ℝ≥0∞`.

**The challenge:** We need `toPMF` to be a monad homomorphism — commuting with
`pure`, `bind`, and `map`. The `pure` and `map` cases are proved (in
`OutcomeKernelBridge.lean`). **`toPMF_bind` is the hard one:**

```lean
theorem toPMF_bind (d : FDist α) (f : α → FDist β)
    (hd : d.totalWeight = 1)
    (hf : ∀ a ∈ d.support, (f a).totalWeight = 1) :
    (d.bind f).toPMF hbind = (d.toPMF hd).bind (fun a => ...)
```

Pointwise, both sides compute `∑ₐ d(a) * f(a)(b)`, just in different semirings.
The proof requires showing `NNRat.toNNReal` (our custom `ℚ≥0 → ℝ≥0`) commutes
with finite sums and products (proved), then lifting through `ENNReal.coe` and
relating the finitely-supported sum to Mathlib's `tsum`.

The subtlety is the **support mismatch**: `FDist.bind` sums over `d.support`,
but `PMF.bind` sums over *all* of `α` (via `tsum`). Outside `d.support`,
`d(a) = 0` so the terms vanish, but the RHS needs `f a` for *every* `a` (as a
`PMF`), not just those in support. This forces a guard:

```
fun a => if a ∈ d.support then (f a).toPMF ... else PMF.pure default
```

or a proof that the tsum collapses to the finite sum. Either way, the `tsum`
↔ `Finset.sum` conversion requires careful bookkeeping.

### 3.2. Environment reconstruction (`ρ` faithfulness)

The compiler maintains `ρ : RawNodeEnv L → VisEnv L Γ`, which reconstructs the
Vegas environment from a MAID node assignment. At each binding site, `ρ` is
extended: for `sample`, it reads the value from the MAID node via
`readVal raw τ id`; for `letExpr`, it evaluates the expression in the
already-reconstructed env.

We need to prove that `ρ` is **faithful**: when applied to `rawEnvOfAssign a`
(the `RawNodeEnv` extracted from a total MAID assignment `a`), it produces the
same env values that the Vegas semantics would compute. This requires:

1. **`readVal` roundtrip**: `readVal (rawEnvOfAssign a) τ id` recovers the
   original typed value. This goes through `taggedOfDesc → readVal`, which
   involves a dependent type cast (`if h : τ' = τ then h ▸ v else default`).
   The proof must show the type tags match, which holds because the compiler
   stores each value with its correct type — but this is a metatheoretic fact
   about the compiler's behavior that must be proved by induction on `Prog`.

2. **Monotonicity**: when the fold processes node `k`, the accumulator assigns
   `defaultAssign` to nodes `> k`. But `ρ` at program point `k` only reads
   nodes `< k` (by the compiler's dependency tracking). We need to show `ρ` is
   insensitive to nodes it doesn't read — i.e., `readVal` returns `default` for
   unassigned nodes, and this default is never actually used in the reconstruction.

### 3.3. Policy correspondence (`profileToPolicy` correctness)

The Vegas profile `σ.commit who x acts R view` returns `FDist (L.Val τ)` — a
distribution over *values*. The MAID policy must return
`PMF (Fin acts.length)` — a distribution over *action indices*. The bridge:

1. Evaluate `kernel σ raw` (the compiler-stored closure) to get the FDist.
2. Convert via `toPMF`.
3. Map values to indices via `List.idxOf v acts`.

**Challenges:**
- **Normalization**: `profileToPolicy` needs `(kernel σ raw).totalWeight = 1`
  for the `toPMF` conversion. This requires knowing that the Vegas profile is
  normalized at this decision site. But the MAID `Policy` type is a plain
  function `Infoset → PMF (Val nd)` with no way to thread normalization proofs.
  We must carry normalization as a separate hypothesis and discharge it at
  construction time.

- **Support containment**: The Vegas profile may assign positive weight to values
  not in `acts` (violating legality). The `List.idxOf` encoding maps such
  values to `acts.length` (out of range), which we clamp to 0. We need
  `AdmissibleProfile` to ensure this doesn't happen, or prove the clamped
  distribution still matches.

- **Infoset reconstruction**: The MAID policy receives
  `obs_cfg : Cfg S (obsParents nd)`, a partial assignment of observed parents.
  We must convert this to a `RawNodeEnv` and show it provides enough information
  for `kernel σ raw` to produce the same distribution as `σ.commit who x acts R view`.
  This requires showing the compiler's `obsParents` (view-dependency tracking)
  correctly captures exactly the variables visible to the player.

### 3.4. Utility node triviality

The compiler emits one utility node per player at the `ret` point, each with
domain size 1. The MAID `evalStep` for a utility node draws from
`PMF.pure ⟨0, ...⟩`, which is a no-op on the marginal outcome distribution.

**Challenge**: Proving this requires showing that `updateAssign a nd ⟨0, ...⟩ = a`
at utility nodes (since there's only one possible value). This is easy in
isolation but interacts with the fold invariant: we must show the utility-node
fold steps don't break the correspondence established by the
chance/decision steps.

### 3.5. The induction statement

The hardest part may be formulating the inductive invariant precisely enough
to go through. The invariant must relate:

- **Vegas side**: `outcomeDist σ p (ρ raw)`, where `ρ` and `raw` depend on the
  accumulator state.
- **MAID side**: a fold of `evalStep` over nodes
  `[st₀.nextId, ..., st₁.nextId − 1]`, transforming an accumulator
  `μ : PMF (TAssign S)`.

These live in different worlds: Vegas produces `FDist Outcome`, while the fold
produces `PMF (TAssign S)`. The bridge must relate them through the outcome
extraction function and `toPMF`.

A plausible invariant: for any accumulator `μ` satisfying
"nodes `< st₀.nextId` are correctly assigned",

```
PMF.map extract (fold [st₀..st₁] μ) =
  μ.bind (fun a => (outcomeDist σ p (ρ (rawOf a))).toPMF ...)
```

But this is not quite right because `extract` depends on the full compilation
state `st₁`, while `μ` only knows about nodes `< st₀.nextId`. The extraction
function must be compatible with the partial state, requiring an additional
coherence condition on the accumulator.

### 3.6. Dependent types and `Fin` arithmetic

The MAID API is heavily indexed by `n : Nat` (number of nodes) and uses
`Fin n` throughout. The compiler builds `n` dynamically via `nextId`. Relating
pre- and post-compilation states requires casting between `Fin st₀.nextId` and
`Fin st₁.nextId`, which is painful in Lean 4.

Specifically: the fold operates on `TAssign st₁.toStruct` (assignments over
all nodes in the final compiled MAID), but during induction we reason about
a prefix of nodes. We need embeddings `Fin st₀.nextId ↪ Fin st₁.nextId` and
proofs that `descAt` commutes with these embeddings. The compiler's
`MAIDCompileState` tracks `ids_range : nodes.map fst = List.range nextId`,
which helps, but threading this through the induction is mechanical and verbose.

## 4. Implementation plan

### Phase 1: Bridge lemmas (OutcomeKernelBridge.lean)
- [x] `toPMF_apply` — pointwise evaluation
- [x] `toPMF_pure` — pure homomorphism
- [x] `toPMF_map` — map homomorphism
- [ ] `toPMF_bind` — bind homomorphism (**key lemma, ~60 lines**)

### Phase 2: Structural scaffolding (MAIDCorrectness.lean)
- [x] `naturalOrder` — the canonical topological order
- [x] `compiledOutcome` — outcome extraction from total assignment
- [x] `rawEnvOfAssign` — total assignment → RawNodeEnv
- [x] `profileToPolicy` — Vegas Profile → MAID Policy (1 sorry: normalization)

### Phase 3: Environment reconstruction lemmas
- [ ] `readVal_roundtrip` — `readVal (rawEnvOfAssign a) τ id = decode (a id)`
- [ ] `rho_faithful` — `ρ (rawEnvOfAssign a) = expected Vegas env`
  (by induction on the compilation trace)
- [ ] `rawEnvOfCfg_mono` — extending the configuration doesn't affect reads at
  already-known nodes

### Phase 4: Step correspondence
- [ ] `evalStep_chance_eq` — chance node step ↔ FDist.bind (evalDistExpr D env)
- [ ] `evalStep_decision_eq` — decision node step ↔ FDist.bind (σ.commit ...)
- [ ] `evalStep_utility_noop` — utility node step doesn't change outcome marginal

### Phase 5: Fold induction
- [ ] `ofProg_fold_invariant` — core induction on `Prog` (~250 lines)
- [ ] `vegas_maid_dist_eq` — assemble via `evalAssignDist_eq_evalFold`

### Estimated total: ~700 lines, of which ~300 are sorry-able initially.

## 5. Current state

- `MAIDCorrectness.lean` compiles with 2 `sorry`s:
  1. `profileToPolicy` normalization (needs threading of `NormalizedOn` through the policy construction)
  2. `vegas_maid_dist_eq` (the main theorem)
- `OutcomeKernelBridge.lean` has `toPMF_apply`, `toPMF_pure`, `toPMF_map` proved.
- The natural topological order is constructed and verified.
- `compiledOutcome`, `rawEnvOfAssign`, and the `profileToPolicy` skeleton compile.

## 6. Risk assessment

| Component | Difficulty | Risk |
|-----------|-----------|------|
| `toPMF_bind` | Medium | Low — algebraic, both sides compute the same thing |
| `readVal_roundtrip` | Medium | Low — straightforward dependent-type unfolding |
| `rho_faithful` | High | Medium — requires careful induction on `ofProg` trace |
| `evalStep_*_eq` | High | Medium — must relate `nodeDist` (which pattern-matches on node kind) to the compiled CPD/kernel |
| Fold induction | Very high | High — invariant formulation is the crux; if wrong, the proof won't go through |
| `Fin` arithmetic | Medium | Low but tedious — may dominate line count |

The highest-risk item is getting the fold invariant statement right. If we
formulate it incorrectly, we'll discover this only deep into the induction.
A mitigation is to test the invariant on a concrete 2-node example before
attempting the general proof.
