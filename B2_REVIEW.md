Several parts are genuinely hard. Several others are self-inflicted.

## What is genuinely necessary

At least four obligations are real and do not go away:

1. **Decision semantics must match.**
   `commit` is the only source construct where the target policy matters, so some theorem connecting Vegas profiles to MAID decision CPDs is unavoidable.

2. **Visibility / observation must match.**
   The player in the MAID must condition on exactly the information available in Vegas. That is not bookkeeping; it is the core semantic obligation.

3. **Fresh-node dependency correctness must match.**
   Every emitted node must depend only on already-emitted parents, and with the right kernel.

4. **Outcome extraction must match.**
   However you encode utilities or returned payoffs, you need one theorem saying the target-side extracted outcome equals source-side payoff evaluation.

Those are the semantic heart of the theorem.

---

## What looks accidental

This is where most of the bulk seems to be coming from.

### 1. `FDist` vs `PMF`

This is the biggest accidental cost.

Your source semantics is finite, your compiled MAID is finite, your node domains are finite, your network is finite. But you are forcing the proof through:

* `ℚ≥0` on the source side
* `ℝ≥0∞` + `tsum` on the target side

That is mathematically harmless, but proof-theoretically expensive.

`toPMF_bind` is not “a hard semantic lemma”. It is a sign that the bridge is in the wrong place. You are paying a global price for a representation mismatch.

**Better move:** prove compiler correctness entirely in a finite distribution semantics on both sides, then convert to `PMF` once at the end.

Concretely, add an auxiliary target semantics:

```lean
evalAssignFDist : FDist (TAssign S)
```

or even better, a prefix version:

```lean
evalFoldFDist : FDist (CfgPrefix n)
```

Then prove:

1. Vegas correctness into `FDist`
2. target-internal theorem `evalAssignFDist.toPMF = evalAssignDist`

That isolates all `tsum`/`ENNReal` pain into a target-only lemma, instead of polluting the compiler proof.

This single change likely removes a large fraction of the difficulty.

---

### 2. Proving correctness against the **full assignment distribution**

This is also likely the wrong main theorem shape.

The source semantics is sequential and monadic. The compiler emits nodes sequentially. The fold semantics is sequential. So far, everything matches.

But then the proof is stated against the most global target object:

```lean
PMF (TAssign S)
```

over total assignments to all nodes, with defaults on not-yet-written entries.

That introduces:

* insensitivity to future nodes
* `rawEnvOfAssign` from total assignments
* monotonicity wrt unused nodes
* coherence of `extract` with partial information
* `defaultAssign` junk
* `Fin` casts between prefixes and the final network

Most of that is not semantic. It is an artifact of choosing the fully-closed BN semantics too early.

**Better move:** prove correctness for a **prefix semantics** first.

Instead of folding over total assignments, define assignments to the first `k` nodes only:

```lean
CfgPrefix k := (i : Fin k) → ValDesc ...
```

and a step

```lean
evalStepPrefix : FDist (CfgPrefix k) → Node k → FDist (CfgPrefix (k+1))
```

Now “future nodes are irrelevant” becomes definitional, not a lemma.
Your compiler already uses natural-number fresh IDs, so prefix semantics is the natural proof object.

Then prove equivalence between prefix semantics and the existing total-assignment semantics afterward.

This is probably the second biggest simplification available.

---

### 3. Reconstructing the whole Vegas environment from target assignments

This is probably too strong.

You likely do **not** need:

```lean
ρ (rawEnvOfAssign a) = expected Vegas env
```

as a full extensional equality.

What you really need is usually one of these weaker facts:

* agreement on the variables free in the remaining suffix of the program
* agreement on visible variables for a specific player
* agreement on the dependencies of an expression / kernel / payoff

That is a major difference.

Instead of “faithfulness of full reconstruction”, define a logical relation like:

```lean
EnvAgreeOn deps raw env
```

meaning: for every variable actually read by the current continuation, `ρ raw` and `env` agree.

Then each compiler step preserves the relevant agreement set.

This avoids proving that reconstruction ignores irrelevant nodes globally. You only prove that the next thing you evaluate reads what you think it reads.

That is a much better fit for Lean.

---

### 4. `idxOf` + clamp in `profileToPolicy`

This is not just awkward; it is the wrong encoding.

If the decision node represents a choice among `acts`, the target value type should be a finite type *equivalent* to the legal actions, not a lossy encoding via `idxOf` with illegal fallbacks.

The clamp-to-0 trick makes the semantics tolerate illegal profiles operationally, and then you need a side theorem saying it never matters. That is backwards.

**Better move:** compile decision values as something like

```lean
{ v // v ∈ acts }
```

or an explicit finite enumeration with an `Equiv` to the legal action set.

Then the policy bridge is transport along an equivalence, not “map values to indices and pray legality holds”.

This removes the ugliest part of policy correctness.

If you absolutely need `Fin acts.length`, then at least establish a clean bijection:

```lean
Fin acts.length ≃ LegalActs acts
```

and compile through that, not through `List.idxOf`.

---

### 5. Utility singleton nodes in the main induction

These feel administrative, not central.

If your theorem is only about the outcome marginal, singleton utility nodes should not be interleaved with the core induction unless the MAID API forces it.

Two better options:

* prove the core theorem for chance/decision nodes only, with `compiledOutcome` computed directly from the reconstructed environment;
* or prove once and for all that appending deterministic singleton utility nodes preserves the relevant marginal.

Either way, utility nodes should be a small wrapper theorem, not part of the semantic spine.

---

## So is the overall complexity necessary?

Not in the current amount.

My estimate:

* The **semantic difficulty** is real.
* The **proof volume** is inflated by representation choices.

The core theorem should still be substantial. But the current plan is carrying at least three avoidable burdens:

1. finite distribution semantics vs `PMF`
2. total assignments instead of prefix assignments
3. full environment reconstruction instead of agreement on needed reads

Those three are doing most of the damage.

---

## A better proof architecture

I would seriously consider this refactor.

### Layer 1: finite target semantics

Define a target semantics in the same finite world as Vegas.

Either:

```lean
evalFoldFDist : FDist (CfgPrefix n)
```

or a slightly more semantic kernel form:

```lean
compiledKernel : RawEnv → FDist (RawEnv × Outcome)
```

The second is often even better.

### Layer 2: local compiler correctness

Prove by structural recursion on `Prog` a theorem that directly mirrors the source monad.

Something like:

```lean
compile_sound :
  map outcome (compiledKernel σ p raw) =
  outcomeDist σ p (ρ raw)
```

or, if using prefix assignments,

```lean
fold_segment_sound :
  foldSegment ... μ
    =
  μ.bind (fun a => lift ((outcomeDist σ p (ρ (rawOf a))).toFDist ...))
```

The key is: the theorem should talk about **only the freshly emitted segment**, not the final whole network.

### Layer 3: target-internal equivalence

Separately prove:

* prefix semantics = total-assignment fold semantics
* fold semantics = product semantics
* finite target semantics = `PMF` target semantics

These are target metatheory, not compiler correctness.

That decomposition is much cleaner.

---

## About the fold-vs-product choice

Your instinct is mostly right.

For compiler correctness, the fold proof is the natural one, because compilation order mirrors source evaluation order.

The product factorization is a better *network semantics* theorem than a better *compiler proof* theorem.

So I would keep the fold as the main route. I would just not prove it against full assignments and `PMF` immediately.

In other words:

* **fold-based induction:** good choice
* **full-assignment PMF fold-based induction:** bad choice

---

## Specific hints by hard part

### `toPMF_bind`

If you keep it, avoid putting the guard in the theorem statement if you can. The cleaner way is to prove the RHS `tsum` reduces to a finite sum over the support of `d`. The value outside support is irrelevant because the coefficient is zero.

But again, I would try hard not to need this theorem in the main proof at all.

### `rho_faithful`

Weaken it.
Prove “agreement on reads of the continuation”, not equality of full environments.

### `rawEnvOfCfg_mono`

This should disappear under prefix semantics.

### `evalStep_decision_eq`

Make the node value type a legal-action finite type. Then this theorem becomes transport of a distribution across an equivalence, which is routine.

### `evalStep_utility_noop`

Push it out of the induction. Treat it as a suffix theorem or an observational-equivalence lemma.

### `Fin` arithmetic

This is another sign you are introducing `Fin n` too early.

During the correctness proof, prefer:

* natural-number node IDs with `< nextId` side conditions, or
* prefix-indexed configurations

Then repackage into `Fin n` only when interfacing with the final MAID API.

Raw `Fin`-casting across growing bounds is rarely where the real theorem lives.

---

## The induction statement I would aim for

Something like this shape is usually the right one:

```lean
Theorem segment_sound
  (compile p from st₀ = st₁)
  :
  for any prefix assignment/configuration a consistent with st₀,
  evaluating exactly the nodes emitted by p from a
  yields the same distribution as
  running the Vegas semantics of p in the environment reconstructed from a,
  while extending a on the emitted node segment.
```

The important features are:

* **segment**, not full network
* **consistency relation**, not full equality of raw envs
* **extension of a prefix**, not mutation of a total default assignment
* **same finite distribution world**, not `FDist` vs `PMF`

That is the theorem shape that seems to fit your compiler.

---

## One more structural thought

You may be proving the correctness theorem one level too specifically.

The proof skeleton seems generic for any language with:

* deterministic lets
* stochastic sampling
* observable decisions
* hidden-state reveals
* payoff return

That suggests a more reusable intermediate theorem:

> sequential effectful program with fresh-node emission compiles to a DAG/fold semantics preserving the induced distribution.

Then Vegas-specific proof obligations reduce to typing, visibility, and environment reconstruction lemmas.

That abstraction might actually reduce total work, because the induction becomes cleaner once stripped of Vegas-specific syntax.

---

## Bottom line

The theorem itself is substantial. The current proof burden is larger than it needs to be.

The biggest simplifications are:

1. **Do not carry `PMF`/`ENNReal` through the compiler proof.**
2. **Do not reason over total assignments during the main induction.**
3. **Do not prove full environment reconstruction when agreement-on-reads suffices.**
4. **Do not encode legal actions via `idxOf` + clamp.**

If you change only the first two, the project likely becomes much more tractable. If you change all four, the main theorem should still be nontrivial, but it will look like compiler correctness rather than representation repair.
