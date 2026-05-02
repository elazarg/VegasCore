# Configuration-style operational semantics for Vegas — proposal

Status: revised after code review. Initial implementation in progress; the
raw layer, neutral configuration layer, and checked/FOSG bridge are now in
code.

## Goal

Add a configuration-style small-step semantics to Vegas and prove it agrees
with the existing denotational and trace semantics. The FOSG connection should
then be stated through the existing checked-world / PMF history projection
bridge, not as a direct raw equality.

```
raw small-step  ⟷  traceDist / positive-weight Trace  ⟷  outcomeDist
                                                          │
                                                          ▼
                                      checked PMF step / mapped FOSG.runDist
                                                          │
                                                          ▼
                                           toKernelGame / IsNash / eu / ProtocolNash
```

The motivating use case is reasoning about deployed agents (e.g. on-chain),
where you want to phrase liveness, fairness, MEV, scheduler, or state-machine
properties against a transition relation, and then transport those statements
to the strategic / equilibrium layer.

## What we already have

| layer                     | file                               | shape                              |
| ------------------------- | ---------------------------------- | ---------------------------------- |
| big-step / denotational   | `Vegas/BigStep.lean`               | `outcomeDist σ p env : FDist (Outcome P)` |
| path / tree-style         | `Vegas/TraceSemantics.lean`        | `Trace Γ p` + `traceWeight` + `Trace.legal` |
| reachability (∃ trace)    | `Vegas/TraceSemantics.lean`        | `CanReach`, `Reach σ` (inductive)  |
| runtime configuration     | `Vegas/Config.lean`                | `World`, `World.initial`, `terminal`, `syntaxSteps` |
| sequential game view      | `Vegas/FOSG/Basic.lean`            | `active`, `availableActions`, checked/cursor transitions |
| operational kernels       | `Vegas/Operational.lean`           | `OmniscientOperationalProfile.commit` |
| strategic / equilibrium   | `Vegas/Strategic.lean`, `Equilibrium.lean`, `ProtocolSemantics.lean` | `KernelGame`-based |

### What this means

- `Vegas/Config.lean` now defines `World := { Γ, prog, env }`,
  `World.initial`, `terminal`, and `syntaxSteps`. This is the neutral
  configuration shape shared by raw small-step and the FOSG bridge.
- `active` and `availableActions` remain in `Vegas/FOSG/Basic.lean` because
  they are game-view structure over configurations, not part of the neutral
  runtime configuration.
- `Trace` (`TraceSemantics.lean:48`) is essentially a tree of complete paths
  through these configurations — but it carries the full path as one term, not
  a step relation.

What is missing is a **single labelled step relation between `World`s**, and
a small set of agreement theorems that nail it to the existing semantics.

## What's missing

1. Done: a step relation `Step : World P L → FDist (Label P L × World P L) → Prop` (or
   the deterministic-once-the-label-is-fixed variant — see "Design choices"
   below). One rule per `VegasCore` constructor.
2. Done: a reflexive-transitive closure / multi-step relation, plus a "run from
   `World.initial g` to a terminal world" wrapper that returns an `FDist
   (Outcome P)`.
3. Done for the raw distribution surface: agreement theorems linking the new relation to `traceDist` and
   `outcomeDist`.
4. Done under `Vegas/FOSG/SmallStep.lean`: a separate checked/PMF agreement theorem linking the checked small-step
   kernel to mapped `FOSG.runDist`.
5. In progress: a small but real cleanup pass on the layers we already have, before adding
   another one — see "Cleanup" below.

## Cleanup we should do first

These are not strictly required to add small-step, but each one reduces the
number of agreement theorems we'll need or removes ambiguity about which
object is canonical.

### C1. Pick a single configuration type

Today there are *de facto* three configurations:

- `World` (FOSG): `{ Γ, prog, env }`.
- The implicit configuration in `outcomeDist` and `Trace`: `(Γ, p, env)` as
  three separate arguments.
- `OmniscientOperationalProfile`: not a configuration but the "scheduler"
  side; lives separately.

Proposal: promote `Vegas.World` (currently in `FOSG/Basic.lean`) to
`Vegas/Config.lean` (or `Vegas/World.lean`) and re-export from `FOSG/Basic`.
Rephrase the *statements* of the existing big-step / trace lemmas in terms
of `World` where it doesn't break proofs (often just a thin abbreviation
layer is enough). This lets `Step`, `Trace`, `outcomeDist`, and `runDist`
all share one configuration type and avoids per-layer re-bundling.

### C2. Make `Trace` and `Reach` line up syntactically

`CanReach` / `Reach` (`TraceSemantics.lean:140`, `:179`) and `Trace`
(`:48`) have nearly-identical constructor lists. A small refactor where
`CanReach (p, env) oc ↔ ∃ t : Trace Γ p, t.legal ∧ traceOutcome p env t = oc`
is stated once, then the rest of `Reach` follows by pushing through
`traceWeight > 0`.

Current status: the headline `CanReach` theorem already exists as
`canReach_iff_exists_legal_trace` in `TraceCorollaries.lean`; the packaged
`World.canReach_iff_exists_legal_trace` form is now also available.

### C3. Name the trace ↔ outcomeDist agreement explicitly

`outcomeDist σ p env = ∑ t, traceWeight σ t • δ (traceOutcome p env t)` is
described in `TraceSemantics.lean:14–18` and proved (as `traceWeightSum`-
style equalities). Give the headline equality a single canonical name
(e.g. `outcomeDist_eq_traceSum`) and re-export it. Small-step agreement
will route through this one lemma.

Current status: `outcomeDist_eq_traceWeightSum` already exists in
`TraceCorollaries.lean`; `outcomeDist_eq_traceSum` and packaged
`World.outcomeDist_eq_traceSum` compatibility aliases are now available.

### C4. Decide the canonical form of "operational profile"

`OmniscientOperationalProfile` is a `Pi`-typed bundle of full-state commit
kernels (`Operational.lean:25`). It's the right thing for raw big-step and raw
small-step.

It is *not* automatically a FOSG behavioral profile: the FOSG bridge uses
guard-legal, view-indexed PMF behavioral strategies. For the raw small-step
layer, keep `OmniscientOperationalProfile`. For the FOSG agreement layer,
state a separate PMF/check-world theorem over `LegalProgramBehavioralProfilePMF`
or add explicit observation-respecting/admissibility assumptions before
constructing a FOSG profile from an omniscient one.

## The new layer

### Files to add

```
Vegas/SmallStep/
  Defs.lean         -- Step, Steps, runSmallStep
  Agreement.lean    -- agreement with Trace and BigStep
  Properties.lean   -- progress, functionality, bounded-horizon lemmas
Vegas/SmallStep.lean -- public entrypoint: imports + re-exports
Vegas/FOSG/SmallStep.lean -- checked PMF / mapped FOSG.runDist bridge
```

## Architecture notes after implementation

- `World`, `terminal`, and `syntaxSteps` were competing because they were
  semantically neutral but lived in FOSG. They are now unified in
  `Vegas/Config.lean`.
- `active` and `availableActions` are not neutral runtime notions. They remain
  FOSG-owned as the game-theoretic view of a protocol configuration.
- `CheckedWorld` and `CursorCheckedWorld` are still two presentations of
  checked execution state. They are related by `CheckedWorld.ofCursorChecked`,
  but should not yet be claimed equivalent: `CursorCheckedWorld` is the finite
  executable carrier, while `CheckedWorld` is suffix/proof oriented and useful
  for semantic kernels.

### Core definitions (sketched)

A label records the observable event at one step. Silent steps carry no
information; sampled and committed steps carry the chosen value.

```lean
inductive Label (P : Type) (L : IExpr) where
  | tau                                          -- letExpr or reveal
  | sample (b : L.Ty) (v : L.Val b)              -- nature's draw
  | commit (who : P) (b : L.Ty) (v : L.Val b)    -- player's action
```

The raw step relation. We give it as a *probabilistic* relation
`Step : World → FDist (Label × World) → Prop` (one rule per syntactic form),
i.e. each non-terminal world has exactly one outgoing step distribution.
This makes `Step` essentially functional in the world and makes the
agreement proofs trivial induction.

```lean
inductive Step (σ : OmniscientOperationalProfile P L) :
    World P L → FDist (Label P L × World P L) → Prop
  | letExpr   : Step σ ⟨_, .letExpr x e k, env⟩   (FDist.pure (.tau, …))
  | reveal    : Step σ ⟨_, .reveal y who x hx k, env⟩ (FDist.pure (.tau, …))
  | sample    : Step σ ⟨_, .sample x D k, env⟩
                   (FDist.bind (L.evalDist D _) (fun v => FDist.pure (.sample _ v, …)))
  | commit    : Step σ ⟨_, .commit x who R k, env⟩
                   (FDist.bind (σ.commit who x R _) (fun v => FDist.pure (.commit who _ v, …)))
```

`runSmallStep σ w : FDist (Outcome P)` is defined by structural recursion on
`w.prog` and matches `outcomeDist` constructor-for-constructor. A later theorem
can also characterize it as "bind one `Step`, then recurse" for non-terminal
worlds.

### Multi-step / labelled trace

A "small-step trace" is a list of `Label`s plus a witness that successive
applications of `Step` produced them. It should agree with `traceDist`, not
with all `Trace.legal` traces unconditionally.

Reason: `Trace.legal` checks sample support and commit guards, while
`Step σ` follows the support of `σ.commit`. A legal trace may have zero
profile weight, and an arbitrary omniscient profile may put mass on
guard-illegal commits. Legal-trace agreement requires an admissible profile
assumption and possibly a full-support assumption; raw distribution agreement
does not.

```lean
def smallStepTraces (σ) (w : World P L) : Finset (List (Label P L) × Outcome P)
def smallStepWeight (σ) (w : World P L) : List (Label P L) → ℚ≥0
```

### Agreement theorems

Three theorems, all by induction on `syntaxSteps`:

1. **Trace-distribution equivalence** —
   `smallStepTraceDist σ w` is the labelled projection of `traceDist σ w.prog
   w.env`, and positive-weight small-step traces correspond to positive-weight
   `Trace`s. Legal-trace corollaries require `FairPlayProfile`/admissibility.

2. **Big-step equivalence** —
   `runSmallStep σ w = outcomeDist σ w.prog w.env`.
   Proof: induct, each constructor of `Step` matches the corresponding
   `outcomeDist` clause definitionally up to `FDist.bind`/`FDist.pure`.

3. **Checked PMF/FOSG equivalence** —
   For `β : LegalProgramBehavioralProfilePMF g`, the checked PMF small-step
   kernel agrees with
   `PMF.map (observedProgramHistoryOutcome g hctx)
     ((toFOSG g hctx).runDist (syntaxSteps g.prog)
       (toObservedProgramLegalBehavioralProfilePMF g hctx β))`.
   This should reuse `checkedProfileStepPMF`,
   `checkedProfileStepPMF_bind_checkedVegasOutcomeKernelPMF`, and the existing
   mapped-`runDist` outcome closure proof rather than proving a direct raw
   FOSG equality.

Once (2) is in place, **all** strategic theorems transport for free via
`isNash_iff_protocolNash` etc. — there is nothing new to prove on the
equilibrium side.

### Properties to expose

These are the lemmas that make small-step useful for blockchain-style
reasoning, beyond what `Trace` already gives:

- `progress` — every non-terminal world has a step.
- `preservation` — `Step` preserves typing and well-formedness.
- `determinism modulo label` — fixing the label collapses `Step` to a
  function (this is what makes a "scheduler" / chain a labeller).
- `bounded_horizon` — multi-step terminates in `syntaxSteps w.prog` steps.
  Already provable from `FOSG/Basic.lean:144`.
- `commute_independent_commits` — commits at independent player views
  commute. Already proved at the big-step level (`outcomeDist_comm_commit`,
  `outcomeDist_comm_reveal` per `TraceSemantics.lean:24`); restate at
  small-step.

## What this enables

- **Scheduler-as-permutation.** A blockchain that interleaves transactions
  is a re-ordering of `Step`-events; commute lemmas + agreement theorems
  give "outcome-distribution invariant under any interleaving that
  respects view dependencies" as a corollary.
- **Agent-level Hoare-style reasoning.** Pre/post-conditions on `World`s
  along `Step*` are the natural form for reasoning about an on-chain
  agent's behaviour. The agreement theorem with `outcomeDist` lifts these
  to statements about the strategic-form game.
- **Liveness / fairness.** Currently inexpressible. With `Step`, we can
  state things like "every player gets to commit eventually" as standard
  trace properties.
- **Refinement.** A deployed runtime is a `Step`-respecting simulation of
  the abstract semantics; this is the standard configuration-refinement
  obligation, which is hard to phrase against `outcomeDist` alone.

## Design choices to confirm before implementing

1. **Per-step probabilistic vs fully demonic.** Use
   `World → FDist (Label × World)` (one outgoing distribution per world),
   which matches the existing `outcomeDist` shape and avoids re-proving
   measurability lemmas. A "demonic" `World → Label → World → Prop`
   relation with a separate weighting is more standard PL, but doubles the
   agreement work.

2. **Labels are observable events vs full transitions.** Proposed labels
   above hide `letExpr`/`reveal` as `tau`. Alternative: distinct labels
   per syntactic form. The hiding choice matches `TraceSemantics.lean`'s
   "silent step" comments and the on-chain inlining model. If we expect
   to reason about *gas* or *step counting* at the chain layer, we may
   want non-silent labels for those forms instead.

3. **Where `View` enters.** Today, view legality is enforced at the
   strategy-bundle level (`LegalProgramBehavioralStrategy`). For
   raw small-step, `Step.commit` stays view-agnostic and consumes
   `OmniscientOperationalProfile`. The checked/PMF small-step/FOSG layer is
   where view-indexed legal behavioral profiles enter.

4. **`Trace` retirement?** Do not retire `Trace` in this pass. It already
   carries useful theorems (`traceDist`, `outcomeDist_eq_map_traceDist`,
   reachability corollaries). The first small-step implementation should prove
   compatibility with those theorems, not invert the dependency graph.

## Suggested order of work

1. Done: add `Vegas/SmallStep/Defs.lean` with `Label`, raw `Step`, `Steps`,
   `runSmallStep`, and `runInitialSmallStep`.
2. Done: add `Vegas/SmallStep/Agreement.lean` with
   `runSmallStep_eq_outcomeDist`, `runInitialSmallStep_eq_outcomeDist`, and
   trace-label projection theorems.
3. Done: add lightweight properties for the raw layer: progress, step
   functionality, exact syntax-step consumption, and bounded horizon.
4. Done: add a checked/PMF small-step wrapper under `Vegas/FOSG/SmallStep.lean`,
   reusing `checkedProfileStepPMF` rather than duplicating the FOSG proof stack.
5. Done for the core split: C1 (`World` lift) is implemented in
   `Vegas/Config.lean`; FOSG re-exports compatibility aliases.
6. Optional follow-up: a thin `Vegas/Refinement.lean` stating
   "implementation `I` simulates Vegas iff every reachable `I`-state
   has a matching `Step` with equal label-distribution," for the
   blockchain story.

## Non-goals

- No new equilibrium content. Strategic concepts already route through
  `outcomeDist`; once small-step agrees with `outcomeDist` they all come
  for free.
- No change to `WFProgram` or `WF.lean`. Well-formedness should be a
  precondition of the small-step rules, not a co-evolved invariant.
- No new probabilistic infrastructure. Everything is `FDist` (or `PMF`
  where the existing layer already uses it for the Kuhn theorem).

## Risk / cost estimate

Roughly: ~150–300 lines for the raw `Defs.lean`, ~100–250 lines for the
initial raw agreement/properties, then a separate checked/PMF PR if needed.

The agreement-with-FOSG proof remains the highest-risk item, but it should be
phrased as a mapped PMF history theorem over `LegalProgramBehavioralProfilePMF`,
not as a direct equality between raw `FDist (Outcome P)` and `FOSG.runDist`.
