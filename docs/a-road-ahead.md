# A road ahead

This is a non-binding implementation plan. Revise the decomposition when a
smaller proof boundary becomes clear; retain the acceptance criteria. The
[active tower](active-tower.md) records checked results separately.

## Goal and theorem shape

Compile checked VegasCore programs to a realistic abstract public-message
runtime, preserving at least Nash equilibrium, and carry the same theorem
through executable deployment. Ethereum is the grounding target. Transport,
commitments, resolution, and strategic simulation remain runtime-general.

For a source profile `s`, generated profile `C s`, and arbitrary observation-local
unilateral runtime deviation `d`, the ideal-target theorem should establish:

```text
honest law:  observe(run(C s)) = law(source(s))
deviation:   exists legal source deviation b,
             E[U_target(run((C s)[i := d]))]
               <= E[U_source(source(s[i := b]))]
```

The opponents stay unchanged. The strategy compiler describes compliant play;
it neither generates player software nor restricts submitted transactions.
The environment may adapt to its observations, including pending payloads;
its deadline-relative service contract is explicit. Player-builder coalitions
are a different strategy space from unilateral player deviations.

Honest utility agreement and the deviation inequality give same-error
epsilon-Nash preservation and reflection at generated profiles. Exact deviation
outcome laws are a stronger, separate objective: informed quitting can change
those laws without increasing utility. Concrete cryptography, costs, or
imperfect service may require quantified error rather than exact Nash.

No final theorem should exclude heterogeneous values, rejecting guards,
dependent source chance, or initial fields merely because a proof was built
without them. A target capability restriction must identify the missing
operation or information, preferably with a counterexample or impossibility
theorem. Networking constructs do not belong in the minimal source language.
Whether the current source failure semantics matches the intended programming
contract must be settled explicitly, not assumed from a backend default.

The [deferred-guard specification](deferred-guards-semantics.tex) and checked
`Interaction.GuardedPublication` component provide a candidate interpretation:
ordinary typed values, pending publications, and null failures are distinct;
deferred relations fail the publication that closes an inconsistent tuple.
Private bindings and earlier public results are immutable. Consistency and
ordinary satisfying executions are proved. Integrating source expression
evaluation, observations, chance, and settlement remains the acceptance test;
the component alone does not complete the models milestone.

The [source migration plan](source-semantics-migration.md) records the agreed
explicit-result typing, the tentative decision to retain primitive public
chance, the full-source acceptance test, and the downstream migration order.
Agreement on these contracts does not establish their source implementation
or downstream correspondence.

## One compilation spine

```text
checked sequential source
  -> typed event graph with compiler-proved information certificates
  -> typed logical commitment protocol
  -> public pending-message application with deadline resolution
  -> transaction/block host
  -> identified executable contract in a checked VM/ledger semantics
```

Each artifact has its own observations and strategy space. A game presentation
is an analysis interface for that artifact, not an independent compiler
destination. The backend consumes graph certificates, not a source-image
assumption. The end-to-end theorem delegates to edge composition.

Use the source-certified canonical operation order for the baseline protocol.
A public program counter gates application acceptance, not off-order submission,
delivery, observation, or attempted inclusion. Commit and reveal remain
distinct source operations. Inclusion checks alone cannot justify publishing
an honest opening early. Optional parallel admission belongs in a later
refinement with its own information theorem.

The [typed protocol interface](typed-protocol-interface.md) specifies the next
boundary and its operational implementation. It is not a preservation theorem. Local transition
classification must be accompanied by the joint observation/probability law
needed to translate adaptive deviations.

## Milestones and exit tests

### 1. Typed protocol with actual language coverage

Separate the three acceptance points within this milestone:

1. **Models:** all source constructs have operational representations; raw
   deviations remain expressible; local capability contracts are explicit;
   mixed-feature tests compile; the mathematical source failure interpretation
   is settled. Definitions that merely carry arbitrary resolution values do
   not settle that interpretation.
2. **Compilation:** one actual checked mixed-feature program is lowered through
   the graph to this model, including its guard contexts and source-defined
   resolution behavior. No source constructor is disabled.
3. **Correctness:** the generated program satisfies the honest outcome law;
   milestone 2 below adds the whole-program arbitrary-deviation certificate.

The current source admits only guard-valid commitments and has deterministic
reveal. The intended target accepts opaque candidates and checks their guards
at reveal; failure resolves to programmed quitting. Prove the interpretation
between these semantics, including dependent private choices and subsequent
settlement, or explicitly correct the source abstraction. Do not silently add
recoverability or commit-time validity proofs to make the models agree.

Replace homogeneous sealed values with site-indexed values and typed decoding.
Separate raw candidates from legal source actions. Preserve arbitrary candidate
selection, failed openings, retries, and rejection. Rejection is an application
stutter; authorized resolution installs a declared legal alternative and its
continuation. Retain original guard inputs without pretending public code can
read a secret. In the current source, legality is determined at commitment:
a raw candidate rejected at reveal never becomes a legal source action merely
by being bound. A correspondence with that source needs a legal alternative
at the commitment checkpoint. A source with explicit deferred failure instead
needs its own policy semantics and correspondence; existing theorems do not
automatically transfer to the changed rules.

Design chance and initialization at this same boundary before proving another
whole-program specialization. Chance draws from the source conditional kernel
once, caches the result, and publishes it as the source's public sample step.
There is no strategic sampler or publisher. Private initial data belongs to a
setup realization, not public constants. An initial sealed binding can be used
in its owner's guard and later disclosed. Its deterministic disclosure does
not itself give the owner a source quitting choice; the host must implement its
availability. Setup refusal is a separate pre-play contract.

Exit test: one actual checked source program combines two value types, a
rejecting guard, meaningful private initial data, and dependent chance. Its
generated public-message application has legal resolution and an exact honest
outcome law under named capabilities. No disabled case implements a source
operation; no interface field assumes the desired whole-run law.

### 2. Whole-program arbitrary-deviation theorem

Prove current-operation observation and continuation laws, then compose them
along canonical execution. Reuse the graph runner, probability factorization,
candidate persistence, deadline service, and generic utility simulation where
their contracts fit. Do not repeat the source induction inside the backend.

Extraction must be causal: earlier source choices cannot depend on later
disclosures. Freeze or condition environmental randomness jointly with the
deviator; do not independently resample correlated signals. Malformed and
guard-invalid candidates must retain legal unchanged-opponent continuations,
not merely yield an arbitrary source support witness.

Exit test: a graph-relative honest/deviation certificate for the typed protocol,
instantiated by the compiler, and a directly delegated source-to-pending
epsilon-Nash theorem. The combined program from milestone 1 instantiates it.
The incentive premise is source-defined and its strength is explained. An
assumed native-checkpoint inequality does not replace deriving it from that
source condition.

This is the immediate strategic target. Supporting lemmas count toward it only
when they discharge a named part of this certificate.

### 3. Realistic abstract transaction/block host

Realize the application with authenticated callers, transaction identities,
nonces/replay protection, pending delivery, inclusion, atomic state changes,
rejection/revert receipts, block clocks, and a finality boundary. Keep
adversarial traffic and adaptive ordering. Service is relative to expiry,
not eventual fairness after the deadline.

Exit test: arbitrary-transaction transport/application refinement, including
failure effects, and a composed strategic theorem. State who pays fees and how
balances, costs, and trace-valued utilities relate to source outcomes. Prove
cost bounds or enrich the interpreted outcome where equality fails. Trusted
account, verification, or entropy services must be named capabilities.

### 4. Executable artifact and VM refinement

Compile to identifiable executable code. Separate computable compilation and
representation from noncomputable analysis witnesses. Prove storage layout,
handlers, dispatch, linking, deployment, and whole-program execution refinement.
Component instruction proofs alone do not establish this edge. The expression
implementation, encodings, and resource bounds must be realizable on the chosen
VM: arbitrary semantic expression interfaces are not automatically executable.

Exit test: a theorem naming deployed code and its host, with source-to-host
Nash preservation by composition. Independently exercised instruction semantics
and cross-implementation vectors help detect proofs against an incorrect model.

### 5. Concrete services and broader guarantees

Replace ideal commitments, verification, and chance by separately justified
implementations. State computational strategies and security errors; the ideal
exact theorem is not hiding/binding against unbounded concrete adversaries.
Account for service/finality errors and bound utility where probability error
must become incentive error.

Broaden source quitting criteria to justified conditional tests. Investigate
coalitions, robust outcomes, trace utilities, and parallel admission as distinct
claims; retain stronger guarantees for feature combinations that support them.

Exit test: explicit compositional error bounds and concrete instances, or
precise nonimplementability results where a required capability is absent.

## Capabilities and failure cases

| Concern | Required contract; what it cannot conceal |
| --- | --- |
| Withholding | Legal source resolution and an incentive comparison at stopping information. Ex-ante strict quit dominance alone can fail after a new observation. |
| Private guards | Public dependencies or a sound private-verification capability. A secret in proof state does not implement public execution. |
| Chance | The correct conditional draw, sample-once storage, and availability. Strategic selection or retrying a draw changes the game. |
| Initial secrets | Authenticated private setup and availability for deterministic disclosure. Setup refusal must be accounted for before entering the source game. Public EVM storage cannot implement private storage directly. |
| Pending traffic | Observations relative to all existing information, including openings before inclusion. Separate hiding claims need not compose. |
| Progress | Deadline-relative service and finality. Termination by default does not imply protection of honest players. |
| Costs | A source interpretation or utility discrepancy bound. Equivalent payouts need not give equivalent incentives. |

These are contracts to instantiate, not proposed blanket hypotheses for every
program. Require a capability only when the program and claimed guarantee use it.

## Work allocation and stopping discipline

The coordinating agent owns theorem scope, the dependency plan, interface
review, integration, and whole-project status. Delegate bounded implementation
pieces with disjoint file ownership. Mathematical design and adversarial review
run in parallel when Lean work shares too many dependencies. One agent owns
the Lean build; freeze edits for the full warning-free gate.

At a milestone report: broadest source coverage, deepest target, exact strategic
conclusion, assumptions, and next undischarged edge. Report completion only after
the exit test passes. Line counts, lemma counts, and green coverage checks are
not completion metrics.

Keep `Paper.lean` to directly delegated paper capstones and important lemmas.
Supporting results stay in their mathematical modules. Keep one live
implementation of a migrated edge; delete superseded code after consumers move.
Archives are readable references only.

The richer `../vegas` frontend stays separate. It should export a checked core
artifact with a specified lowering correspondence; duplicating its surface
syntax in the minimal core is not a prerequisite for this plan.
