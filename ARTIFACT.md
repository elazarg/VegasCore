# VegasCore proof and artifact guide

This artifact checks the active sequential-source, event-graph, and native
public-message results. It is not a verification of a Kotlin frontend,
blockchain ledger, deployed contract, or EVM.

## Reproduction

Use the pinned Lean toolchain and dependency revisions:

```text
git submodule update --init --recursive
lake exe cache get
python scripts/check-doc-references.py
python scripts/check-lean-options.py
python scripts/check-module-boundaries.py
python -m unittest discover -s scripts -p "test_*.py"
lake --wfail build
```

Do not run `lake update` when reproducing a pinned revision. The cache is only
a build optimization; the subsequent build checks the proof terms.

## Reading route

| Question | Main location |
| --- | --- |
| What is a checked source program? | `Vegas/Core/` |
| What is its written-order execution? | `Vegas/Core/SmallStep.lean`, `Vegas/Core/Strategy.lean` |
| How is the event graph built? | `Vegas/Compile/Compiler.lean`, `Vegas/EventGraph/` |
| How are source decisions and graph reads related? | `Vegas/Compile/Compiler.lean`, `SourceAdequacy.lean`, and the event-graph laws |
| What executes public messages? | `Interaction/`, `Vegas/Compile/SealedSource.lean` |
| Which active games use that runtime? | `Vegas/Game/SealedRounds.lean`, `SealedMessages.lean`, `SealedRelease.lean`, and `SealedTimeoutApplication.lean` |
| Which claims are paper-facing? | The single root audit, `Paper.lean` |

Read the owning theorem and definitions, not only its paper-facing restatement.
The audit pins theorem axioms; it does not prove that prose and formal
statements agree.

The separate manuscript checkout includes broader target claims recorded in
`paper-obligations.json`; those are not current verified results.
`python scripts/check-paper-claims.py --allow-open-obligations` checks progress
against both the direct Lean audit and the pinned manuscript snapshot. The
strict checker remains a completion gate and fails while these obligations
are open. `--allow-missing-paper` permits a clone without the separate paper
checkout; it does not turn an unproved theorem into a proof.

## Trust and scope

Proved audit entries use Lean's standard logical axioms reported by
`#print axioms`. The active `Paper.lean` file is intentionally a small
direct-delegation audit surface and currently contains no admissions. Open
strategic work is documented as an obligation in `docs/active-tower.md`; it is
not disguised as a proved paper theorem. Production libraries cannot import
the audit or contain admissions.

The repository does not treat generated code, test vectors, or an executable
compiler alone as a refinement proof.

Native support theorems say that supported sealed-message executions decode to
reachable graph prefixes, and terminal prefixes reconstruct written-order
source executions with matching payout evaluation. The same support guarantee
holds for arbitrary bounded policy executions, including pending messages,
recipient-local delivery, inclusion, replay, malformed traffic, and
withholding. The scheduler/environment sees the full pending pool; player
views currently expose only their own inbox, sent messages, and the public
ledger.
Ideal-service hiding is proved separately. These results are operational and
support-level; they do not identify an arbitrary runtime policy with a source
policy.

`Vegas.SealedCompilation.RoundModel.isεNash_iff_of_checkpointDominance` is a
concrete strategic edge to the actual pending-message round driver. It uses
timely service, normal source/native utility agreement, and conditional
comparisons at the player's actual timeout-checkpoint information. The legal
source completion retains that player's registered choices. The theorem covers
all unilateral native policies and derives its bound from the constructed
coupling. It preserves and reflects Nash and same-error epsilon-Nash at
compiled profiles; a positive margin charges the actual timeout probability.
`checkpointUtilitySimulation` packages profile-uniform comparisons for
composition. A uniform cap on own timeout utility below every source utility
supplies `utilitySimulation` as a sufficient case. These utility theorems do
not assert exact outcome-law simulation after selective withholding.

For the resolving sealed backend, `pending_honest_round_source_law` in
`Paper.lean` audits an exact coupling with the original written-source profile.
The native marginal is the actual early-stopping pending-message driver.
Roster coverage, periodic inclusion capacity, a sufficient relative timeout
window, and a whole-period termination budget imply normal completion and
exact decoding at every supported result. A multistage nullable-source test
instantiates the assumptions with delayed service and arbitrary unreserved
wire choices. `pending_round_approximate_nash_iff` and
`pending_round_deviation_margin` audit the uniform-cap strategic result.
The `pending_checkpoint_*` theorems audit the conditional result, actual local
information, and retained commitments. Program-specific proofs of the
conditional incentive premise and general source-settlement identification
after defaults remain open. The strategic regression uses simple supplied
utilities, not a proved source payout model. Independently,
`pending_public_payout` verifies public-only payout reconstruction on normally
decoded terminal source executions.

At the graph boundary, `Vegas.EventGraph.Strategic.deviation_law` proves the
sharper exact statement under declared-read locality and a single ready
commitment per player: every canonical unilateral replacement is one behavioral
graph deviation, and `isεNash_compileProfile_iff` follows for every observation
utility. `Paper.lean` delegates both graph claims directly. The theorem is not
yet a source-language or pending-message theorem; a graph with simultaneous
same-player commitments needs a correlated frontier strategy or an explicit
additional hypothesis.

The reusable mechanism-design step for a designated quit is proved in
`GameTheoryExtensions/Core/QuitTransfer.lean`. It transfers a strict source
improvement whenever the runtime supplies a support-level law identifying the
target quit with the source quit. This law is a field-level obligation of a
concrete runtime certificate, not an assumption hidden in the sealed compiler.
