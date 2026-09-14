# VegasCore

VegasCore is a Lean 4 foundation for executable games with partial information.
Its strict compiler path is:

```text
sequential checked source
  -> typed event graph
  -> explicit sealed-message program
  -> native public-message execution
```

The source language gives choices an explicit owner and visible environment.
Compilation retains typed fields, dependencies, guards, probability tables,
and payoff code in an event graph. The native endpoint uses the shared
`Interaction` message pool and explicit commitment service.

The source-to-graph certificate preserves the source outcome law and exactly
backtranslates arbitrary unilateral graph policies. The pending-message backend
has an independent graph-to-candidate utility simulation. Their composition,
`SealedCompilation.candidate_deviation_bound_of_source_floor`, bounds every
randomized native unilateral deviation by a legal written-source deviation
against unchanged opponents. Nash and same-error epsilon-Nash are preserved and
reflected at the actual generated profiles.

The candidate runtime admits competing commitments, unopenable accepted handles,
malformed traffic, retries, replay, pending-message observations, and withholding.
Its adaptive wire policy sees the pending pool, but not the private candidate
table. Periodic inclusion capacity, roster coverage, and sufficiently large
timeout windows protect unchanged players. Withholding resolves to the programmed
default. The theorem assumes a source-only quitting condition: every outcome
possible under a unilateral source deviation against the fixed opponents gives
the deviator at least a bound, and every legal source execution recording its
designated quitting value gives it at most that bound. The floor is pointwise
on each deviation's support, not merely an expected-payoff comparison. A global
floor over all legal executions is a stronger sufficient condition and supplies
the reusable `candidatePayoutSimulation` certificate.

The proof factors through the graph as an independently usable strategic
intermediate representation. The compiler certifies public-prefix readability,
unique direct disclosures, and the public payout interpretation. The backend
constructs its own deviation coupling and proves the timeout utility comparison;
it does not assume a source-image witness or a desired native incentive law.
The all-compiled honest law preserves the original public outcome distribution.
The graph theorem supports arbitrary utilities of typed public fields; the
end-to-end source theorem applies a supplied valuation to the programmed payout.
See [the composition design](docs/compilation-design.md#strategic-intermediate-representation).

The candidate theorem covers homogeneous commit/reveal graphs with universally
accepting guards, no samples, and no initially private disclosure. The registered-site
host additionally has finer conditional timeout-checkpoint incentive results;
transporting such source conditions to the candidate host remains open. Nontrivial
guard validation, chance compilation, heterogeneous sealed values, concrete
commitment cryptography, and ledger/EVM refinement remain further work. Service
is an explicit operational assumption, not a proved censorship-resistance result.

The former fused application path is passive reference material under
`archive/fused/`; it is not an active compiler edge or evidence for these results.

The active libraries are `GameTheoryExtensions`, `Interaction`, `Vegas`,
the retained tests, and the source/native paper audit. See
[the artifact guide](ARTIFACT.md), [module boundaries](docs/module-architecture.md),
and [compilation design](docs/compilation-design.md).

## Build

```text
git submodule update --init --recursive
lake exe cache get
python scripts/check-doc-references.py
python scripts/check-lean-options.py
python scripts/check-module-boundaries.py
python -m unittest discover -s scripts -p "test_*.py"
lake --wfail build
```

GameTheory is a pinned, separately maintained software dependency. General
game-theoretic simulation results live under GameTheory namespaces; Vegas owns
the source language, event-graph compiler, and its native integration.

## Paper target and proof status

The single active `Paper.lean` audit contains only direct delegations to proved
repository theorems; it has no admissions and does not count archived claims.
The exact active layering, source-payout pending-message theorem, and next
end-to-end target are listed in
[the active tower](docs/active-tower.md).

A successful Lean build checks the active proof terms. It is not evidence that
the separate manuscript's claims are all established. `paper-claims.json`
distinguishes active audit mappings from explicitly unverified manuscript
claims. The latter are coverage gaps, not a count or a worklist of missing
theorems. Reference material supplies neither proofs nor audit obligations.

Readable source material for porting is preserved in the
[proof reference archive](archive/fused/README.md), outside all active libraries.
