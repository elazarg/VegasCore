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
`SealedCompilation.candidate_public_deviation_bound`, bounds every
randomized native unilateral deviation by a legal written-source deviation
against unchanged opponents. Nash and same-error epsilon-Nash are preserved and
reflected at the actual generated profiles.

The candidate runtime admits competing commitments, unopenable accepted handles,
malformed traffic, retries, replay, pending-message observations, and withholding.
Its adaptive wire policy sees the pending pool, but not the private candidate
table. Periodic inclusion capacity, roster coverage, and sufficiently large
timeout windows protect unchanged players. Withholding resolves to the programmed
default. The theorem assumes a source-only quitting condition: a legal quitting
settlement is no better than any supported unilateral source continuation with
the same public environment strictly before that commitment. Opponents stay
fixed in the continuation law. This is a pointwise comparison, stronger than
ordinary ex-ante quit dominance. A global quitting cap and equal fixed-opponent
support floor suffice; a floor over all legal executions also supplies the
reusable `candidatePayoutSimulation` certificate.

Separate source quitting caps and supported-outcome floors give a quantitative
version: every native deviation is bounded by a legal source deviation plus the
gap times that native deviation's actual timeout probability. A source epsilon-Nash profile
therefore compiles to an `(epsilon + delta)`-Nash profile when every player's gap
is at most `delta >= 0`. Reflection at compiled profiles needs no quitting
condition; it follows from honest public-outcome utility agreement under the service assumptions.

The proof factors through the graph as an independently usable strategic
intermediate representation. The compiler certifies public-prefix readability,
unique direct disclosures, and the public source outcome interpretation. The backend
constructs its own deviation coupling and proves the timeout utility comparison;
it does not assume a source-image witness or a desired native incentive law.
The all-compiled honest law preserves the original public outcome distribution.
The end-to-end theorem supports any interpretation of the public terminal source
environment, including outcome maps followed by player-specific utilities.
Payout valuations are a special case. The native observation reads only public
graph fields; every supported stopped-game result decodes to a legal public
source outcome, including after defaults. This support result needs no fair
service, but does not fix opponents or establish a deviation law.
See [the composition design](docs/compilation-design.md#strategic-intermediate-representation).

The candidate theorem covers homogeneous commit/reveal graphs with universally
accepting guards, no samples, and no initially private disclosure. The registered-site
host additionally has conditional timeout-checkpoint incentive results;
transporting general conditional source comparisons to the candidate host remains open.
Nontrivial public guards have checked opening validation and legal whole-graph
settlement under arbitrary completed native policy executions. Extending the
strategic theorem to those guards, chance compilation, heterogeneous sealed
values, concrete commitment cryptography, and ledger/EVM refinement remain further work. Service
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
