# Proof review and mathematical mining

Current production implementation and acceptance status is in the
[implementation ledger](proof-review-progress.md#current-findings).

The strongest findings are new quantitative and hypothesis improvements, plus
several small proof migrations that need no new machinery. In strict isolated
checks, the actual timed execution and audited-settlement proof admits the
error **1 − product(1 − deferral)**; the public-source-splice bridge needed for
conditional priors also checks against its complete actual forced-agent
consumer. These are checked candidates, not production changes or new
sequential-equilibrium capstones.

The production Lean baseline is `ec4de15c`. GameTheory source and its gitlink
remain unchanged. Source semantics, runtime contracts, options, SE targets and
checklist statements are unchanged. The [implementation ledger](proof-review-progress.md)
records APIs already implemented; the opportunities below remain separate.

## Scope and reliability

The tracked-source inventory covers **2,549 Lean files and 619,625 physical
lines**, including the frozen GameTheory dependency and its opt-in trees.
Three independent domain reviews and a source/compiler integration review
screened declaration surfaces and selected complete proofs and consumers.

| Area | Files | Physical lines | Detail |
| --- | ---: | ---: | --- |
| GameTheory | 619 | 174,210 | Read-only inventory and selected owning APIs; no fresh whole-foundation body audit |
| GameTheoryExtensions and tests | 102 | 18,134 | [Mathematics](proof-review/mathematics.md) |
| Interaction, tests, EventGraph and Pending | 627 | 86,050 | [Runtime](proof-review/runtime.md) |
| Vegas.Game | 824 | 270,845 | [Strategic proofs](proof-review/games.md) |
| Foundation, Expr, Source and Compile | 274 | 45,304 | [Source/compiler](proof-review/source-and-compiler.md) |
| Examples, VegasTests, Paper and Vegas aggregators | 103 | 25,082 | Source/compiler integration screen |
| Total | 2,549 | 619,625 | |

The table uses the common inventory's root-aggregator convention. Domain
reports explicitly identify any directory-only counts. Inventory is broad;
manual body review is selective. **This is not a line-by-line audit of all
619,625 lines.** No counterexample to a current theorem was established in the
selected reviewed families. The own-cleanliness probe does refute removing its
recall hypothesis.

The scan exposed a tooling defect: result-type `let ... := ...` bindings were
counted as the start of the proof. A prominent eight-file Recovery match was
mostly repeated theorem statements. The scanner is corrected and regression
tested. Its 3,705 cross-file eight-line candidate windows remain search leads:
equation-style proofs do not have complete body coverage, windows overlap, and
renamed variants can be missed. Old and corrected body counts are not a valid
compression comparison. All savings below use physical lines of complete
proofs/modules and their actual adapters.

## Highest-value mathematical results

### Timing bounds retain more information than a union bound

[ServiceTimingCoupling](../Vegas/Game/ServiceTimingCoupling.lean#L184) currently
converts an exact timing-slot mixture into a TV error and then adds those
errors. Its actual slot-zero branch proves the stronger atom inequality

```
(1 - deferral(event)) * P(fix event at zero, x) <= P(timing, x).
```

Composing these lower bounds between full run laws retains the product of
the factors. The checked error is therefore

```
delta = 1 - product(event, 1 - deferral(event))
```

instead of the sum of deferrals. Two deferrals of 0.2 give 0.36 instead of 0.4.
**No additional statistical-independence assumption is introduced.** The
product comes from composing actual law minorization, not multiplying
independent-event probabilities.

The checked probe contains the complete actual one-event proof, all-event
induction, TV result and the actual
[typed-state/audited-payoff settlement consumer](../Vegas/Game/SourceServiceTurnSettlement.lean#L154),
with its existing first-turn law, timely contract, authentic audit and deposit
parameters. It is not inferred from a final unlabelled TV inequality.

The named honest/deviation wrappers and the
[per-player Nash bridges](../Vegas/Game/AsyncServiceNash.lean#L313) still need
production ports. Their expected error becomes `epsilon + 2*delta*range who`;
those complete Nash/capstone ports are **not checked here**. Event-specific
payoff sensitivity remains a different problem requiring continuation-value
guards. This is a quantitative strengthening, not a compression claim.

### Conditional priors have an actual source-splice adapter

The [existing conditional base laws](../Vegas/Game/OnePacketOwnerKeyed.lean#L53)
need the compared source draws to share an observed public signal. The missing
source bridge is now checked: InitialCellsAt and actual PublicCellsAgree imply
equality of every source public initial cell and every compiled public input.
The existing signal-observability premise therefore supplies the required
signal equality. The full actual
[forced-agent consumer](../Vegas/Game/OnePacketSpliceForced.lean#L189) checks
with conditional independence, retaining its well-formedness, covered fields,
same view, source/decode, changed-success and arbitrary-prefix guards.

A separate checked adapter proves that observability on public inputs itself
implies preservation of the signal by hidden-cell splicing. It need not be a
second independent hypothesis at the base-law boundary.

This closes a factual proof gap. It does **not** prove conditional-prior
recovery SE. Signal/hypothesis and constructor propagation remains across the
audited recovery pipeline, including the late-record comparison. The current
32 mentions in 25 Game files include documentation and an unused stronger
unconditional closure, so they are not 25 identical substitutions. No SE box
closes from the probe alone.

### Normalize the finite-weight comparison sharply

Two checked kernels improve the finite-weight calculus:

```
|sum p*f - sum q*f| <= (sum |p-q|)/2   when totals agree and 0 <= f <= 1
contamination L1 <= 2*rho/(1+rho)      when added mass <= rho*base mass
```

The first uses a payoff centered at one half; the second uses the actual final
total rather than discarding its added mass. Both retain the existing positive
normalizers and finite-sum scope. They support replacing the current two-site
SwapTransport bound `4*rho + 4*eps/(1-eps)` by
`2*rho/(1+rho) + 2*eps/(1-eps)` under the same hypotheses. **The assembled
two-site consumer migration is proposed; only its kernels are checked.**

## Sixteen concrete findings and their acceptance boundaries

An exact checked candidate is stronger evidence than a size estimate, but it
is still not a merged production refactor. Estimates include the proposed
common API and actual adapters. They overlap in places and must not be summed.

| Finding | Checked evidence | Remaining work / size |
| --- | --- | --- |
| Product-retention timing error | Complete actual producer, product induction, TV law and audited-settlement consumer | Port wrappers/Nash/public statements together; feature growth |
| Conditional public-source splicing | Factual public-input bridge, signal preservation and complete actual forced-agent consumer | Propagate through recovery and verify the full SE extension; growth unmeasured |
| Sharper normalized comparisons | Equal-total half-L1 and saturating contamination kernels | Assemble SwapTransport/ProductTransport clients; feature growth |
| Information-local own cleanliness | InputRecall locality, all actual site histories, and a counterexample without recall | Replace whole-fiber cleanliness in concrete count-support and phase example |
| Terminal-only audit payoff bounds | Actual audit absolute bound and full continuation-integrability adapter | Port bad/safe/context proof; retain exhausted and unfinished terminals |
| Six compiler tail-order consumers | Both complete actual modules with all six substitutions | 42 fewer physical lines; no new API |
| Lower source raw-result ownership | Existing helper checked at lower imports, four complete actual consumers | 28 fewer proof lines in the four ports; move helper and check further callers |
| Exact recorded-entry prefix reuse | Complete actual producer with unchanged header and callers | 20 fewer physical lines |
| Existing convergence APIs | Three convergence routes and the generic profile-update adapter | Estimated 25–35 fewer lines for convergence; no new machinery |
| Remaining handler projections | Three exact structural statements from current iff certificates | Estimated 45–53 fewer lines using in-owner support helpers; production pilot needed |
| Zero-mass posterior naturality | Generic result and complete actual accumulated-mass producer | Four real callers; small feature growth, not a large compression |
| Exact empty-processing law as owner | Complete existing law/segment/caller route inspected | Estimated 35–50 fewer lines after owner movement and module deletion; unpiloted |
| Three audit-continuation transports | Real primitive transport and three actual higher callers identified | Estimated 100–150 fewer lines including generic API/adapters; medium confidence, unpiloted |
| Four commitment interval descriptors | Four actual static blocks and existing indexed descriptor owner inspected | Estimated 20–30 fewer lines after helper and all four ports; unpiloted |
| Profile/expectation cleanup bundle | Existing owning APIs and generic update reuse checked | Estimated 15–30 fewer lines including adapters; complete migration unpiloted |
| Chance-aware graph confluence | Existing kernel commutation and stricter certificate gap inspected | Unproved feature; retain strategic policy stability and actual progress; semantic outcome only |

The three exact compression candidates concern disjoint owners and remove 90
lines in their checked proof substitutions. This is not a forecast for the
whole repository. Mathematical strengthening adds code; no large compression
factor or consolidation size target is established.

## Mathematical and semantic limits

Own cleanliness is local only after proving InputRecall at every actual
history. One arbitrary clean anchor is insufficient without that adapter.
Terminal payoff bounds must include native horizon exhaustion and unfinished
source/graph outcomes, including audit charges. Bounds on completed source
outcomes alone do not suffice.

Posterior naturality at zero mass holds because the current fallback is the
original law and mapping that fallback commutes with the readout. It does not
give a Bayes interpretation to a zero-mass fiber or apply to arbitrary unrelated
fallback choices.

The chance-confluence proposal concerns the existing store/semantic-outcome
observation. It does not preserve the full order-sensitive execution history,
physical receipts or clock. A public coin can change an unrelated strategic
policy; dependency independence alone does not supply policy stability.

The current large repair-induction match, broad contract merger, new symmetry
hierarchy and generic rank framework do not have a fresh complete saving pilot.
They are not included in the estimates. Source semantics and the result-family
consolidation still have their own owner decisions and adapter obligations.

## Reproduction and suggested order

Run the normal project build before the isolated experiments:

```powershell
lake build
python -m unittest discover -s scripts -p 'test_*.py'
python scripts/proof-inventory.py --output ephemeral/proof-review-current
python scripts/check-proof-review-probes.py
```

The [probe appendix](proof-review/checked-probes.md) contains nineteen temporary
modules: seven retained regression experiments and twelve candidate modules.
All 32 public theorems in the candidate modules have exact standard-axiom
guards. The actual compiler-tail owning modules have also been checked. Declaration
surfaces and complete generated inventories remain
under the ignored review artifact directory.

Verification passes: the ordinary build (5,767 jobs), all nineteen appendix
modules with their candidate axiom guards, both complete compiler-tail modules,
98 Python tests, module boundaries, source policy and documentation references.
The ordinary build still emits the already recorded optional premise-suggestion
metadata recursion diagnostic; kernel checking and the build succeed.

Implementation can start with exact API reuse and lower helper ownership,
then the normalized-weight and zero-safe posterior interfaces. The checked
source-splice and timing producers justify larger strengthening pilots; their
full downstream statements must be checked before claiming capstone results.
Combine the two count-support guard improvements only after completing the
actual all-history, bad-policy and safe-policy proof. Keep the larger audit and
confluence proposals only if complete consumer pilots confirm their cost and
scope.
