# Proof-library refactoring and strengthening

All sixteen findings are addressed in checked production owners and actual
consumers. The [implementation ledger](proof-review-progress.md#current-findings)
records each result. GameTheory source and its gitlink remain unchanged.
Source/runtime execution rules, central Lean options and the fixed SE checklist
are unchanged.

## Mathematical results

### Product timing error

`Vegas.TurnTiming.deferralError` is

```
1 - product(event, 1 - timing.deferral(event)).
```

The actual initialized execution law retains each first-turn branch with its
original mass. Composing those law lower bounds retains the product; no
additional statistical-independence premise is introduced. The error lies in
[0,1] and is at most the sum of event deferrals. Two deferrals of 0.2 give 0.36
rather than 0.4.

[ServiceTimingCoupling](../Vegas/Game/ServiceTimingCoupling.lean) exposes the
actual one-event and whole-run lower bounds and their TV consequence. The
[settlement](../Vegas/Game/SourceServiceTurnSettlement.lean),
[per-player best-response](../Vegas/Game/AsyncServiceNash.lean),
[raw Nash](../Vegas/Game/AsyncServiceRawNash.lean), intended/opening and
[actual-payment](../Vegas/Game/ProgramPaymentAsyncNash.lean) consumers use the
same error, including Paper's public statements. The two-way Nash loss remains
`epsilon + 2 * error * range`, with all original charged/uncharged payoff,
unfinished-readout, admissibility and integrability guards.

### Conditional-public-prior recovery SE

The actual recovery pipeline and
`Vegas.Paper.recovery_intended_raw_sequential_equilibrium` accept initial
private inputs independent given a publicly determined initial signal. The
public-signal property says that agreement on every public compiled initial
input determines the signal. Actual source-cell and native-view facts derive
that equality at the splice; callers do not assume the desired repaired law.

The [recovery root](../Vegas/Game/RecoverySequentialCompilation.lean) retains
the full source/native equilibrium, arbitrary admitted deviations, runtime
contracts, payoff bounds, absence of equilibrium-path charges and joint
settlement/readout conclusion. A constant Unit signal recovers the original
unconditional-input scope. The [correlated-prior regression](../VegasTests/ConditionalPublicPrior.lean)
has a noisy public bit: it satisfies the conditional guards and fails
unconditional independence.

This strengthens an existing recovery environment. The concurrent reserved-tape
and adaptive recovery guarantees retain their distinct assumptions. No fixed
SE obligation or operational rule is changed.

### Sharp normalization and total posterior naturality

Equal-total real weight vectors satisfy

```
|sum p*f - sum q*f| <= (sum |p-q|)/2,  when 0 <= f <= 1.
```

The separate unequal-total L1 theorem is retained. Added nonnegative mass at
most rho times a positive base mass costs at most `2*rho/(1+rho)` in L1.
[SwapTransport](../GameTheoryExtensions/Math/Probability/SwapTransport.lean)
combines these into `2*rho/(1+rho) + 2*eps/(1-eps)`; the product/projected-belief
and actual operational-record formulas and limit proofs use the stronger
bounds. Positive normalizers and the original relative-error guards remain.

[NestedPosterior](../GameTheoryExtensions/Math/Probability/NestedPosterior.lean)
proves posterior/readout naturality for every observation. At zero mass the
existing fallback is the input law, and mapping that fallback commutes with the
readout. This supplies no Bayes interpretation of null fibers and does not
cover arbitrary unrelated fallback laws. All four actual mass-identity callers
are migrated; support facts needed by genuine posterior interpretations remain.

## All sixteen findings

| Finding | Production result |
| --- | --- |
| Product-retention timing error | Full-run domination, bounded product error and all law/Nash/payment/public ports |
| Conditional public-source splicing | Actual public-cell bridge through the full recovery SE and public capstone |
| Sharper normalized comparisons | Half-L1, saturating contamination, full combined bounds and actual client/limit ports |
| Information-local own cleanliness | Actual count-support theorem consumes the player's remembered outputs; InputRecall supplies every history in the fiber |
| Terminal-only audit payoff bounds | Actual bad/safe laws and arbitrary-alternative context integrate from bounds on protocol terminals |
| Six compiler tail-order consumers | Existing tail-order API, 42 fewer physical lines, unchanged statements |
| Lower source raw-result ownership | Existing exact eliminator in the primitive owner, four consumer ports, 28 fewer lines |
| Exact recorded-entry prefix reuse | Exact ordered recall split preserved; 20 fewer lines |
| Existing convergence APIs | Three complete consumers reuse core PMF convergence; 24 fewer lines |
| Remaining handler projections | Exact acceptance certificates supply all three graph-state projections; 49 fewer lines |
| Zero-mass posterior naturality | Total readout naturality and all four actual mass-identity clients |
| Exact empty-processing law as owner | One full-execution owner derives the segment law; retired duplicate module, 37 fewer lines including umbrella |
| Three audit-continuation transports | One actual earlier-input transport and three direct higher clients; 177 fewer lines including umbrella |
| Four commitment interval descriptors | One indexed/interval owner and all four actual consumers; 27 fewer lines |
| Profile/expectation cleanup bundle | Existing update, scalar expectation and finite-support APIs; 29 fewer lines |
| Chance-aware graph confluence | Optional actors, actual action stability and adaptive scheduling over the existing semantic observation |

Whole-family measurements include common APIs and adapters. They are not
inferences from overlapping duplicate windows. Mathematical strengthening can
add code; a short call site alone is not a compression measurement.

The complete physical-source comparison with review checkpoint `610ae97f` is:

| Scope | Net lines |
| --- | ---: |
| Library, including common APIs and aggregators | −16 |
| Existing examples | −24 |
| Regressions and test aggregators | +338 |
| Paper | +308 |

Paper's increase includes 306 lines for 51 exact axiom guards. Proof reuse
removes substantial local duplication while the mathematical extensions keep
the overall library footprint nearly unchanged. This establishes no large
compression factor or completed semantic consolidation.

## Important scope boundaries

Own cleanliness follows from actual InputRecall. A clean arbitrary anchor
without that invariant is insufficient. The [generic transport](../Interaction/ReactiveAuditContinuation.lean)
retains the actual signed record and complete earlier same-author context;
observation and conditional-delivery coverage stay in the three real audit
adapters. Neither independence of delivery nor a final collection law is
assumed as a substitute.

Terminal bounds cover actual protocol terminal histories, including exhausted
horizons and unfinished source/graph outcomes with audit charges. The
[terminal regression](../InteractionTests/TerminalAudit.lean) has unbounded
nonterminal rewards, a charged exhausted terminal and an integrable actual
continuation context for every replacement policy. A completed-source-only
bound would be insufficient.

Chance confluence preserves the existing typed store/semantic-key observation.
It retains no-common-actual-actor, normalized-action stability, actual progress
and sufficient remaining fuel. It does not assert equality of order-sensitive
execution histories, receipts or clocks. The [chance regression](../VegasTests/ChanceScheduling.lean)
uses two nondegenerate sampled Booleans and an actual supported public-coin
policy obstruction; data-dependency independence alone does not ensure policy
stability.

Event-specific payoff sensitivity and omission of a deviator's own timing
factors remain separate refinements. Neither follows from the uniform product
bound. A common service contract, broad simulation certificate or generic rank
hierarchy has no demonstrated additional compression and is not introduced.

## Evidence and reproduction

The [mathematics](proof-review/mathematics.md),
[runtime](proof-review/runtime.md), [strategic](proof-review/games.md) and
[source/compiler](proof-review/source-and-compiler.md) reports give the owning
APIs, consumer scopes, measurements and limitations. The original review
screened 2,549 tracked Lean files and selectively read complete proofs; it was
not a line-by-line audit of all 619,625 physical lines.

The lexical inventory scanner excludes assignments in result-type let/have
bindings. Equation-style body coverage remains incomplete; its corrected
3,705 eight-line windows are search leads, not removable lines or a comparison
with older body counts. The documentation checker includes the actual game
regression library and rejects stale references there.

```powershell
lake build
python scripts/check-module-boundaries.py
python scripts/check-lean-options.py
python scripts/check-doc-references.py
python -m unittest discover -s scripts -p 'test_*.py'
python scripts/check-proof-review-probes.py
```

The [appendix](proof-review/checked-probes.md) replays twenty isolated
experiments, including actual production API replays and the full unconditional
recovery specialization. All 33 public candidate-probe theorems retain exact
axiom guards. The normal build passes all 5,771 jobs. Twenty probes, the full unconditional
recovery specialization, 60 exact standard-axiom roots and all 100 Python tests
pass. Fifty-one permanent production guards pin the new and strengthened roots. The
existing optional premise-suggestion metadata recursion diagnostic persists
independently of successful kernel checks and builds.
