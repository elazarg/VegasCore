# Proof review and mathematical mining

The strongest opportunities are concentrated in repeated operational proof
families and in probability lemmas with unnecessarily global finite-carrier
assumptions. Several small generalizations are checked in isolated experiments;
the larger compression estimates still need production pilots. This review
does not establish a large compression factor or justify weakening any retained
compiler, Nash or sequential-equilibrium result.

## Scope and evidence

The measured source is the tree at `7272a57e`. The inventory covers **2,516
tracked Lean files and 618,853 physical lines**, including the separately
managed GameTheory dependency, its tests and its opt-in/experimental trees.
No production Lean declarations, options, submodule files, language semantics
or SE checklist statements were changed by this review.

Three independent reviewers covered mathematics, operational runtimes and
strategic proofs; the integration review covered source/compiler proofs,
examples, tests, dependency boundaries and consolidation implications.

| Area | Files | Physical lines | Lexical proof-body lines | Review detail |
| --- | ---: | ---: | ---: | --- |
| GameTheory, including package/aggregate files | 619 | 174,210 | 76,943 | [Mathematics](proof-review/mathematics.md) |
| GameTheoryExtensions and its tests | 90 | 17,226 | 7,717 | [Mathematics](proof-review/mathematics.md) |
| Interaction, its tests, EventGraph and Pending | 618 | 86,439 | 41,337 | [Runtime](proof-review/runtime.md) |
| Vegas.Game | 819 | 271,630 | 159,792 | [Strategic proofs](proof-review/games.md) |
| Foundation, Expr, Source and Compile | 272 | 45,220 | 19,045 | [Source/compiler](proof-review/source-and-compiler.md) |
| Examples, VegasTests, Paper and Vegas aggregates | 98 | 24,128 | 8,725 | [Source/compiler](proof-review/source-and-compiler.md) |
| **Total** | **2,516** | **618,853** | **313,559** | |

Coverage has two levels. Every tracked module and declaration surface was
inventoried and screened by family; selected difficult proofs and consumers
were read in depth. The detailed reports name the families and deep-read scope.
This is **not** a claim that every tactic in 313,559 body lines was manually
reviewed. The runtime ledger alone identifies 59 selected deep-read modules.
Counts in the detailed reports that exclude root aggregators have slightly
different denominators; the table above uses the common tracked-source tool.

The inventory detects 16,824 proof-bearing bodies and 4,694 distinct cross-file
matches of eight consecutive nonblank proof lines. Comments and whitespace are
normalized; identifier renaming is not. Matches overlap and include routine
tactic scaffolding. They are search leads, not removable-line counts. The
lexical parser includes tactic-valued definitions and is not Lean's AST.

Within this measurement, Vegas.Game and Vegas.Pending account for about 81%
of the lexical proof-body footprint outside GameTheory. That makes their
operational classification and state-transition interfaces more promising
compression targets than shortening isolated arithmetic proofs everywhere.

## Highest-priority compression work

The figures below are **estimated net physical source lines**, subtracting the
new common proof, all adapter hypotheses and caller changes. They overlap and
must not be summed. A checked scratch statement does not validate a savings
estimate for a production migration.

| Priority | Concrete change | Estimated net saving | Evidence and required next check |
| --- | --- | ---: | --- |
| 1 | Give accepted-event ownership one owner | About 48 | Two modules declare the same fully qualified theorem; deleting one proof and importing the other checks with its downstream proof unchanged |
| 2 | Classify owned-event completion once, retaining packet, receipt, decoded content and expiry facts | 250–450 | Five classifiers contain 743 measured body lines; first prove that the accepted branch supplies all current consumers' facts |
| 3 | Reuse automatic-drain traces for frame/invariant results | 150–280 | Existing drain trace lifts arbitrary predicates; extraction must retain the phase eligibility condition |
| 4 | Make ordinary exclusion evidence the zero-frontier suffix instance | 120–300 | Exact record equivalence checks; lower the common owner to avoid an import cycle |
| 5 | Share serial-prefix count verdict persistence and collection | 150–300 | Serial-prefix input stability checks; instantiate ordinary/recovery/phase observers without changing coverage quantifiers |
| 6 | Share discrete pushforward measurability/integration | 50–100 | Two primitives check on arbitrary target carriers; project-specific value equalities remain concrete obligations |
| 7 | Publish guarded absolute-expectation contraction | 70–120 | Both absolute and difference inequalities check with explicit integrability; do not use a total real expectation to hide undefined expectations |
| 8 | Make passage-based restriction completion the general owner | 130–230 | Existing subsumption application supports reuse; preserve rationality, beliefs and a common tremble sequence |
| 9 | Factor action translation in source repair/replay | 60–130 | Two large inductions share 94 overlapping windows; pilot the reveal legality/readback facts before the configuration relation |
| 10 | Reuse an initialized decoded-invariant induction | 35–55 | Three initial-invariant proofs contain 79 body lines; validate one generic induction and all three adapters |

Other worthwhile seams include the observation codec, reactive environment-step
eliminators, typed handler success/inversion facts, source residual embeddings,
mapped round congruence, continuation-gain algebra, strategic bridge coordinate
transport and discounted Bellman algebra. The detailed reports contain **55
ranked findings** and a further cleanup queue, with exact owners, premises,
proof routes, confidence and costs. No claim is made that these estimates imply
the consolidation size target.

The largest individual inventoried bodies are in qualified binding readback,
source alignment, replay coverage, fresh-terminal coupling and conditional gain
proofs. For example, the binding-row readback has 1,906 lexical body lines and
source replay alignment 1,747. Their size is a signal to improve dependent
provenance interfaces, not permission to replace factual callback/replay/receipt
identities by an assumed alignment record. Extract one constructor branch and
measure the whole result before planning a wholesale rewrite.

## Checked mathematical experiments

Seven isolated probe files, containing thirteen declarations, compiled with
the exact options copied from the central Lake setup. They use existing built
imports and no admissions or local option changes. They remain local review
experiments, not merged production APIs or new capstone guarantees.

| Experiment | Checked content | Consequence |
| --- | --- | --- |
| Proportional Bayes transport | Derive finite scale from proportional mass, a raw information antichain and positive source mass; prove the complete local scheduler Bayes projection without finite expanded histories | The local finite-history premise is unnecessary; global SE still has separate finiteness obligations |
| Expectation contraction | Absolute expectation is bounded by expected absolute value; the difference form follows with explicit integrability | Common probability API can replace bespoke decorrelation bounds |
| Discrete pushforward | A PMF-valued measurable pushforward gives AE measurability and the nonnegative integral identity | The target carrier need not be globally countable or finite; its PMF support is countable |
| Support order | Cross-support payoff order with additive slack survives two independent averages; recover the old zero-slack statement | A small genuine generic extraction, with only modest net compression |
| Event ownership reuse | Remove the duplicate owner theorem and use the existing owner in the unchanged opponent-completion proof | A concrete proof-deletion patch is validated in isolation |
| Runtime kernels | Ordinary exclusion record is suffix record at zero frontier; arbitrary invariants lift over the existing drain trace; earlier same-author inputs survive serial extension | Three small shared runtime kernels are valid without changing contracts |
| Parameterized source-protocol payoff | Preserve the full utility-vector law for an immutable initial parameter jointly with the public result | The missing parameterized source-protocol Nash adapter is close; its Nash statement was not proved in this review |

These experiments validate statements and local reuse. They do not prove that
all proposed consumers can be migrated at the estimated size, nor that every
new API should be retained after its first real application.

## Stronger and nearby unproved results

1. **Sharper continuation domination.** Charge probability loss only at active
   decisions. In single-mover protocols, replace a player-count-times-horizon
   exponent by the number of actual choices; unilateral changes can potentially
   count only the focal player's decisions. The product lower-bound API already
   accepts per-coordinate factors. The active/inactive marginal identities and
   adaptive continuation induction still need proof. This can improve bounds,
   not merely shorten scripts.
2. **Countable, uniformly tight consistency completion.** Replace global finite
   sites and fibers by countability plus uniform tightness, using the existing
   assessment compactness API. Strategy and belief sequences need their own
   tightness conditions. This is a local consistency theorem, not an
   infinite-game SE existence theorem.
3. **Integrable pooled outcomes.** Keep finitely many ranking components but
   replace finite outcome carriers by explicit integrability at the actual
   mixtures and conditionals. Supported conditional guards can often be derived
   from whole-law integrability. Do not drop the guard altogether.
4. **Finite-support purification over infinite alphabets.** Replace finite
   payload types by finite supported action laws along the explored frontier.
   Keep the single pure-policy mixture chosen before the initial draw. Arbitrary
   infinite behavioral products need not be representable by a discrete PMF.
5. **Player-memory joint realization.** Match the scheduler's joint execution /
   posterior-memory theorem for player implementations, conditioning on actual
   player recall. Preserve the private-memory/application-state distinction.
6. **Dependency-height completion bounds.** Instantiate the existing completion
   progress service using dependency height instead of the number of events.
   Keep physical service, expiry and retry accounting; a smaller graph rank
   alone does not bound an arbitrary builder's elapsed time.
7. **Conditioning and multiplicity-sensitive bounds.** Expose conditioning error
   in terms of excluded mass and counterpart bounds in terms of actual fiber
   multiplicity. Positive conditioning mass remains essential.
8. **Event-sensitive Nash error.** Derive a weighted sum of event deferral
   probabilities and event/player payoff oscillations instead of one global
   range. The local payoff replacement bound and expectation guards must be
   proved before composing the two deviation directions.
9. **Exact sound-detection boundary.** Prove the maximal detector and precise
   finite-deterrence criterion described by the enforcement documentation, or
   correct that prose to the current declarations. Uniform finite deposits over
   infinitely many deviations need a uniform gain/detection bound.
10. **Executable-payment auction.** Add a bounded-bid program with return
    expressions computing actual transfers, retaining the existing withholding
    counterexample. The old theorem quantifies over real forfeitures; an
    integer-transfer implementation must be an additional application, not a
    weaker replacement.

## Engineering and claim-quality findings

- **One theorem has two owners.** The event-handler ownership result is defined
  independently in two modules under the same full name. The checked build is
  not evidence that this is a good ownership boundary. The deletion probe
  supplies a direct repair without an alias or compatibility layer.
- **Descriptions exceed declared results in a few modules.** Enforcement prose
  describes exact detector/finite-deterrence conclusions absent from its current
  declarations; factored-likelihood prose describes a type-exclusion result not
  established in that module. These are theorem-inventory issues, not claims of
  an unsound kernel proof.
- **Certificates are not their constructors.** The restricted-extension
  approximation structure is used as a premise, with no constructor found in
  its owner; the factored-history certificate has no declaration consumer found
  by source search. A definition listing the hard obligations is not evidence
  that they have been discharged. Conversely, the near-product weights API has
  real derived bounds and a concrete model constructor and is useful reuse.
- **Module reachability is coarse.** A zero-unreached-module report can coexist
  with unused declarations, redundant private helpers and uninstantiated records.
  Do not automatically delete a mathematically useful public lemma because no
  current caller was found; give its purpose and proof a separate review.
- **Prefer general results before specializations.** Several finite/bounded
  wrappers reprove an argument already present in a more general theorem later
  in the same module. Reorder and instantiate, updating callers rather than
  retaining redundant names.
- **Keep separate operational quantifiers.** All-command invariants, fixed-
  scheduler supported-command invariants, legal-menu invariants and fixed-policy
  support invariants are different contracts. Reuse their constructors and
  lifting proofs without silently replacing one by another.

No new logical bug was found in the inspected bodies. This is a scoped review
finding, not a complete mathematical correctness certification of the codebase.

## Consolidation constraints preserved

The [consolidation ledger](consolidation.md) still governs semantics and result
ports. In particular:

- Requests in a retrying phase have attempt/event identity and a fresh physical
  readiness episode. A bare event identifier does not capture the same service
  obligation. A shared contract needs a proved adapter, not matching field names.
- Bounded activation/inclusion gaps do not imply all-view late-packet blindness.
  Reserved correlated tapes are not arbitrary adaptive timely builders.
- Rollback must retain observed traffic, serials, player/environment recall,
  receipts and canceled attempts. Clear/empty-archive repair frames cannot
  replace the fuller counted-history frames merely because they are shorter.
- A source image, true callback query, retained binding, historical window and
  replay origin are factual obligations. Do not hide them in the assumed
  conclusion of a proposed generic certificate.
- Fixed exit cash does not make exit utility constant without a valuation
  condition. Recovery cash inversion needs valuation recoverable from the
  retained readout; a clean audit alone does not establish that condition.
- None of the review results closes an SE checklist box, proves a common
  contract, establishes concurrent SE for arbitrary timely builders, or turns
  conditional withholding into dominant truthfulness.

## Recommended implementation sequence

1. Integrate the checked ownership deletion and expectation primitives, with
   one real caller each. Remove duplicates rather than add aliases. Measure net
   source size and owning builds after all adapters.
2. Remove the proved unnecessary local Bayes finiteness premise and specialize
   existing compactness/consistency machinery before inventing new machinery.
3. Pilot the rich completion classifier, decoded-invariant lifting, drain-trace
   reuse and count-audit serial kernel. These are the best larger reductions
   under fixed semantics. Keep their semantic regression tests.
4. Generalize the source-protocol observation reader once to cover correlated
   private parameters, then pursue finite-support purification and active-choice
   quantitative bounds as explicitly stronger theorems.
5. Tackle one dependent provenance constructor only after the earlier APIs have
   checked consumers. Revisit contract unification with those facts available;
   do not begin with a mass namespace move or an opaque new certificate hierarchy.

## Reproduction and validation

Run the inventory from the repository root:

```powershell
python scripts/proof-inventory.py --output ephemeral/proof-review
python lean-defs.py Vegas/Game Paper.lean -o ephemeral/proof-review/games-surface.txt
python lean-defs.py Vegas/Source Vegas/Compile -o ephemeral/proof-review/source-surfaces.txt
python scripts/check-proof-review-probes.py
python -m unittest discover -s scripts -p 'test_*.py'
```

The [checked-probe appendix](proof-review/checked-probes.md) contains the full
Lean source of all experiments. Its runner checks temporary modules using the
central Lake setup; `--list` and `--probe NAME` support focused replay.

The inventory writes module/declaration CSV files, exact-window locations and
JSON summary data locally. Physical sizes are reproducible; estimated savings
are not measurements. The test suite checks inventory behavior around blank
lines, comments, proof/definition separation and cross-file matching.

Validation includes the ordinary full VegasCore build and an explicit complete
GameTheory library build, plus the seven isolated probes and repository checks.
The GameTheory library build includes its opt-in/experimental submodules; the
ordinary VegasCore default build alone should not be described as validating
every optional dependency module. Detailed outcomes are recorded with the
review artifacts; no production API migration is implied by a scratch proof.

| Check | Outcome |
| --- | --- |
| Ordinary full VegasCore build | Pass, 5,733 jobs, including Paper axiom guards |
| Complete GameTheory library build | Pass, 4,284 jobs, including opt-in/experimental modules |
| Replayable central-option proof experiments | All seven files / thirteen declarations pass |
| Python regression suite, including inventory tests | All 94 tests pass |
| Module boundaries, source/option policy, documentation references and whitespace | Pass |
