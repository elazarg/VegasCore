# Sequential equilibrium across compilation

## Target and status

The credibility target is **Kreps-Wilson sequential equilibrium**: optimal
continuation play at every decision information set, with beliefs justified by
one common sequence of fully mixed behavioral profiles. Use GameTheory's
existing definition. Beliefs are mathematical analysis data; the executable
policy still receives only its player's observations and recall.

The source-to-native preservation theorem is open. The checked foundations are:

- [SequentialIncentives.lean](../GameTheoryExtensions/Protocol/SequentialIncentives.lean):
  exact, utility-independent transport of sequential rationality between fixed
  assessments, for finite observed outcomes.
- [Sequential.lean](../GameTheoryExtensions/Analysis/Protocol/Sequential.lean):
  for a consistent source assessment, preservation for all utilities is exactly
  target consistency plus inclusion of its incentive differences in the source
  cones. The theorem uses the existing equilibrium predicate and canonical
  assessment-induced continuation contexts.
- [SequentialCredibility.lean](../GameTheoryExtensionsTests/SequentialCredibility.lean):
  a hidden-bit game admits a behavioral SPE prescribing a strictly inferior
  off-path response. No belief system makes that profile sequentially rational.
  This tests the required strengthening, not a native compilation theorem.
- [Bayes.lean](../GameTheoryExtensions/Analysis/Protocol/Bayes.lean): full mixing
  gives every legal history positive reach probability. With finitely many
  players and a bounded horizon, it also implies finitely many legal histories.
  Finite decision fibers admit canonical Bayes assessments with positive mass.
- [SequentialBeliefs.lean](../GameTheoryExtensionsTests/SequentialBeliefs.lean)
  and [SequentialEquilibrium.lean](../GameTheoryExtensionsTests/SequentialEquilibrium.lean):
  explicit sequential equilibria with a genuinely unreachable information set,
  using one common fully mixed sequence for all strategies and beliefs.
- [SequentialDisclosure.lean](../GameTheoryExtensionsTests/SequentialDisclosure.lean):
  abstract disclosure defeats every utility-independent sequential-equilibrium
  translator, even allowing utility-dependent target beliefs. The source
  witness satisfies the actual sequential-equilibrium definition.
- [ReactiveDecisionInformation.lean](../Interaction/ReactiveDecisionInformation.lean):
  actual reactive decision fibers are nonterminal history antichains, for any
  application, scheduler and passive observation rule.
- [ReactiveSequential.lean](../Interaction/ReactiveSequential.lean) and its
  [Vegas specialization](../Vegas/Pending/ReactiveSequential.lean): the current
  arbitrary scratch-memory carrier prevents finite-support fully mixed play at
  any decision site. This is a mismatch with the finite assessment interface,
  not an impossibility theorem for sequential equilibrium in other models.

No runtime actions or observations are restricted by these modules. The
GameTheory submodule is unchanged.

## What the existing definition provides

| Existing API | Meaning | Adapter obligation |
|---|---|---|
| `InformationSite` | A legally reachable decision information state | Include sites reached after deviations, not only under the prescribed profile |
| `InformationHistory` | Complete histories in that information fiber | Retain private types, binding values, observations and actual remaining time |
| `BehavioralAssessment` | Behavioral policies plus a supported belief at each site | Strategies never receive the analyst's full history or belief witness |
| `continuationContext` | Belief-weighted execution with one whole policy replaced | Use original opponents and actual remaining opportunities |
| `IsSequentiallyRationalWithin` | No profitable whole continuation-policy replacement | Supply enough evaluation fuel for all legal continuations |
| `IsBayesConsistent` | Normalized history reach probabilities at positive-mass sites | Finite information fibers and a decision-history antichain |
| `IsSequentiallyConsistent` | Pointwise limit of fully mixed, Bayes-consistent assessments | Construct one sequence for all players and sites |
| `IsSequentialEquilibriumFor` | Sequential rationality and sequential consistency | Instantiate contexts with the assessment's own beliefs and runner |

Definitions are in GameTheory's
[BehavioralAssessment.lean](../GameTheory/GameTheory/Protocol/BehavioralAssessment.lean)
and [analytic bridge](../GameTheory/GameTheory/Analysis/Protocol/Sequential.lean).
Its EFG adapter supplies finite history fibers for finite tree-shaped games;
our operational adapters must establish their own finite-history facts.

The word "reached" in `InformationSite` means reachable by **some legal play**.
It does not permit discarding an information set because the equilibrium assigns
it probability zero. Zero-probability chance transitions are absent from legal
histories; nature's fixed prior and service laws are not player trembles.

The reactive adapter proves `InformationSite.AllNonterminal` and the decision
antichain property. At a decision, the observation includes the player's full
response record. Its own response increases that record's length, and later
steps retain the record as a prefix. Two decision histories with equal
observations therefore cannot be proper ancestors of one another. This uses
the actual adapter, which returns `none` while the player is inactive; it does
not assume the stronger global `PerfectRecall` predicate at inactive histories.

## Preservation statement and quantifiers

Fix a source game, runtime instance, initial type distribution and admissible
service. Fix **one playerwise compiler** `C_i`, independent of utilities,
opponents' policies and assessment beliefs. The proposed guarantee is:

> For every utility profile on original private types and public results, and
> every source sequential-equilibrium assessment `(sigma, mu)`, there exists a
> target belief system `nu` such that `(C sigma, nu)` is a target sequential
> equilibrium. Compilation also preserves the initialized joint law of types
> and public results for every source behavioral profile.

Here `C sigma` means coordinatewise compilation. Its behavior must be defined
at every target decision information set, including histories produced by
earlier deviations of its own player or of opponents. A proof may inspect the
whole source assessment to construct target beliefs; compiled player code may
not use that access.

For a service class, choose the compiler before quantifying over the service
members. Beliefs may depend on the fixed service law. A compiler parameterized
by a publicly configured service is a different, explicitly parameterized
claim. Neither statement makes the scheduler a utility-maximizing player.

A stronger, useful sufficient interface constructs one target assessment from
each consistent source assessment **before** choosing utilities. Its exact
criterion is checked below. This stronger quantifier order must not be called
necessary for the more permissive statement above, where target beliefs may
depend on the utility being analyzed. Initialized law preservation is a
separate requirement in both cases.

## Exact incentive boundary

For assessment `A`, player `i`, decision site `I` and whole replacement policy
$\tau_i$, let `P(A,i,I)` be the observed continuation law under the prescribed
profile, starting from `A`'s belief at `I`. Let `D(A,i,I,tau_i)` be the same law
with player `i` replaced. Sequential rationality is exactly

```
E[D(A,i,I,tau_i)] u_i <= E[P(A,i,I)] u_i
```

for every player, site and replacement. Beliefs stay fixed in this comparison;
the player chooses a continuation, not a new explanation of the past.

For finite observed outcomes, form each signed vector `P - D`. The checked
criterion for fixed source and target assessments is inclusion of every target
vector in the closed convex cone generated by the source vectors for that
player. No history-by-history maximization, single source-site decoding, or
equality of baseline laws is required by this exact incentive criterion.

If the source assessment is consistent, uniform sequential-equilibrium
preservation holds **iff** the target assessment is consistent and these cone
inclusions hold. Necessity of consistency follows by taking all utilities zero;
the remaining equivalence uses the checked cone separation theorem. Consistency
is independent of utilities. This is a semantic characterization for fixed
assessments, not a weakest miner contract or a decision procedure.

The generic theorems accept explicit finite evaluation fuel. Runtime adapters
must supply a global legal-history bound and establish independence of larger
sufficient fuel. Evaluation fuel must never reset an operational deadline.

## Belief transport: the substantial new proof

A source witness gives fully mixed profiles $\sigma_n$, their Bayes beliefs
$\mu_n$, and a joint limit `(sigma, mu)`. The proposed constructive proof has
four obligations:

1. Build target profiles $\tau_n$ that give every **legal target choice** positive
   probability, including choices outside the compiler's image. Keep chance,
   the type prior, observation rule and scheduler fixed.
2. Derive target beliefs from target history reach probabilities. Prove positive
   information mass at every legal decision site under full mixing; do not
   leave zero-mass fallback beliefs doing the work.
3. Prove $\tau_n$ converges to the actual compiled profile, and all target Bayes
   beliefs converge along the **same sequence** to `nu`.
4. Establish the target continuation incentive condition under that `nu`,
   including sites reached after multiple players' deviations. Sequential
   rationality is required of the limiting assessment; the approximants need
   not themselves be equilibria.

The generic positive-mass and Bayes construction in step 2 is checked. Steps
1, 3 and 4 remain compiler-specific construction obligations. It is insufficient
to compile each
$\sigma_n$ verbatim: that need not randomize over target-only actions. Adding
uniform noise without analyzing conditional probabilities is also insufficient.
The relative rates at which different mistakes vanish determine off-path
beliefs. Do not choose a convenient posterior independently at each site, or
allow a target replacement to see the sampled complete history.

Use belief-weighted continuation law simulations as a tractable sufficient
proof method, with cone inclusion as the exact incentive test when matching
whole laws is unnecessarily strong. Any mixture over source sites must justify
its conditional source beliefs, preserve the same player's opponents, and
choose its weights independently of that player's proposed replacement.

### Checked off-path assessment and disclosure boundary

Chance samples a uniform bit and shows it to Alice. Alice stops or asks Bob;
Bob guesses without seeing the bit. The prescribed profile stops and would
guess `true`. For the consistency witness, each player independently switches
its prescribed action with probability `1 / (n + 2)` at every decision site.
Alice's asking probability is the same for both bits, so each Bob history has
reach probability `1 / (2 * (n + 2))`. Bob's information mass tends to zero,
but his Bayes posterior stays uniform. Alice's decision beliefs are singletons.
The complete sequence converges in every strategy and belief coordinate.

Two rationality tests use that same consistency witness. When Bob receives
one for `true` and zero for `false`, the prescribed continuation is optimal,
even though Bob is never asked. When Bob is rewarded for matching the hidden
bit, or instead for mismatching it, every continuation guess has expected
payoff `1/2`. Alice receives zero throughout. Thus the same assessment is a
sequential equilibrium for both opposite guessing utilities.

Now reveal the actual bit to Bob when Alice asks. Each Bob information fiber
is a singleton, so even arbitrarily chosen beliefs cannot hide it. At bit
`false`, rationality for matching requires payoff at least one from guessing
`false`; rationality for mismatching requires payoff at least one from guessing
`true`. The two prescribed payoffs sum to one. No target strategy can therefore
admit rational assessments for both utilities, even with different beliefs.

This rules out every utility-independent translator for these two games,
including translators with access to the whole source profile. The existing
[law-preserving compiler](../GameTheoryExtensionsTests/OffPathDisclosureLaws.lean)
still preserves initialized joint type/result laws for every source profile.
Sequential consistency does not remove the extra-information obstruction.
This is a preservation impossibility, not an equilibrium-existence claim or a
native runtime counterexample. A runtime application must prove that its
observations actually implement this disclosure before using the negative result.

## Finite games without restricting private computation

`FinDist` has finite support. The new `FullSupport.finite` theorem proves that a
fully supported such law requires a finite carrier. A finite horizon does not
make the current action menu finite: `ResponseMemory.privateData` alone can
store any natural number. At a decision site, this injects the naturals into
the legal response menu. Raw submissions and replay identifiers also require
an audit after scratch memory is separated.

The recommended first theorem is a **family of explicitly finite runtime
instances**, with finite wire alphabets, finite semantic value domains where
needed, finitely many principals and a certified horizon. These are premises
of the runtime theorem, not new opcodes or an equilibrium flag in source syntax.
Do not equate bounded payload sizes with bounded local computation.

| Approach | Benefit | Obligation or cost | Decision |
|---|---|---|---|
| Finite runtime instances | Reuses the existing standard definition | Explicit domain/encoding bounds; all legal messages within each bound remain available | First implementation target |
| Finite semantic quotient of raw runtime | Can cover an unbounded representation | Prove information, deviations, beliefs and tremble lifting, not only initialized outcomes | Optional optimization after a concrete quotient is justified |
| Countable or general distribution model | Retains genuinely infinite menus | New probability/conditioning and consistency theory; hypotheses depend on the chosen generalization | Separate research task if finiteness is unacceptable |
| Full mixing only over compiler outputs | Simplifies perturbations | Omits genuine target deviations | Reject |

Wire bounds have a possible engineering justification in finite transaction
encodings and execution horizons. This is **not a modeled blockchain theorem**.
Exact bounds, feasibility of the service, fees and enforcement require a concrete
backend. A theorem for each finite instance does not establish a theorem for
the unbounded union of instances.

Keep auxiliary implementation memory within strategies if a continuation-aware
realization proof justifies it. The existing
[PrivateStrategy.realize](../GameTheoryExtensions/Protocol/PrivateStrategy.lean)
preserves external laws against adaptive environments, but does not prove
transport of off-path beliefs or sequential rationality after fixing an
internal memory state. That missing step is explicit. Private types and binding
commitment meanings have semantic effects and cannot be erased as scratch data.

Nor can all malformed packets simply be identified with silence: their visible
contents may communicate information or influence the service. Any restriction
that removes partial foreign leaks, pre-inclusion reactions or meaningful
communication requires discussion before implementation.

## Runtime obligations and ownership

| Layer | Work belonging here |
|---|---|
| `GameTheoryExtensions/Protocol` | Assessment continuation laws, recall/antichain adapters, incentive comparisons, whole-policy deviation transport |
| `GameTheoryExtensions/Analysis/Protocol` | Pointwise convergence, Bayes/perturbation lifting, sequential consistency and preservation theorems |
| `Interaction` | Finite response/packet interfaces, passive observations, public-history service, at-most-once inclusion, legal-history and view laws |
| `Vegas/EventGraph` | Source assessment adapter, persistent type/result observation, source decision recall and horizon |
| `Vegas/Pending` | Binding submissions, accepted-receipt recovery, native assessment adapter and dependency/service certificates |
| `Vegas/Compile` | Playerwise translation and instantiation of the generic transfer theorem |

Use proof hypotheses for service guarantees and semantic capabilities. Avoid a
boolean "preserve sequential equilibrium" option, a second equilibrium definition,
or carrying belief calculations in executable policies. A future optimization
should prove which continuation and consistency facts it preserves. Forfeiture
elision remains such a separate obligation; retaining source forfeiture is the
initial candidate, not an established sufficient condition.

The existing [obstruction inventory](spe-obstructions.md) remains useful evidence
about information, opportunities and recovery. Each negative result must be
rechecked for a source **sequential** equilibrium before being advertised as a
sequential-equilibrium counterexample. A source SPE counterexample alone does
not establish that stronger impossibility. Likewise, local inclusion regularity
has no proved implication for conditional continuation incentives or beliefs.

## Acceptance gates and implementation order

1. **Definition regression (checked):** SPE/credibility separation, positive
   sequential-equilibrium assessments with genuinely off-path beliefs and an
   explicit common consistency witness, and the abstract disclosure impossibility.
2. **Finite presentation:** implement the smallest reactive finite instance
   preserving binding, passive partial foreign leaks, repeated responses and
   at-most-once inclusion. Nonterminal fibers and decision antichains are checked
   for the actual reactive adapter. The generic finite-history theorem is ready;
   a finite response presentation and its player-memory justification remain open.
3. **Belief construction:** identity translation, a redundant private-bit
   extension, and a message encoding with target-only errors. Prove one common
   tremble sequence and posterior convergence; include an incompatible-beliefs
   negative regression. Neither identity nor private-memory realization alone
   validates the message encoding case.
4. **Continuation simulation:** test recovery after earlier own deviations,
   disclosure failures, partial observations, competing commitments and actual
   remaining deadlines. Audit the prior SPE witnesses under sequential
   rationality. Record any required extra source capability separately.
5. **Compiler theorem:** combine initialized joint-law correctness, consistency
   lifting and the incentive criterion for one playerwise compiler. Then compare
   operational service assumptions and their engineering justification.

Only the checked foundations listed at the start are established. There is no
claim here of native sequential-equilibrium preservation, equilibrium existence
for the raw infinite runtime, a general decision procedure, or a verified EVM.

## Research informing the design

- Kreps and Wilson, [Sequential Equilibria](https://www.gsb.stanford.edu/faculty-research/publications/sequential-equilibrium)
  (1982): assessments combine strategies and beliefs, with rationality at
  information sets including off-path ones. GameTheory's limit interface is the
  definition used here; ordinary subgame boundaries are not the coverage test.
- Halpern, Pass and Seeman,
  [Computational Extensive-Form Games](https://www.cs.cornell.edu/home/halpern/papers/kuhn.pdf),
  Definition 3.4 and Theorem 4.5: representation conditions support a
  computational sequential-equilibrium preservation result. Their history map
  preserves depth and the mover, and their equilibrium handles computational
  information. Our extra network activations and exact information model do
  not satisfy that setup automatically. This is a useful separation of
  representation and strategic proofs, not a theorem we can directly apply.
- Geffner and Halpern,
  [Communication games, sequential equilibrium, and mediators](https://arxiv.org/abs/2309.14618),
  Section 6 and Appendix A: communication protocols can be analyzed using
  sequential equilibrium, with explicit treatment of scheduling. Their
  asynchronous scheduler controls deliveries and recalls them; our passive-leak
  service deliberately has different observations. Their results do not supply
  our service assumptions or compiler theorem.
- Dilmé,
  [A characterization of consistent assessments using power sequences of strategy profiles](https://doi.org/10.1007/s00182-023-00874-z),
  Theorem 3.1 and Proposition 4.2: finite-game consistency admits power-sequence
  witnesses, including integer exponents. This suggests checkable relative-rate
  certificates for small experiments. It is not formalized here, and no global
  uniform tremble rate or automatic compiler check follows from citing it.

The finite-instance and certificate architecture above is our design proposal;
it is not attributed to these sources as a ready-made runtime construction.
