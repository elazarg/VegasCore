# Sequential-equilibrium compiler: theorem, inference and boundaries

This is the results map and reading guide for SE compilation. The
[ideal-sanctions proof](research/se-ideal-sanctions.md) contains the generic
mathematics; the [native pilot](research/se-native-pilot.md) contains the checked
source-to-runtime instance. The general action-restriction theorem and scalar
deposit inference are checked in Lean. The
[general revelation compiler](../Vegas/Game/RevealServiceSignedCompilation.lean)
instantiates the staged theorem end to end for arbitrary finite reveal sequences,
with repeated owners, correlated valid initial bindings and all source
withholding choices. Arbitrary activation rosters and fresh source commitments
remain outside that result.
The [stack and implementation plan](se-compilation-stack.md) records proof edges
and the remaining service and language boundaries.

## Checked results and remaining compiler work

| Result | Scope |
| --- | --- |
| General SE extension | Every source SE extends across a structural action restriction satisfying the conditional enforcement bounds. Preserves retained strategies, beliefs, and joint completed-history/net-payoff laws. |
| Scalar deposit inference | Executably computes the least nonnegative deposit for a finite rational comparison table, or identifies an infeasible row. This decides the certificate, not semantic SE implementability. |
| Native guessing compiler | Every SE of the stated source program has a native SE under the fixed bounded service, partial monitoring and collectible charge. Includes a fixed playerwise policy translation. |
| Declared-payoff family | Every SE of the literal two-reveal source program, for any integer payoff table with zero watcher payoff, has a full bounded raw native SE with the exact joint initial-bit/result/net-payoff law. Both opening and withholding are retained. |
| General revelation compiler | Every SE of an arbitrary finite reveal sequence has a full bounded raw native SE preserving the joint typed terminal-state/net-payoff law, under the explicit owner/watcher service and positive monitoring coverage. |
| Terminal-audit compiler | A direct source → C → effective → raw theorem uses authentic partial traffic records and fixed deposits for all players, with no zero-utility reporter. The exact realized settlement law is preserved. Its calendar remains the specified revelation service. |
| Signed-evidence compiler | Source → C → public-replay menu → effective → raw preserves the exact joint typed-state/realized-settlement law. The sampled evidence contains phase, prior ledger and signed envelope, with no broadcaster field. Coverage, authentic context and collectible account penalties remain assumptions. |
| Concrete strategic stack | Source → C → W → N → raw is checked for arbitrary revelation sequences. All native games share the runtime and utility; deposits are fixed from actual finite watched-history payoff extrema before choosing the source equilibrium. |
| Reusable monitoring step | A watcher uses ordinary pending observations and replay; public at-most-once inclusion turns the sampling bound into persistent evidence under arbitrary later policies. Reporting a differently addressed packet before the current public event completes records its rejection. |
| Source correspondence | Service-block induction, replay recall, one common consistency sequence and conditional incentives establish the arbitrary-length revelation theorem. |
| Harmless public replay extension | Every retained SE extends to a menu permitting auxiliary-player public replays, for arbitrary application-state utilities. Exact continuation laws and all-legal-history counterparts are checked; no fine or reporter indifference is needed for this edge. |
| General-roster source prefixes | Every actual legal decision starts from an initialized legal source prefix; own recall identifies its depth. The compiled policy has the exact source-prefix state law for arbitrary timing distributions. Full auxiliary coupling includes pending observations, inclusion, ticks and expiry. Multi-phase source beliefs and sequential incentives remain open. |
| Fresh commitment blocks | Actual atomic binding and reserved inclusion preserve typed source-store and decoded source-history agreement. Paired blocks carry the source hidden-binding repair invariant and the actual native joint observation law. The stopped native continuation induction remains open. |
| Guarded source actions | Failed disclosure and withholding can erase different private intentions into the same native behavior. Their SE aggregation must preserve private correlations and a common perturbation sequence. Operational correspondence does not discharge this remaining source-to-retained-runtime gate. |
| Private-intention normalization | A fixed playerwise behavioral normalizer preserves joint initial parameters and typed outcomes. Actual prefix laws restore original private intentions with observation-local posterior weights. Information-fiber conditioning and continuation lifting remain before applying the checked common-sequence SE limit theorem. |
| Required-binding enforcement | Public completion without an accepted handle certifies omission and persists under arbitrary native continuations. The actual protected binding deadline produces this evidence when no required submission arrives. Partial packet samples alone cannot certify omission; the full stopped continuation comparison remains open. |

The central proof is
[`sequential_equilibrium_extends_of_continuation`](../GameTheoryExtensions/Analysis/Protocol/RestrictionExtension.lean).
Its premises describe execution and actual continuation values; they do not
assume a target equilibrium, a rational completion, or belief preservation.
Under every paired profile and finite posterior, each additional target choice
must be bounded by one whole legal source continuation. That policy may depend
on the posterior, but cannot be selected separately at each hidden history.
This permits repairs that change later choices, such as replacing an unusable
binding by a valid value and later withholding. Instantiating that repair for
native execution remains a separate obligation.

The `sequential_equilibrium_extends_of_comparator` specialization uses a fixed
source-legal local lottery whose value dominates at every hidden history.
It permits harmless undetectable actions. The simpler
`sequential_equilibrium_extends` corollary derives comparison from payoff bounds
and collection.
The [multiplayer regression](../GameTheoryExtensionsTests/RestrictionEnforcement.lean)
instantiates that corollary: Alice can depart into a new Bob decision, where Bob
prefers the response benefiting both players. A fixed charge of one preserves
every source SE, and source equilibrium existence makes the result nonvacuous.

## Compiler contract

Fix a source program, its declared utilities, initial distribution, backend
service and observation rules. Compile one native game, including any inferred
deposits, before choosing a source equilibrium. The primary theorem is:

> Every source SE has a native SE with the same joint initial-type,
> public-result and actual net-payoff law.

The structural proof additionally extends source behavior and beliefs at retained
information sets. Additional native equilibria are allowed. Equality of the two
sets of SE outcome laws is a stronger, separate property: even dominated added
actions can change off-path beliefs and create additional equilibria.

Compiling the game and translating player policies are distinct tasks. Generic
continuation completion can depend on the whole source assessment. It therefore
does not yet supply a fixed playerwise policy compiler, although the native
guessing pilot has one. Do not claim executable strategy synthesis from a
noncomputable equilibrium-existence proof.

The compiler may inspect declared utilities to select deposits. If a theorem
instead ranges over arbitrary external utilities, it must specify their bounds
or another common incentive certificate. A monetary deduction has the claimed
utility effect only under the stated preference model.

## Program artifacts and strategic proof stack

```text
SourceProgram + Setup + declared payoffs
                 |
                 v
              EventGraph
                 |
                 v
Pending-message application + specified native service
```

The native service specifies observations, inclusion, deadlines, bounded
responses, and any monitoring and collection mechanism. It is a backend
parameter, not a language in which the programmer rewrites the game.

The command-policy service used by the Nash/Bayesian theorem and the reactive
service used for SE are backend instances. A proof for one is not an
intermediate SE edge to the other. Concrete cryptographic or ledger execution
would require its own refinement beyond this idealized target.

The [strategic proof stack](se-compilation-stack.md#stack-one-runtime-several-strategic-games)
uses genuine response-menu restrictions of this same runtime:

```text
Ordinary source
  → source-representable native choices
  → harmless public-replay choices
  → all effective native choices, with terminal audit and fixed deposits
  → full bounded raw native game
```

The terminal-audit theorem applies the enforcement edge to every player at once.
Its auxiliary player can have any source utility; passive player observations
need no coverage bound. Instead, the settlement oracle supplies authentic
partial traffic records with the specified conditional coverage. The current
signed checker needs authentic transmission phase, prior ledger and signed
envelope. It permits harmless public replays and charges the signing account
for forbidden fresh traffic; it needs no physical-broadcaster attribution.
Signatures alone do not authenticate the reported phase or ledger context.
Collection is an economic/backend assumption, not an implemented escrow.

The final edge restores only proved private response aliases. All these games
use the same runtime and enforcement configuration; they add no source syntax
or emitted interpreter. Their composition is checked for arbitrary finite
revelation sequences, with correlated valid initialization. The fixed real
range-based deposits are sufficient, not claimed minimal or executable.

The separate [strategic-reporting compiler](../Vegas/Game/RevealServiceCompilation.lean)
uses an intermediate game with prescribed reporting. It restores ordinary
players' choices first, then the reporter's choices under identically zero
reporter utility. That implementation requires passive sampling coverage and
protected report inclusion. Its assumptions must not be combined implicitly
with those of the terminal-audit theorem.

Both instances retain the specified owner and auxiliary-player activation
calendar. Extending it needs a new correspondence proof: a pending message that
a later player can read cannot be classified as harmless merely because
inclusion ignores it. Fresh bindings also require native continuation repair
for privately unusable commitments; public auditing alone cannot identify them.

Ambient communication is an alternative source interpretation when a capability
must be retained. It is not automatically inserted to make an ordinary-source
preservation claim true. A compiler diagnosis must identify the capability and
the resulting change to the game's strategic meaning.

## Three proof obligations

### 1. Identify permitted native behavior with the source

Relate initialization, legal alternatives, information and chance laws at every
retained decision, including source withholding and admitted failure. Preserve
the joint terminal law. Forced service steps may be erased only with a proof
that their observations and timing do not change the decisions being compared.

Implement this as a relation between the existing protocols and their histories.
A narrower information menu alone is invalid: execution legality and the
resulting history space must agree. Source-to-graph correctness, completion of
the service, and the existing reactive policy translation are ingredients;
their initialized laws alone do not discharge continuation correspondence.

Every bounded raw native response must have an account: source behavior, a
proved alias, or an extra choice handled by an incentive argument. An alias
proof cannot erase different publicly visible packets merely because their
application effects match.

### 2. Establish conditional incentive bounds for extra choices

At every retained information set, show that an extra action is no better than
some legal source alternative after accounting for collectible loss. The bound
must respect the player's information and use additional future loss; an
already inevitable one-time charge supplies no fresh incentive.

The simple sufficient certificate is bounded base gain and a uniform positive
conditional collection probability. A sharper certificate compares actual
continuation gains and collection together, admitting harmless undetectable
actions. It need not catch every extra action or prevent every leak.

Soundness applies to all permitted source behavior, not just a selected profile.
Attribution, reporting, timely adjudication and remaining collateral must be
established separately. Ordinary passive sampling does not establish collection.
A mechanical reporting rule and an equilibrium of strategic reporters are
different implementations with different proofs.

### 3. Construct one consistent, rational completion

Pin a source consistency sequence, make forbidden trembles sufficiently rare
relative to compliant-history reach, and complete the other information sets
jointly. Preserve retained beliefs and apply the posterior one-shot principle
to whole continuation policies. After a departure, behavior is allowed to differ
from source behavior and must be rational with the information actually received.

The complete bridge is checked. A local operational square in
[`ActionRestriction`](../GameTheoryExtensions/Protocol/ActionRestriction.lean)
implies continuation-law correspondence. Rare forbidden trembles retain a
multiplicative share of each source history's probability; choosing their rate
relative to source information-set reach preserves even off-path beliefs.
One common completion solves all new information sites, and the conditional
incentive bounds and one-shot principle establish whole-policy rationality.

The current structural theorem preserves step counts and active players, and
assumes finite histories, decision-site recall, common-depth information sets and a
sufficient horizon. It permits additional actions, histories and information
sets. Extra service activations must first be aligned with forced source steps
or eliminated by a separate correspondence proof. This is an obligation in
connecting the ordinary source protocol to the native service calendar.

The recall compatibility proof is checked. The capstone uses
[decision-site recall](../GameTheoryExtensions/Protocol/DecisionRecall.lean),
and every reactive menu satisfies it with the existing native observations.
Inactive information may remain empty. Common decision depth must separately
follow from the service calendar and existing observations.

[Pointwise menu inclusion](../Interaction/ReactiveMenuRestriction.lean) now
constructs the structural action restriction, retaining every observation and
the execution law under arbitrary policies. The
[public ledger audit](../Interaction/ReactiveLedgerConformance.lean) proves
detection and persistence of included nonconforming packets. Its
[native regression](../VegasTests/MonitoredGuessingConformance.lean) checks an
accepted disclosure missed by the pilot's charge. These are compiler ingredients;
full response coverage, collection and source assessment transport remain open.

## Inference rather than compiler flags

The intended compiler result consists of the ordinary compiled program, an
enforcement configuration, a preservation certificate and an explicit list of
backend assumptions. Game-specific analysis chooses the configuration; the core
language does not need a separate syntax option for each obstruction.

For finite rational comparison data, collect inequalities

`gain_k <= collection_k * deposit`.

Here the two coefficients describe the same conditional comparison. With
nonnegative collection coefficients, a zero coefficient requires a nonpositive
gain. Otherwise the least sufficient nonnegative deposit for this certificate is

`max(0, max_k gain_k / collection_k)`.

The inner maximum ranges over positive collection coefficients; when there are
none, zero suffices if every gain is nonpositive.
[`EnforcementSynthesis`](../GameTheoryExtensions/Analysis/EnforcementSynthesis.lean)
implements this calculation and proves soundness, minimality even against real
deposits, and a concrete infeasible-row characterization. Its operational
adapter proves the resulting actual distribution comparisons. The monitored
native example extracts a range from declared integer source returns and checks
the inferred deposit against every raw early submission and later policy.

For several collectible charges, use a vector of deposits and linear
inequalities. Source-legal comparator lotteries can also be inferred, provided
one lottery works across every hidden history and continuation being compared.
The [sanctions note](research/se-ideal-sanctions.md) gives the finite certificate
and proof. The general SE theorem accepts these legal comparator lotteries and
their operational inequalities. Extracting all required finite rows from an
arbitrary protocol and synthesizing comparators are not implemented. Enumeration
can be large; a solver may search for a candidate while Lean checks its
inequalities and the operational extraction theorem.

That extraction has a specific next proof obligation: corresponding source and
target decisions must share the same sampled pure choices when averaging finite
rows back to behavioral policies. Independent source/target sampling would lose
the profile correspondence. An executable extractor also needs explicit finite
enumerators and rational kernels/payoffs, or certified rational bounds; the
general theorem itself allows real probabilities. These are algorithmic work,
not additional compilation levels.

This is the least deposit for the chosen sufficient certificate, not necessarily
the least deposit preserving SE. A comparison against every continuation can
be stricter than a comparison against equilibrium continuations. The existing
range/detection bound is a conservative instance, not a weakest assumption.

A caught abort can be synthesized only when its actual continuation utility is
controlled. For compliance value `V`, missed value `U`, caught value `F` and
detection probability `p`, the exact comparison is `U - V <= p * (U - F)`.
Replacing future actions by failure does not by itself implement an arbitrary
negative `F`, revoke information, or guarantee payment.

The analyzer has three honest outcomes:

| Result | Evidence |
| --- | --- |
| Certified | A structural correspondence and incentive certificate, with inferred parameters and backend assumptions. |
| Obstructed | A source SE whose retained law no target SE can match, or an exact proof that the specified repair family has no solution. |
| Unresolved | A sufficient certificate failed, an operational premise is missing, or a complete search exceeded its budget. |

Failure of the linear certificate is not an impossibility proof. Repairs may
change the target enforcement configuration; changing source payoffs, source
observations, or admitted strategies changes the specification and must be
presented as such.

## Exact detection and synthesis on finite inputs

For explicitly finite games with rational or algebraic data, preservation is a
first-order formula over the reals. If `P(D)` means every source SE has a
matching SE in the fixed target with deposit `D`, the synthesis question is

```text
exists D >= 0, forall sourceAssessment,
  SE_source(sourceAssessment) -> exists targetAssessment,
  SE_target(D, targetAssessment) and Match(sourceAssessment, targetAssessment, D)
```

The deposit precedes the equilibrium quantifier. `Match` compares joint laws;
it can additionally require extension of retained strategies and beliefs. An
exact decision procedure can therefore classify every given finite pair and
determine all successful parameters within a specified repair template. This
is the semantic weakest condition for that template and guarantee, rather than
a single weakest collection assumption for all runtimes.

The [real-algebra reduction](runtime-abstraction-classification.md#an-exact-decision-procedure-in-principle)
gives the consistency encoding, probability laws, parameter quantifiers and
proof of the reduction. It is a written algorithmic argument, not an implemented
or Lean-verified solver. Its cost confines it to small reference examples and
diagnosis; it is not the first implementation dependency of the compiler.

Exact synthesis does not justify rounding a parameter, assuming a least
solution, or assuming larger deposits always work. Such properties hold for
the nonnegative linear sufficient certificate above and require separate proof
for a general repair template. A specified fixed playerwise strategy compiler
can be checked when its graph has an effective finite algebraic description;
synthesis of arbitrary unknown compiler functions is not this decision problem.

## Assumptions to keep visible

| Assumption | What it enables; what remains outside it |
| --- | --- |
| Finite value/response alphabets and bounded interaction | Standard finite SE and finite inference. Timeouts alone do not bound pre-deadline traffic. Cover all source output values; do not silently truncate the game. |
| Decision-site recall | Consistent local optimality implies whole-policy rationality. Every reactive menu satisfies this premise; common-depth information sites and adequate evaluation fuel remain separate requirements. |
| Faithful permitted histories and observations | Source behavior is genuinely implemented. Clock signals, rejected plaintext and visible encodings require proofs, not a declaration that they are administrative. |
| Correct utility model | Deposit deductions and abort payoffs have the intended incentive effect. Voluntary entry and available wealth are separate questions. |
| Sound, attributable, collectible consequences | A reporting opportunity becomes an expected utility loss. The generic bound covers arbitrary continuation policies. A watcher who may refuse to report needs a separate equilibrium argument; the native pilot supplies one directly. |
| Stated commitment/evidence capabilities | Ideal ownership restrictions do not establish cryptographic security after secrets or keys are shared. |

There is no globally weakest set across changes to utilities, available
communication, monitor powers and source observations. The exact finite check
compares such choices once their operational meaning is fixed.

## Implementation order and acceptance tests

The [implementation plan](se-compilation-stack.md#implementation-work-packages)
records the checked revelation-service composition. The remaining priorities are:

1. **General activation rosters.** Retain bounded off-turn transmission and
   pending observation opportunities. Prove conditional source correspondence
   for repeated owner opportunities; extra timing recall alone is not an SE
   impossibility.
2. **Weaker audit assumptions.** The actual terminal-audit compiler is checked.
   Reduce its need for broadcaster attribution by allowing harmless public
   replays at auxiliary opportunities. Original-envelope signatures do not
   authenticate a rebroadcaster; the current capstone states that oracle
   requirement explicitly.
3. **Fresh commitments and guards.** Couple the checked source value-only
   continuation repair to actual native opponent observations and consistent
   continuation play. Do not require public detection of a privately unusable
   binding when it is observationally identical to lawful withholding.
4. **Sharper inference.** Extract rational comparison tables or terminal-only
   payoff bounds after the preceding semantic gates. Exact finite diagnosis
   remains a separate diagnostic project.

The decisive runtime cases are:

- **Early or rejected openings:** plaintext can matter before inclusion. A
  punishment rule needs evidence of when transmission was permitted; judging
  delayed traffic solely against the current stage can punish lawful behavior.
- **Opaque unopenable commitments:** valid and forfeited bindings can have the
  same public packet. Ordinary observation does not justify a positive detection
  premise. A game-specific irrelevance argument, admitted source forfeiture,
  or a stronger validity backend must account for the omitted choice.
- **Signals in permitted representations:** separate enforceable canonical
  encodings from choices that remain observable. An additional signaling SE
  alone does not refute forward preservation; prove harm to the chosen contract.

These tests and the existing checked obstructions are regressions, not extra
languages or mandatory compilation stages.

## Ownership and documentation

- `GameTheoryExtensions/`: restriction/completion theorem, finite incentive
  certificates, and SE formula correctness. Leave the GameTheory submodule alone.
- `Interaction/`: runtime observations, collection interfaces, operational alias
  laws and finite execution extraction, independent of Vegas syntax.
- `Vegas/`: source/graph/native correspondence, game-specific conformance,
  utility extraction and composed compiler theorem.
- Existing test roots: positive compiled instances and minimal obstructions.

The public result should consist of the ordinary Nash/Bayesian theorem, a
conditional SE compiler theorem with an inference algorithm, and precisely
scoped obstructions. SE existence and agent-form games support the proof.
The [artifact map](../ARTIFACT.md) records checked declarations. Detailed native
audits and research notes explain their premises. The strategic stack shares one
runtime implementation; a research example does not itself justify a new level.

CE and coalition enforcement, strategic paid watchers, cryptographic refinement,
unbounded traffic, computational/approximate SE and channel-noise bounds remain
separate research. They should enter the compiler contract only through a proved
additional instance or a stated change of assumptions.
