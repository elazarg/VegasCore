# Subgame perfection across compilation

## Status and recommendation

The existing compiler theorem concerns play from initialization. It preserves
Nash incentives, including ex ante Bayesian incentives for utilities of initial
parameters and public results. It does not establish subgame perfection.

The recommended target is preservation of behavioral subgame perfection by one
utility-independent, playerwise compiler, at every proper native subgame.
Reflection is a separate goal with a separate root-coverage obligation. Both
should use the canonical `GameTheory.Protocol.InformationModel` definitions.

This target needs operational work as well as a stronger simulation theorem.
The checked examples below expose a recovery defect and a general obstruction
to filling in new continuations from an optimal source plan. Neither example
is yet an end-to-end `IsSubgamePerfect` counterexample for the serviced runtime:
that requires service-specific continuation and subgame-root proofs.

Keep private inputs separate from commitments. Make commitment-failure
admission explicit in the source interface, and justify its omission separately
for each requested guarantee. The [preservation-contract design](preservation-contracts.md)
compares flag architectures and records executable and Lean experiments. A
request for SPE must not silently change the source game. A backend that only
satisfies the existing initial-play contract retains the existing Nash theorem;
it does not automatically satisfy the stronger contract.

There is a further obstruction independent of private preparation. The checked
atomic example below proves that adding early irreversible failure can prevent
any utility-independent compiler from preserving SPE from a value-only source.
An abstract withdrawal operation, a restricted continuation theorem, or a
runtime without that early commitment device is a substantive design choice.
Free private work alone does not resolve it.

### Checked implementation

The source protocol adapter is implemented for the actual typed program, with
an explicit commitment-admission map. It restricts legal transitions and
histories, retains the existing player views, and is equivalent to admitted
source pure and behavioral policies in both directions. Its initialized and residual laws
agree with the existing source runner; arbitrary legal prefixes retain private
state and own-action recall. A separate setup presentation includes the
private initial law as one chance step, using the same policies across draws.

[SourceSubgame.lean](../Vegas/Game/SourceSubgame.lean) and
[SetupSubgame.lean](../Vegas/Game/SetupSubgame.lean) identify canonical pure SPE
with inequalities over those source continuation laws. The tests in
[SourceProtocol.lean](../VegasTests/SourceProtocol.lean) and
[SetupProtocol.lean](../VegasTests/SetupProtocol.lean) prove that a hidden
forfeiture prefix and a hidden private-type draw, respectively, are not proper
subgame roots when another player's information set crosses them.

[Continuation.lean](../GameTheoryExtensions/Protocol/Continuation.lean) proves
the generic pure transfer theorem from prescribed and unilateral-mixture laws
at matching proper roots, plus a separate reflection theorem. The laws are
explicit hypotheses about one playerwise map. The canonical irreversible-
failure example refutes uniform certificates for that proposed abstraction in
[ContinuationTransfer.lean](../GameTheoryExtensionsTests/ContinuationTransfer.lean).
This code is in VegasCore; it requires no GameTheory submodule changes.

[BehavioralSubgame.lean](../Vegas/Game/BehavioralSubgame.lean) characterizes
behavioral SPE by the same source continuation laws, with arbitrary admitted
behavioral replacements. [BehavioralContinuation.lean](../GameTheoryExtensions/Protocol/BehavioralContinuation.lean)
proves conditional preservation and reflection for these policies. Its roots
are the existing information-set-closed histories, and its payoff uses the
existing randomized runner. The certified evaluation bound does not affect
the predicate. No finite player universe or finite action domain is assumed.

[ResponseProtocol.lean](../Vegas/Pending/ResponseProtocol.lean) presents the
native response service with the actual players as strategic coordinates.
Setup, wire scheduling, and adaptive order are fixed stochastic kernels.
[ResponseProtocolPolicy.lean](../Vegas/Pending/ResponseProtocolPolicy.lean)
proves an equivalence with all native response policies, using only own recall
and the actual native view at invocation. The service cursor is not observed.
The service plan retains all three initial owner invocation slots and every
wire/roster reaction slot. Each invocation permits finite free private work
and one network command; public submission opportunities are retained.

The response adapter has checked termination, exact native invocation laws,
and refinement of arbitrary continuations to native action sequences.
[ResponseProtocolNative.lean](../Vegas/Pending/ResponseProtocolNative.lean)
proves that responses consume zero clock ticks, retain live activation times,
and preserve fixed candidate meanings. It also proves that every legal
initialized response history retains fresh, unused candidate handles.
[EventBindingResponse.lean](../Vegas/Pending/EventBindingResponse.lean) realizes
any binding result in one response and proves exact graph acceptance when its
packet is included while ready and timely. This tolerates occupied canonical
slots and arbitrary remembered actions. It does not cancel competing packets
or supply a complete contingent policy. This is a response-service presentation;
the paper's initial-play capstones concern the command-service compiler.
Compiling graph policies into responses, recovery after arbitrary prefixes,
source/native continuation correspondence, and proper-root coverage remain
open. No native SPE capstone is claimed.

## What the theorem must mean

`GameTheory/Protocol/SubgamePerfect.lean` already defines:

- `InformationModel.IsSubgameRoot`: every decision information set intersecting
  the continuation lies wholly inside it.
- `InformationModel.IsSubgamePerfect`: no whole replacement policy improves a
  player's continuation value at any such root, including roots off the
  equilibrium path.
- `InformationModel.IsHistorywiseOptimal`: the stronger comparison after every
  complete history, whether or not it starts a proper subgame.

The existing SPE predicate takes pure, information-local policies, allows
probabilistic transitions, and uses `historyBackwardValue`. The EFG interface
specializes that predicate; it does not supply a different semantics.
Its one-shot characterization concerns the stronger historywise predicate
under its stated hypotheses. Do not substitute that characterization for SPE
in an imperfect-information game.

The desired statement is schematically

```text
Source.SPE u sigma -> Native.SPE (u o decode) (compile sigma).
```

Here `compile sigma` is one global contingent profile. Choosing a different
optimal native continuation separately at each root is not enough: those
choices must come from that same information-local profile. A deviation changes
future decisions; it never rewrites the prefix being evaluated.

Utilities remain `u : Theta × Omega -> Player -> Real`, with `Theta` read from
the original setup and `Omega` the public result. Continuation execution retains
the original types, private memories, packets, clock, and remaining service
cursor. It does not sample a new prior or restart the service budget.

Proper roots matter. Private types can prevent a history from starting a
subgame because an information set crosses its boundary. A public transcript,
a completed event, or a complete machine state is not by itself a subgame-root
certificate. Checking only source-aligned checkpoints also leaves a weaker
property than native SPE. SPE need not rule out every implausible threat inside
an imperfect-information subgame; sequential equilibrium is a separate notion.

## Evidence that constrains the design

### A recoverable native prefix

[`VegasTests/ContinuationRecovery.lean`](../VegasTests/ContinuationRecovery.lean)
uses the real pending application and compiled player policy. There is one
player, one initial Boolean binding, and one resolve event with deadline two.
It checks:

1. A commitment packet addressed to the resolve event is rejected by `handle`.
2. Submitting that packet is a legal player step.
3. The compiled policy subsequently returns `wait`.
4. A correct opening at the same application state would publish successfully.

`compilePlayerPolicy` treats any earlier event-addressed submission as a reason
to stop submitting, independently of whether it can succeed. The first of the
three reserved owner calls can therefore leave a prefix from which following
the compiled policy wastes the remaining opportunities.

The checked result is operational: it does not yet prove the complete suffix
payoffs or that this prefix is a proper root of the full serviced game. Those
are the first adapter validation obligations. The repair must also account for
first-write remembered actions and occupied preparation slots after arbitrary
earlier commands; replacing one Boolean test is insufficient evidence of
general recovery.

### An optimal plan does not specify the best remaining choice

Suppose a one-player source decision offers `a`, `b`, and `c`, but a native
continuation offers only `b` and `c`:

| Utility | a | b | c |
| --- | ---: | ---: | ---: |
| `utilityB` | 3 | 2 | 1 |
| `utilityC` | 3 | 1 | 2 |

The same source plan chooses `a` optimally for both utilities. At the restricted
continuation the utilities require different choices. Randomization does not
help: the two expected utilities always sum to three, whereas optimality for
both would require each to be at least two.

[`GameTheoryExtensionsTests/ContinuationMenus.lean`](../GameTheoryExtensionsTests/ContinuationMenus.lean)
checks this using the canonical `GameForm` and `IsεNash`, including the explicit
nonexistence of a utility-independent completion function for this plan and
menu. It is an abstract continuation obstruction, not a theorem that every
Vegas implementation has such a continuation.

For the command-service runtime, there is a concrete candidate witness:
prepare candidates `b` and `c`, leave `a` unprepared, and reach the last owner
invocation before a binding expires. Submitting an already prepared candidate
uses one invocation; preparing and submitting `a` takes two. With a suitable
service order, the binding can be the last event visited before the expiry
sweep. The remaining choices could then expose exactly this preference gap.

Before using that argument as a runtime impossibility theorem, check the whole
prefix, the exact residual outcome menu (including failure), and proper-root
closure. Give failure utility below both `b` and `c`. Account for replay,
cross-event submissions, reserved inclusion, and all remaining service slots.
The abstract lemma alone does not discharge these obligations.

The atomic-response runtime removes this preparation-capacity obstruction.
Every finite prefix leaves fresh handles, and one response can prepare and
submit any value. The checked construction does not assume an empty cache or
an unused canonical event slot. An existing transmitted candidate remains
binding, and an earlier pending packet can still win inclusion; the two cases
are checked in `VegasTests/InFlightCommitment.lean`. A continuation certificate
must address these remaining network choices. It cannot treat a new submission
as cancellation of the old one.

## Protocol architecture

### Early irreversible failure is strategically observable

[`GameTheoryExtensionsTests/IrreversibleFailure.lean`](../GameTheoryExtensionsTests/IrreversibleFailure.lean)
uses the canonical `InformationModel.IsSubgamePerfect`, its history evaluator,
and its definition of proper subgames. One player takes four atomic decisions:
seal A, choose B, disclose A, disclose B. The source requires A to be openable;
the target additionally permits an unopenable A. All decision histories are
proper subgame roots, proved using the player's complete own-action recall.
There is no private preparation, clock, network, or computation cost.

The two utilities depend only on the public results:

| Public result | Utility favoring false after failure | Utility favoring true after failure |
| --- | ---: | ---: |
| A succeeds; B is either value | 3 | 3 |
| A fails; B is false | 2 | 1 |
| A fails; B is true | 1 | 2 |
| B is withheld | 0 | 0 |

The same source plan is SPE for both utilities: seal an openable A, choose
false for B, and disclose both. At every source continuation before A's
disclosure, success remains available and is preferable. If A was already
withheld, B's value has already been chosen; disclosing B is then optimal for
either utility.

The target has a proper subgame after an unopenable A is sealed but before B is
chosen. A's failure is now unavoidable. The two utilities require opposite B
choices. The module proves `no_utility_independent_spe_compiler`: no single
translation of that common source plan is SPE for both utilities. A separate
finite-distribution bound proves that randomization cannot supply a common
optimal continuation either.

This explains the limit of the public-outcome abstraction. At initialization,
an unopenable binding can be simulated by a valid binding followed by deliberate
withholding. At an intermediate history, the valid binding still permits
disclosure; the unopenable one does not. Initial-law equivalence therefore does
not identify these continuation games.

The example is a complete SPE counterexample for the stated atomic protocols,
not a compiler theorem about the full Vegas runtime. Relating that protocol to
the source and serviced runtime still requires the adapters below. In
particular, an abstract withdrawal operation would address this obstruction
without exposing malformed values or candidate handles, but would not by itself
prove the remaining native continuation correspondence.

### One continuation semantics

The pure and behavioral continuation game forms in
[Continuation.lean](../GameTheoryExtensions/Protocol/Continuation.lean) and
[BehavioralContinuation.lean](../GameTheoryExtensions/Protocol/BehavioralContinuation.lean)
use the existing pure and randomized history runners. Behavioral SPE is Nash
optimality at each existing proper root. A proved bound on every legal history
ensures termination; a checked theorem makes the predicate independent of
which sufficient bound is supplied. Evaluation fuel is not a fresh operational
service budget.

Point-mass policies give exactly the existing pure run law. Behavioral SPE of
such a profile implies canonical pure SPE, because it includes all pure
replacements. No separate source evaluator or source-only root predicate is
introduced.

Value agreement for point-mass policies is not, alone, equivalence of pure and
behavioral SPE: the latter quantifies over behavioral deviations. Prove that
additional equivalence under an appropriate predraw/no-repeated-decision
condition, instantiated for these protocols. The current generic predraw
theorem's freshness premise covers all histories of different lengths, which
is stronger than merely having perfect recall or fresh genuine decision sites.
Do not make the adapters reveal an invisible service cursor to satisfy it.

[SingleMover.lean](../GameTheoryExtensions/Protocol/SingleMover.lean) constructs
behavioral joint actions when at most one player acts. Each player's marginal
is exactly its local policy law; idle players have singleton menus. This agrees
with the canonical finite product when a finite player instance is available.
The source and setup adapters supply the single-mover proof. Tests instantiate
the construction with natural numbers as players and a nondegenerate lottery
over a valid binding and forfeiture. No finite payload domain or equilibrium
existence assumption is needed for transfer.

### Source, graph, and native presentations

| Presentation | State and information | Required adequacy result |
| --- | --- | --- |
| Abstract source | Typed residual program, store, own-action recall, and explicit per-site commitment admission | Initial and residual laws agree with the selected source interface |
| Canonical graph | Existing configuration, event cursor, observations, and action histories | Residual laws agree with source suffix execution |
| Serviced native game | `ServiceControl` and `PolicyExecution`; actual own history and native view | Response policies correspond exactly to protocol policies; graph-policy compilation and source/native continuation laws remain required |

The source's legal actions must implement the selected admission interface:
values at a value-only site, values or forfeiture at an explicit failure site.
A subtype of complete strategies, by itself, does not select a tree of legal
histories. The failure-aware source can serve as the common internal interface,
but its initial public-outcome simulation does not license SPE failure elision.
That abstraction needs its own continuation certificate.

Reuse `SourceProgram.runFrom` and its typed successors, `CompiledSuffix`, and
the native service-control transitions. A protocol adapter exposes these
transitions to the shared game theory; it does not implement them again.
Prove policy correspondence on realizable decision views, in both directions
needed by the theorem, without increasing what a player observes.

The native protocol must have the actual players as strategic coordinates.
Setup, public chance, fixed wire policy, and fixed order policy belong in the
transition kernel. The existing `serviceProtocol` has one analysis agent
controlling focal-player, wire, and order decisions for a predraw proof; the
scheduler protocol fixes the players and makes the scheduler strategic. The multiplayer response adapter supplies the required strategic coordinates;
neither analysis protocol can substitute for it.

Keep an explicit termination certificate. Begin with sequential dependencies
and a canonical order. Prove any extension to concurrent event scheduling as a
separate continuation theorem: store-law confluence does not establish root or
information-set correspondence.

## The continuation certificate and proof

Write `L_S(sigma, h)` and `L_T(compile sigma, k)` for the laws of decoded terminal
`(theta, omega)` pairs, starting from source and target histories respectively.

For each source profile `sigma` and each proper target root `k`, the sufficient
certificate supplies a finite law `mu` over **proper source roots**, with:

```text
L_T(compile sigma, k)
  = E[h ~ mu] L_S(sigma, h)

For every player i and native replacement tau:
L_T((compile sigma)[i := tau], k)
  = E[h ~ mu] E[rho ~ Q(i, tau, h)] L_S(sigma[i := rho], h).
```

These equations are equalities of distributions; the expectations denote
finite mixture. A single matching source root is the point-mass case and is
the first implementation target. Introduce the root-mixture generalization
only where an adapter needs it.

The quantifier order carries substantive requirements:

- `compile` is fixed globally, playerwise, and independent of utilities.
- `mu` is chosen before the native deviation, and is the same in both laws.
  Changing the reference root distribution with the deviation invalidates the
  averaging proof.
- Each `rho` is one legal, information-local source replacement for its whole
  continuation. It cannot inspect hidden chance subsequently drawn below `h`.
- The unchanged source opponents remain `sigma[-i]`. The target prefix may
  already contain deviations by several players; restricting prefix coverage
  to a single earlier deviator does not suffice.
- The laws preserve the initial parameters as well as public results. At a
  fixed prefix these parameters are retained, not resampled.
- Every proper target root is covered, including roots between private commands
  or packet operations. No positive-probability-on-equilibrium-path premise is
  allowed.

The transfer proof is short once these obligations are met. Source SPE bounds
every `rho` at every root in `mu`. Average first over replacement policies and
then over roots, and rewrite the two laws. The same argument preserves a
per-subgame epsilon bound. This is stronger than an ex ante epsilon bound,
which cannot simply be conditioned on rare prefixes.

The checked pure single-root theorem is
`InformationModel.isSubgamePerfect_of_continuation_laws` in the VegasCore
extension module. Its proof uses the canonical continuation values and finite
expectation bounds. A weighted-root lemma, if needed, is an averaging argument
over the same continuation games. Composition must preserve the global compiler
and root coverage; compose the laws before claiming a tower theorem.

For **reflection**, realize every proper source root by suitable proper native
roots and lift its profitable source deviations with the requisite continuation
laws. Terminal-law reflection at initialization is insufficient. Only after
this second direction is proved can an SPE equivalence preserve the distinction
between a Nash profile sustained by noncredible threats and an SPE profile.

## Native design to validate

The preferred backend contract is: before an abstract action takes effect,
all its source choices remain implementable; after it takes effect, the
available choices match the corresponding source continuation. Administrative
operations must preserve this correspondence, including after earlier
malformed commands. This is an obligation to prove, not a definition that can
be satisfied by deleting inconvenient native histories.

The response interface should permit finite private computation and an optional
outgoing message in one owner invocation. Private bookkeeping consumes no
separate service opportunity. This removes the particular deadline menu loss
caused by splitting preparation and submission. Sampling a source action and
constructing its packet together may also eliminate the staging cache. Actual
recall of earlier choices remains necessary.

`Interaction.MessageApplicationResponse` provides this response operation:
finite private work followed by submission, replay, or waiting. Its expansion
into native actions is proved, so existing native safety invariants apply.
Private work changes neither transport nor the observations of other players
under the application's locality premise. The atomic reaction test in
[InFlightCommitment.lean](../VegasTests/InFlightCommitment.lean) checks one observation-local response that reads a
delivered bit, prepares a fresh candidate, and submits it without advancing time
or including a packet. The response-service kernel executes the same reaction
before reserved inclusion and preserves every existing invocation slot.
Its native refinement and clock laws are checked. The graph strategy compiler
still needs an atomic-response translation and proofs at arbitrary prefixes;
the paper capstones use the command-service translation.

Submission must remain separate from delivery and inclusion. The wire can
inspect the pending pool, deliver an envelope to a player's inbox, and invoke
that player's response before inclusion. The player can read that envelope and
send another packet, replay a known packet, or withhold. Response grouping must
preserve these observation and reaction points. Neither the number of public
submission opportunities nor message visibility should change as an incidental
consequence of removing private staging.

### When a transmitted handle acquires its meaning

Commitment meanings are fixed by authenticated submission, before the packet
enters the observable pool. A prepared handle keeps its value; an unprepared
handle becomes permanently unopenable. A foreign reference cannot freeze
another player's private candidate. Delivery, inclusion, replay, and later
private commands cannot change a fixed meaning.

`EventGraphRuntime.submitted_commitment_binding` proves this invariant for
arbitrary finite native continuations, without honesty or inclusion premises.
[`VegasTests/InFlightCommitment.lean`](../VegasTests/InFlightCommitment.lean)
checks the following actual native transitions:

1. Alice submits an unprepared commitment handle.
2. Bob's packet is submitted; the wire delivers both packets to their respective
   observers while the ledger and receipts are still empty.
3. One information-local Alice policy reads Bob's bit from her inbox and tries
   to prepare her already-transmitted handle with that bit.
4. The original handle remains unopenable. Alice can instead prepare and send
   a new handle with the received bit while the original envelope is pending.

The example checks the native transitions and handler; it does not assert a
serviced-game equilibrium or a proper-subgame witness. Its policy does not take
the bit as an extra input: it reads the actual received packet.

Binding at submission is independent of grouping private work into a response.
Reading and reacting to other pending messages remains possible. The response
redesign must preserve those opportunities while making private work free.

The native edge still needs proofs about competing pending packets,
irreversible acceptance, adaptive wire reactions, receipts, and recovery after
arbitrary earlier submissions. Atomic response construction alone is not an
SPE theorem.

Do not reset deadlines on retry: that changes completion and strategic timing.
Do not add candidate pools or staging counters to the abstract language.
Irrevocable forfeiture can express the strategic effect of malformed binding
without exposing invalid payloads; its admission and information timing must
be explicit. If the intended runtime cannot meet the continuation contract,
report the unresolved obligation or proved obstruction with its exact scope.
The existing Nash result does not discharge an explicit request for SPE.

An alternative is utility-aware equilibrium completion on newly introduced
continuations. That is an analysis/synthesis operation with additional inputs
and existence obligations, rather than the current playerwise compiler. In
multiplayer imperfect-information games, independent local maximization does
not even construct a mutually consistent equilibrium. This alternative is not
the default design.

## Proof gates

1. **Validate the actual subgames.** Present the single-player serviced example
   through the canonical protocol API. Prove prefix reachability, information-set
   closure, complete continuation laws, and the profitable recovery deviation.
   Check the deadline-menu candidate just as explicitly. A failure to establish
   proper-root closure changes the counterexample claim.
2. **Close the semantic bridge.** Pure and behavioral source adapters,
   arbitrary-prefix laws, private setup, and the crossed-root tests are checked.
   The multiplayer native response adapter, native policy equivalence, and
   invocation laws are checked. Prove the graph-policy response compiler and
   source/native continuation correspondence, including behavioral deviations.
3. **Prove the source-to-canonical edge.** Establish source suffix laws, policy
   restriction compatibility, and root coverage for histories legal under the
   selected commitment-admission interface. Keep concurrent scheduling outside
   this gate.
4. **Validate the response contract.** Native safety, submission binding,
   bounded service, and zero clock cost for private response work are checked.
   Discharge hostile prefixes for the selected compiler: establish recovery,
   candidate allocation, cache handling, and residual choice correspondence.
5. **Compose preservation.** Instantiate the continuation certificate at every
   native root and lift joint parameter/public-result utilities. Add a genuine
   noncredible-threat example that is Nash but not SPE, alongside a preserved
   SPE. Prove reflection and scheduler generalization only with their additional
   coverage lemmas.

All five gates are required before adding native SPE preservation to the paper.
The source part of the semantic bridge and the conditional pure and behavioral
transfer and reflection theorems are checked. The remaining gates are not discharged by the examples,
and no missing theorem is asserted as an axiom.

## Related methodological precedent

[Halpern, Pass, and Seeman, *Computational Extensive-Form Games*](https://www.cs.cornell.edu/home/halpern/papers/kuhn.pdf)
uses a representation relating histories and information sets, in addition to
strategy and distribution requirements. Its Theorem 4.5 transfers sequential
equilibrium to its computational notion under that representation and perfect
recall. This supports investigating a history-level contract here. It does not
imply ordinary SPE preservation at every raw native history from our terminal
outcome theorem; the equilibrium notions and hypotheses differ.
