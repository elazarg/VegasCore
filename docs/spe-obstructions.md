# Obstructions to SPE preservation

## Scope

This is the inventory of concrete failure mechanisms found in the experiments,
proofs, and runtime investigation. It is not an exhaustiveness theorem: excluding
these examples would not itself establish preservation. The final obligation is
a continuation theorem covering every proper native subgame.

The intended claim fixes **one utility-independent, playerwise compiler**, then
quantifies over source behavioral SPE profiles and utilities of original private
types and public results. The compiled profile must be behavioral SPE at every
proper native root, including roots reached after earlier deviations by any
players. Reflection requires additional coverage and is a separate claim.
The [SPE specification](subgame-preservation.md) gives the canonical definitions.

Three evidence levels must remain distinct:

- **Native SPE counterexample:** legal initialized prefix, proper-root proof,
  information-local deviation, and continuation payoffs in the actual runtime.
- **Abstract SPE or local obstruction:** a checked game or operational witness,
  without all the obligations of a native SPE counterexample.
- **Documented argument or open obligation:** useful design evidence, with its
  missing formalization stated explicitly.

## Inventory

| ID | Mechanism | Strongest evidence | Present boundary |
|---|---|---|---|
| O1 | The target can irrevocably lose disclosure before another decision; the source cannot | Checked abstract pure-SPE compiler impossibility, plus a randomized local bound | Source forfeiture is available; a matching native continuation theorem is open |
| O2 | New public traffic changes which old commitment wins | Checked native behavioral-SPE impossibility for every utility-independent compiler into the specified scheduler | Stronger selection contracts exclude this rule locally; unrestricted scheduling remains impossible |
| O3 | Replay has selection power unavailable to a fresh proposal | Checked local randomized incentive obstruction and exact network selection witnesses | Distinct identifiers and unpublished eligibility address the witnessed menu effects |
| O4 | One transmission opportunity can help different events | Checked honest source SPE whose current compiled policy is not native behavioral SPE under uniform inclusion | Authorized uniform service removes the exhibited improvement; full SPE and ledger realization open |
| O5 | Recovery confuses an attempted submission or remembered intention with what took effect | Checked operational failure of the command-service policy; reactive recovery and reconstruction regressions | Selected cases are repaired; arbitrary-prefix correspondence remains open |
| O6 | Target observations reveal information absent from source observations | Checked abstract behavioral-SPE impossibility for disclosure after a deviation, despite initialized law matching; documented raw-packet example | No native adapter for the disclosure example; reactive continuation information laws remain open |

O1 and O2 illustrate a common obstruction: a source policy can select its best
option without encoding a ranking of alternatives that the target later forces
it to compare. The checked [continuation-menu example](../GameTheoryExtensionsTests/ContinuationMenus.lean)
isolates that argument. It is an explanation of these mechanisms, rather than an
additional native counterexample.

### Representation issue: private memory removes subgames

The [checked memory audit](private-memory-and-subgames.md) concerns the adequacy
of the requested predicate, rather than a profitable deviation. In the actual
reactive protocol, after one player has responded, proper subgames cannot
contain later foreign decisions. After two distinct responders, they cannot
contain further player decisions at all. Arbitrary auxiliary memory causes
this for every scheduler and observation rule, including the Vegas adapter.

This would make a positive raw-SPE theorem miss the intended multiplayer
continuation obligations. The generic realization of internal strategy memory
as an information-local behavioral policy is proved, but its reactive adapter
and the resulting subgame presentation remain open. Resolve this issue before
using the absence of proper native roots to close the preservation argument.

### O1. Early irreversible failure changes the remaining game

**Witness.** There are four atomic decisions: seal A, choose B, disclose A,
disclose B. The source requires A to be openable. The target also permits an
unopenable A. Successful A gives the same best payoff regardless of B, so one
source policy is SPE for two utilities. After unopenable A, those utilities
require opposite choices of B. No common target pure SPE exists.

[IrreversibleFailure.lean](../GameTheoryExtensionsTests/IrreversibleFailure.lean)
proves source SPE, proper roots, and impossibility of a utility-independent
pure-SPE compiler for these atomic protocols. It also proves a local bound
against randomized completion. This is not a serviced Vegas runtime theorem.
There is no separate preparation action, cost, network, or deadline in the example.

**Required response.** Either the source admits the corresponding early,
owner-known irreversible forfeiture, or the chosen game/backend has a proof
that it can be omitted. Later withholding is at a different decision point and
does not supply the missing source history. Dependency authorization alone
does not address a malformed first commitment with no predecessors.

**Closure criterion.** Relate actual native forfeiture continuations to legal
source continuations, preserving information and the remaining choices. If
forfeiture is elided, prove that specific transformation preserves the requested
property. Enabling the existing source admission interface is not that proof.

### O2. Public traffic controls the choice among old commitments

**Witness.** Commitments to 1 and 2 are pending. A fixed scheduler includes 1
if Alice sends a fresh envelope, and 2 otherwise; it never includes the new
commitment to 0. Two utilities rank 0 first but disagree about 1 versus 2. They
share a source SPE, but no target behavioral profile is SPE for both.

The [reactive inclusion counterexample](reactive-inclusion-obstruction.md)
establishes the full native result, including arbitrary randomized replacements.
It rules out every utility-independent compiler for that scheduler, even with
source forfeiture admitted. The scheduler uses public pending traffic, with no
leaks or secret observation records. Forgetting history does not exclude its
decisive rule. It is a standalone scheduler, not the reserved epoch service.

**Required response.** Constrain how fresh traffic affects retained candidates.
The checked [selection contracts](inclusion-and-spe.md) supply either a fixed
mixture with the old distribution or the weaker condition that insertion never
increases an old candidate's absolute probability. The local incentive results
also require independence from the fresh source value and a fixed downstream
kernel. A uniform final draw does not constrain earlier inclusions or later
traffic-dependent service decisions.

**Closure criterion.** Establish the relevant law for every response and every
inclusion that can settle the event, and then relate the whole remaining play.
This must cover silence, replay, fresh submissions, and subsequent reactions.

### O3. Replay defeats a contract about fresh submissions

There are two checked boundary cases:

- **Counting copies.** A stateless weighted selector counts repeated copies of
  one envelope. Replaying a preferred old candidate can outperform proposing
  the source-optimal fresh value. [PendingChoice.lean](../GameTheoryExtensionsTests/PendingChoice.lean)
  proves that the resulting local game has no common randomized optimal response
  for two utilities. It does not construct a proper native subgame.
- **Restoring a spent identifier.** A stable priority selector prefers a removed
  identifier when it is replayed; the next fresh identifier cannot obtain that
  priority. [PendingPriority.lean](../InteractionTests/PendingPriority.lean)
  proves the exact network selections. This is an operational witness, without
  an application-level incentive or SPE theorem.

**Required response.** Select distinct identifiers, and exclude already included
identifiers *before selection*. At-most-once inclusion also consumes rejected
calls. Merely converting a second attempted inclusion into a wait does not
establish that replay leaves the selector unchanged.

**Current protection.** [ReactivePublication.lean](../Interaction/ReactivePublication.lean)
proves that replay preserves the unpublished eligible menu at every legal
initialized history. [ReactiveServicePublication.lean](../Vegas/Pending/ReactiveServicePublication.lean)
checks at-most-once inclusion for the reserved service. These are the relevant
local protections; a scheduler's reactions to the public rebroadcast still
belong in the whole-continuation proof. Fresh envelopes with equal payloads
have different identifiers and are not covered by replay invariance.

### O4. Transmission opportunities compete across events

**Witness.** An off-path prefix leaves a commitment to 1 and a premature
withholding packet pending. Alice gets one activation before binding inclusion
and one before disclosure inclusion. Each inclusion uniformly selects distinct,
unpublished envelopes for its event.

The recovery compiler submits a commitment to 0, then opens the selected
binding. A deviation instead spends the first activation opening the old
commitment to 1, then sends another opening at disclosure. For success payoffs
0 -> 3, 1 -> 2, and failure -> 0, the checked continuation values are:

| Continuation | Expected utility |
|---|---:|
| Compiled recovery | 5/4 |
| Early-opening deviation | 4/3 |

[ReactiveEarlyOpeningSPE.lean](../VegasTests/ReactiveEarlyOpeningSPE.lean)
proves an honest source SPE, a proper native root, both values, failure of the
actual graph-policy compiler to preserve SPE, and at-most-once inclusion.
Both compared continuations finish. This refutes that compiler under the
specified uniform service; it does not rule out every compiler for that service.
The [detailed account](early-opening-and-spe.md) states the source/graph bridge
and the limits of the fixture's service guarantees.

The commitment and opening are selected in **different draws**. The scarce
resource is Alice's earlier transmission opportunity. The graph already has
a commit-before-disclose dependency; execution readiness does not prevent an
early packet from waiting to participate later.

**Candidate response.** [Dependency-authorized submission](dependency-authorized-submission.md)
requires evidence of completed predecessors to be authenticated together
with the payload when the envelope is first submitted. Its semantic contract,
permanent exclusion of unauthorized envelopes, and concrete witness checks are
proved. Raw premature broadcasts remain possible. A
[public-history service](../Vegas/Pending/ReactiveDependencyService.lean) enforces
the condition and combines it with uniform, at-most-once selection. Its local
response law is checked. A ledger certificate and the complete continuation
argument remain open; ordinary execution-time dependency checks do not imply
the contract.

[ReactiveDependencyService.lean](../VegasTests/ReactiveDependencyService.lean)
checks the same proper root under the enforcing calendar. Across the complete
remaining continuation, the compiler's value is 5/2 and the exhibited
early-opening deviation's value is 2. Both finish successfully. This closes
that comparison, while leaving arbitrary continuation replacements open.

**Closure criterion.** Prove optimality with the actual remaining opportunities.
The checked authorization invariant and source information discipline isolate
each player's authorized unfinished packets to its one ready owned event, even
with concurrent foreign commitments. Whole-service effects of raw signaling,
fresh duplicate payloads, and near-deadline recovery still need coverage. These
are test obligations, not additional established counterexamples. Increasing a
fixed transmission allowance requires its own capacity argument at every prefix.

### O5. Recovery must use what actually happened

**Witness.** A wrong packet addressed to a disclosure event makes the
command-service compiler regard the event as already submitted. It waits even
though a valid opening still succeeds.
[ContinuationRecovery.lean](../VegasTests/ContinuationRecovery.lean) checks the
legal player step, rejection, compiled wait, and successful replacement. It
does not prove proper-root status or an SPE counterexample.

There is also a reconstruction issue: several pending responses can remember
different intentions, and a rejected attempt to disclose can produce the same
public withholding packet as a deliberate decision to withhold. Source own
action recall distinguishes those intentions. An arbitrary memory tag cannot
decide which one should enter the reconstructed source history.

**Current response.** The [reactive recovery policy](reactive-recovery.md) is total
after unsupported own responses, preserves initialized execution laws, and
reuses supported choices rather than repeatedly resampling them. Reconstruction
matches an intention to the actual accepting receipt and checks the recorded
response. [ReactiveRecovery.lean](../VegasTests/ReactiveRecovery.lean) tests
accepted, rejected, competing, and forged intentions.

**Closure criterion.** Prove information-local source-history reconstruction and
continuation correctness at arbitrary legal roots, including earlier deviations
by several players. Initialized packet uniqueness assumes the focal player has
followed its compiler and cannot simply be reused at those roots. The O4
counterexample also shows that a defined recovery response need not be optimal.

### O6. The target exposes extra information

**Checked abstract witness.** Chance gives Alice a private bit. She can stop
or ask Bob to guess it. The source keeps the bit hidden; the target reveals it
when Bob is asked. Alice is indifferent. The same source stop profile is SPE
for utilities rewarding either a match or a mismatch. The target Bob histories
are proper subgames requiring opposite choices, so no common target behavioral
SPE exists. This rules out every utility-independent translation of that
profile for these two games, including randomized translations.

Nevertheless a playerwise compiler preserves initialized joint type/result
laws for all source profiles. At the stop profile, every target unilateral
deviation also has an exact source law match. The
[incentive-criterion note](spe-incentive-criterion.md#information-after-earlier-deviations)
explains the experiment and links its canonical-root, SPE, and law proofs.
This identifies the additional obligation after earlier deviations by other
players. It is not a native runtime counterexample: the disclosure must
authenticate the actual bit to obtain those particular proper roots; an
untrusted raw claim does not automatically do so.

**Documented witness.** Bob commits a random bit under a rejecting guard. If
the prescribed policy broadcasts the raw attempted opening, Alice learns that
bit, although the source publishes only failure. Bob later publishes the bit
through a valid commitment; Alice can use the early leak to win a matching
game that has no such source strategy. The
[public-observation note](event-graph-public-observations.md) gives the incentive
argument. This negative example has no standalone Lean canonical-SPE proof.

**Current response.** The prescribed compiler checks the prospective resolution
before constructing the public packet. A rejected opening emits a
value-oblivious withholding packet and retains the original intention privately.
The emission lemmas and initialized command-service deviation law are checked.
Arbitrary deviating players still have the raw packet space.

**Closure criterion.** Establish the continuation information law for unchanged
players' emissions, passive observations, public scheduling, and retained own
recall. Dependency authorization would not conceal the contents of an unusable
raw broadcast. The theorem must cover foreign in-flight reading and reactions;
removing them would change the intended runtime.

## Model invariants already established

These constrain the investigation; they are not reasons to keep changing the
player action boundary.

| Concern | Present model/evidence | Limit |
|---|---|---|
| Late assignment of a commitment's meaning | [ReactiveSafety.lean](../Vegas/Pending/ReactiveSafety.lean) fixes the candidate at submission and preserves it through transitions | Binding does not promise successful disclosure |
| Separate private preparation or computation cost | [ReactiveApplication.lean](../Interaction/ReactiveApplication.lean) gives one response with optional transmission | This is the chosen action model, not an equivalence to every game with split actions |
| Running out of private preparation slots | [ReactiveFreshCandidates.lean](../Vegas/Pending/ReactiveFreshCandidates.lean) supplies fresh candidates after every legal history | Public transmission opportunities and deadlines remain finite |
| Receiving one's own packet as a new leak | [ReactiveKnowledge.lean](../Interaction/ReactiveKnowledge.lean) proves foreign-only passive knowledge | Own action recall remains available |
| Scheduler sees which private leak was sampled | [ReactiveObservation.lean](../Interaction/ReactiveObservation.lean) proves identical scheduler views across samples, including after silent responses | The scheduler still sees public traffic; shared public causes can correlate inclusion and observations |
| A root inside consecutive implementation actions | [ResponseCoalescing.lean](../VegasTests/ResponseCoalescing.lean) excludes the particular split root in the comparison protocol | No universal SPE theorem for coalescing; O2 and O4 use separate public transmissions |

The [action-boundary investigation](action-coalescing.md) also has a finite
Alice-Bob-Alice experiment without adjacent same-player decisions. It has no
native runtime adapter. Merely inserting another player's turn is therefore
neither an established repair nor a new native impossibility theorem.

## Positive proof obligations

These are gaps to discharge, not additional proved counterexamples.

1. **Proper roots and information sets.** A public checkpoint or completed event
   is not automatically a subgame root. Hidden source choices and private setup
   can make information sets cross a proposed cut; see
   [SourceProtocol.lean](../VegasTests/SourceProtocol.lean) and
   [SetupProtocol.lean](../VegasTests/SetupProtocol.lean). Root matching must use
   the actual canonical information models throughout the suffix.
2. **Service guarantees at arbitrary prefixes.** Termination, packet provenance,
   and graph completion are checked for the reserved reactive service. Acceptance,
   protection through inclusion, and strategic continuation correspondence remain
   open. Keep the actual pending pool, spent identifiers, clock, grants, and
   remaining opportunities. Do not restart the service or its deadlines at a root.
3. **A whole-continuation incentive argument.** The checked generic
   [behavioral transfer theorem](../GameTheoryExtensions/Protocol/BehavioralContinuation.lean)
   supplies one sufficient route: each proper target root has a distribution of
   proper source roots, fixed before the deviator is chosen. The same distribution
   explains prescribed and deviated outcome laws, with unchanged source opponents
   and whole information-local replacement policies. A fixed distribution for
   each isolated inclusion is insufficient, as O4 demonstrates. Exact law matching
   is a sufficient certificate, not a necessary characterization of SPE
   preservation. For finite observed outcomes, the checked
   [incentive-cone theorem](../GameTheoryExtensions/Protocol/BehavioralIncentives.lean)
   gives a necessary and sufficient alternative: every target comparison must
   belong to the closed cone of source comparisons for that player. Finite
   nonnegative combinations supply sufficient certificates. Instantiating this
   criterion for the reactive compiler remains open; no baseline-law matching
   requirement should be mistaken for a necessary runtime assumption.
4. **Original types and private recall.** Preserve the joint law of initial types
   and decoded public results, rather than only the public marginal. The checked
   [parameter-outcome regression](../VegasTests/ParameterOutcomes.lean) gives
   equal public marginals with different type-dependent utilities. Types already
   drawn at a root cannot be resampled. Failed attempts and accepted intentions
   must reconstruct the appropriate own recall as in O5.
5. **One coherent translation.** Compose the source-to-graph and graph-to-reactive
   maps, initialized correctness, and the continuation theorem for the same
   compiler and service. A utility-specific optimal recovery policy is not the
   intended compiler. A command-service Nash theorem and a conditional generic
   SPE theorem do not certify the reactive compilation together. The current
   [reactive composition](../Vegas/Game/ReactiveCompilation.lean) defines the map;
   its full correspondence remains open.

## What each proposed repair addresses

| Measure | Intended coverage | What still needs proof |
|---|---|---|
| Explicit source forfeiture, or proved failure elision | O1 | Native/source continuation match with the correct visibility and timing |
| Regular, value-independent inclusion | O2 | Every settling inclusion and the downstream interaction, not just one draw |
| Distinct IDs, unpublished eligibility, at-most-once inclusion | O3 | Whole-service effects of a rebroadcast; fresh duplicates are different envelopes |
| Dependency-authorized submission | Checked public-history enforcement, per-player event isolation, and authorized uniform response laws | Ledger realizability and remaining continuation effects |
| Total recovery with receipt-based reconstruction | O5 | Every legal root and optimality, beyond the checked reconstruction cases |
| Prevalidation plus source-compatible observations | O6 | Complete reactive continuation laws with passive leaks and reactions |

These are semantic and proof obligations on different components, rather than
six compiler flags. In particular, asking for SPE must not silently admit
forfeiture in the source or delete target broadcasts from the deviation space.

## Work order and acceptance criteria

1. **Specify the combined contract.** The [service design](reactive-spe-service.md)
   states source failure admission, inclusion behavior, replay handling,
   submission authorization, and retained observation
   behavior together. Record blockchain realizability arguments separately from
   formal assumptions. The
   [authorization proposal](dependency-authorized-submission.md) records the
   relevant external evidence and outstanding authenticity/finality questions.
2. **Validate authorization against O4.** The abstract exclusion rule and witness
   checks are proved without deleting raw transmissions or passive leaks.
   The public-history monitor and uniform calendar enforce authorization.
   Test the calendar's complete continuation semantics before building a
   blockchain certificate implementation.
3. **Prove a complete base case.** Use a sequential event graph and an explicit
   failure-admitting source interface to isolate the service obligations. Cover
   all proper roots and arbitrary behavioral replacements. This is a proof
   milestone, not the proposed final language restriction.
4. **Generalize through the actual missing dimensions.** Address concurrent ready
   events, multiple players with partial observations, and persistent private
   inputs. Check information closure and remaining opportunities at each step.
   Per-player isolation of authorized unfinished proposals is checked even with
   concurrent foreign commitments. Complete scheduling and information effects
   remain open; do not infer impossibility or full preservation from isolation.
5. **Derive omission checks.** Once the full-interface theorem is established,
   prove when a program may elide forfeiture. Reflection and an automatic checker
   need their own theorems. A checker's failure to certify is not an impossibility
   result.

The regression cases for any candidate contract should cover:

- empty, singleton, and competing pending pools;
- silence, replay of pending/spent IDs, fresh duplicate payloads, and malformed
  packets;
- current, future, and simultaneously ready events;
- valid bindings, irreversible forfeiture, rejected openings, and conflicting
  remembered intentions;
- the last transmission opportunity and approaching deadlines;
- no, partial, and full foreign leaks, with reactions before inclusion;
- earlier deviations by the focal player and by several players;
- original private types and proper-root closure in multiplayer histories.

These are dimensions of the proof and experiments, not a claim that every
combination already has a counterexample. Positive closure requires the native
continuation theorem. A new negative result must identify its legal prefix,
proper root, available information, payoff comparison, and exact compiler/service
scope. A failure of one recovery policy must not be reported as impossibility
of every translation.

Generic game-theoretic transfer belongs in `GameTheoryExtensions`, network and
authorization contracts in `Interaction`, and event readiness, source admission,
reconstruction, and compiler proofs in `Vegas`. The `GameTheory` submodule does
not need to be changed for this investigation.
