# Runtime choices and the scope of preservation

Analysis by Codex. This is a decision aid for the mathematical research project,
not a replacement runtime specification. It proposes a small interface and
states where its conclusions stop. The linked new arguments are paper proofs;
their native compiler adapters remain separate obligations.
The proposed scope and result classification have received independent
mathematical review.

My recommendation is to keep the source language abstract and keep scheduling
exogenous in the first general theorem. State the runtime's observable service
properties, the permitted submission choices, and the utility comparison.
Do not introduce a complete miner economy merely to make these properties
explicit. Equally, do not call an omitted economic or information effect
irrelevant without proving that it is irrelevant to the claimed conclusion.

## The question to fix before choosing a model

For a finite perfect-recall commit–reveal game, choose collateral and compiler
parameters from the program and a public service specification. Then select a
runtime satisfying that specification and a source sequential equilibrium.
Ask whether there exists a target sequential equilibrium with the same joint
law of initial private parameters and declared logical results. Net utility
fidelity, absence of penalties, and reflection of all target equilibria are
additional conclusions, not part of that law comparison by definition.

The source class must say whether withholding is lawful. The existing
settle-late negative compares a mandatory-opening source with an expanded game
containing forfeited withholding. It is not an impossibility theorem for every
program permitting withholding. The target must include the submissions,
observations and costs actually permitted by its declared interface, rather
than only those used by a recommended client.

Two knowledge claims are worth pursuing separately. A pointwise theorem may
choose a different equilibrium policy for each fully specified service law.
A stronger implementation claim uses one policy relying only on public
properties and observed execution. If a persistent service type is unknown,
a common prior and the signals available for learning specify a Bayesian game.
Properties alone do not specify Bayesian beliefs. None of these choices changes
the requirement that collateral precede the selected builder.
[Details and examples](miner-assumptions.md).

## Three legitimate ways to omit a physical detail

**Prove it irrelevant.** Recover the original decision information and prove
that the player's entire remembered auxiliary view has the same likelihood
across compatible hidden source histories. Also preserve logical transitions,
menus, utilities and completion. The source policy can then ignore the
auxiliary view. The [observation-abstraction argument](observation-abstraction.md)
derives consistent beliefs and sequential rationality from replay-channel
properties. It allows correlated private views under its stated conditions;
the checked token-view scheduling theorem is a restricted reference case.
The copied source policy works across the whole specified service class;
consistent beliefs remain service-dependent.

This is a genuine simplification: the high-level program need not specify
every benign delivery token or scheduler state. It is not enough that each
individual token looks independent. Several remembered tokens can jointly
reveal a secret. Nor does the argument remove retry, fee-bidding or timing
choices: those are excluded from that theorem's action interface.

**Bound its effect.** With unchanged information and opportunities, a terminal
utility error bounded by eta at every history gives at most 2 eta additional
gain from any whole continuation policy. Public waiting can be combined with
explicit bounded discounting, fees and financing costs to obtain such a bound.
The copied assessment remains exactly consistent, with the same logical law,
but its rationality is approximate. Strict pure incentives at every decision
can restore an exact result when the margin exceeds the error.
[Costs, the quantitative bound and counterexamples](costs-and-scope.md).

This keeps a fee market out of the game only if fees neither add information
nor change admission opportunities, and the bound covers deviations as well as
recommended play. A bound on honest expected cost alone is insufficient.

Auditable fees offer a separate route for handling controlled bids. A public
state-dependent bidding rule need not force a single numerical paid fee.
Departure enforcement requires authentic evidence and a fresh collection bound,
including departures that successfully obtain priority. Canonical fees still
need the information, service and utility comparisons above. A mere fee cap
leaves controlled choices that can signal. The [fee-policy note](fee-policy.md)
gives the conditional collateral comparison and separates these possibilities
from the fixed-bid producer contrast.

**Exclude it from the claim.** A theorem may condition on already funded
participants, ideal cryptography, exogenous producers, and specified
communication channels. Those are scope choices. It must not infer voluntary
entry, computational equilibrium, coalition resistance or an economic miner
equilibrium. State the excluded feature beside the result and explain which
conclusion adding it would require revisiting.

## A small runtime interface worth testing

The following separates four mathematical obligations. It does not impose four
new runtime mechanisms or adopt the candidate interfaces in the linked notes.

| Obligation | What the runtime must establish | What can remain abstract |
| --- | --- | --- |
| Information | At each source-corresponding decision, remembered packets, timing, receipts and private auxiliary views add no strategically relevant secret information, or their effect is explicitly analyzed. | Network internals and auxiliary state satisfying a proved observation-channel criterion. |
| Service | State owner opportunities, timely publication and finality guarantees over the relevant deviation space; distinguish certain bounds from conditional probability bounds. | The consensus implementation behind those guarantees. |
| Extra actions | Every permitted additional submission is source-equivalent or has a justified incentive/extension argument. Accepted late calls cannot simply be declared forbidden when settlement accepts them without charge. | Packet encodings and audit plumbing once their observation and collection properties are proved. |
| Utility | Specify additive utility versus wealth preferences, delay sensitivity, funded capital, and bounded or exactly canceling costs. | Detailed economics covered by a uniform utility bound; strategic bids or financing choices are outside that simplification. |

The existing asynchronous contract already supplies owner opportunities,
protected sole-identifier inclusion, and completion under its configured
service assumptions. Its settled audit uses final accepted records rather than
an oracle proving when a player privately sent a packet. General preservation
therefore needs actual information and extra-action adapters. Merely increasing
collateral does not establish them.
[Service contract](../../Vegas/Pending/ReactiveAsyncContract.lean),
[settled verdict](../../Vegas/Pending/ReactiveSettledVerdict.lean).

The [native serial information proof](native-observation-criterion.md) gives
a concrete positive input to this task. Canonical commitment packets hide their
chosen values; previous effective openings are source-public before the next
decision. Equal public packet and environment histories therefore couple even
a content-inspecting scheduler and correlated private packet samples. The
restricted game retains one protected source decision per event and makes
other activations forced silence. Its full RAW extension remains unproved.

Not every additional implementation choice needs a charge. The
[compositional theorem](universal-preservation-criterion.md) permits genuine
aliases when each preserves conditional logical execution and a fixed
full-support alias rule proves the required full observation channels. A
private packet-name choice is a useful example. Public names, retries and bids
are not equivalent merely because the application accepts the same value.

For now, retain that abstract service layer. Test alternative public properties
against it rather than silently substituting a new blockchain model. In
particular, a uniform lower bound on late failure is a candidate enforcement
property, not a consequence of miner honesty. A gain-to-additional-collection
bound may be more general than such a failure floor, but still needs physically
available evidence and funded collection under all later policies.
[Enforcement conditions](service-and-enforcement.md).

Nor does every accepted late action require a failure floor. The
[one-opportunity immutable-opening proof](admission-information-boundary.md)
uses a public lower bound on success to make sending optimal at the late
callback. Its consistent successful posteriors then match the source, and
the root's potential gain is proportional to failure probability. It allows
late success to approach one and includes certain success. More timing choices
or a fresh private value choice can change this conclusion; the latter's
counterexample uses attempted-value-dependent failure utility, which is not a
proved native payoff adapter. These restrictions belong in the result, rather
than in a general assertion about public mempools.

That positive now composes across a finite mandatory-opening program in the
[serial late-opening proof](serial-late-release.md). It uses protected bindings,
one late callback per immutable opening, uniform success/loss bounds and a
public failure marker. A single global consistency sequence couples all
successful prefixes and completes all failure entries with their actual
perturbed priors. The source horizon bounds possible losses, but does not
derive the physical callback restriction or conditional inclusion guarantee.

A separate sufficient interface in the same note permits every late success
probability from zero to one. It requires exact callback odds known to the
owner and their classification recoverable by every later strategic player
after success. This is a pointwise theorem with uniform collateral, rather
than a robust complete policy under unspecified service laws. Native readiness
credentials do not by themselves retain callback time or this classification.

There is also a meaningful simplification to test. If the protocol stops and
settles at its first publication failure, an unaccepted opaque binding value
has no later payoff-relevant use. The
[late-binding erasure theorem](late-binding-erasure.md) then permits fresh
value choices at late callbacks as well as fixed-value openings, with any
positive public success lower bound and phase-independent loss accounting.
This is a proposed failure policy for mandatory-success sources; it does not
implement arbitrary source recovery or lawful withholding continuations.

Without stopping, ignoring attempted values in terminal utility is weaker
than erasing them from the future game. Actual private registration retains
transferable opening evidence even for a candidate never admitted. Future
packets and choices may therefore differ. The resulting failure of the
erasure adapter is concrete, but does not itself prove native nonpreservation.

The fixed source horizon can help with whole-game reliability once actual
conditional stage guarantees are supplied. With continuation probability at
least q_k at every compatible service history, completion probability is at
least the product of the q_k; no independence between checkpoints is needed.
The [exogenous-abort analysis](exogenous-abort-preservation.md) makes the
resulting failure branch explicit. Source-independent service and abort utility
unaffected by source actions preserve exact SE, while source-law equality holds
conditional on completion. Unconditional readout error is its abort mass.
This is a useful weaker outcome target, not a redefinition of the research's
principal unconditional preservation goal. Real failure settlement, inclusion
selection and extra submission choices still need their own arguments.

## What two simple producer models add

The [honest-producer candidates](honest-producer-models.md) separate production,
observer propagation and finality without a strategic miner game.

With enough capacity, bounded delivery and bounded block gaps, a call valid
through its inclusion interval has an explicit inclusion bound. If every
permitted relevant transmission precedes a receiver's irreversible decision
by the delivery bound, that receiver sees even excluded or rejected packets.
This removes the partial-observation premise of the particular settle-late
proof. The last permitted transmission time must be a physical interface
restriction or an enforced boundary; a fixed source horizon does not supply it.
These are service lemmas and a restricted single-phase application, not a
general sequence-preservation theorem.

In a one-slot fee-maximizing model, an independent competing transaction occurs
with probability epsilon. A sole late opening succeeds with probability
1-epsilon. Producers follow the same noncolluding rule as epsilon approaches
zero. Bounded plaintext propagation can still give an earlier opening more
exposure than a later opening before the receiver replies. Pending packets
remain readable and eventually reach every observer.

The note completes a paper negative using those production and propagation
laws, a restricted finite submission/observation menu, and an explicit terminal
audit. It incorporates an actual fixed fee for accepted openings. Its negative
applies when the effective forfeit exceeds the reward range, the audit charge
exceeds half that range, exposure lies strictly between zero and one, and late
inclusion is sufficiently reliable. Independent identifiers, scheduled
observations, the auxiliary signal channel and collectible deadline evidence
are material premises. They have not been established for the native compiler.
The result shows that a particular retry-lottery formula and malicious miners
are unnecessary for this comparison, not that producer honesty alone implies
nonpreservation.

## Scope that must accompany a general theorem

“General” should identify what is quantified over. Universality over finite
source games does not imply universality over blockchain behavior. A theorem
about a restricted submission interface must advertise that restriction.

| Aspect | Default scope for the proposed research target | Limitation to report |
| --- | --- | --- |
| Cryptography | Ideal hiding, binding and authentication; metadata separately covered by the information condition. | No security-parameter or computational-equilibrium claim. Owners can still disclose values they know through permitted channels. |
| Producer behavior | An exogenous service law from a public class. | No equilibrium of miners, bribes or outcome-dependent producer investments; noncollusion alone does not establish the law. |
| Player rationality | Finite perfect-recall expected-utility SE against unilateral whole-policy deviations. | No coalition, bounded-computation or memory-cost claim. |
| Participation | Funding and entry are prior conditions unless explicitly modeled. | Continuation preservation does not prove willingness or ability to participate. |
| Costs and time | Exact utility cancellation, or explicitly bounded utility error and physical waiting. | Small monetary costs can remove tied exact equilibria; a logical horizon need not bound lock time. |
| Resources and finality | Guarantees cover all allowed load, bids, retries and rollback observations. | A service guarantee only on recommended play does not cover profitable capacity or priority deviations. |
| Communication and payoffs | The declared channels and utilities exhaust the modeled choices. | An off-chain disclosure or external financial position needs its own argument; contract rejection cannot erase knowledge. |

These defaults are proposed scopes, not newly approved semantics. Where an
aspect is outside a result, say so at its statement rather than relying solely
on this table. The [result-card workflow](workflow.md#required-result-card)
makes that requirement explicit.

## Next mathematical handoffs

First, test the actual retained runtime against the replay-channel criterion,
including remembered private leak samples and receipt metadata while old
secrets remain. If it fails, exhibit the observation that defeats it; do not
hide that observation by weakening the player's recall.

Second, analyze the target's permitted timing and submission actions under
public service properties. A preservation route needs a source-equivalent
continuation or an enforceable additional-collection argument. A negative route
needs the full native menus, observations and settlement audit, not just an
embedded bad subgame.

Third, add an explicit utility comparison to whichever information/action
interface succeeds. Exact preservation under declared time indifference and
canceling costs, approximate preservation with bounded costs, and exact
strict-margin preservation are distinct useful claims. Their combination needs
one game and one consistent assessment; proofs for incompatible interfaces
cannot be multiplied into a compiler theorem.
