# A finite broadcast runtime with direct ledger audit

This document specifies the runtime used by a fresh-service preservation
argument without an honest auditor, relay or evidence collector. Every bounded
authenticated current-session application body is recordable, including a
malformed inner game call. The primary construction therefore collects audit
evidence directly from the ledger; it needs no strategic reporting stage.

The target has one broadcast/submission primitive. Broadcasting such a body
creates the funded recording obligation defined below. A network observation
is not itself a submission. There is no second operation which announces the
same authenticated bytes while declining the submission transition. This is an explicit
restriction of the runtime communication model. It is not a consequence of a
compiler, transaction signatures, or ordinary account-nonce replacement.

The chain's stated inclusion contract is an assumption about the blockchain
service. Evidence comes from the actual public chain record. No unseen
observer's private retention is counted as collection. The two substantive
availability premises are that broadcast is submission and that submitted
bodies have the stated nonrevocable timely-inclusion service.

The [fresh-service proof](se-asynchronous-support-weakening.md) supplies the
proper-core timing and reset argument. The
[authenticated comparison](se-asynchronous-authenticated-construction.md)
supplies the semantic repair and raw-action comparison. This specification
gives their concrete transaction, observation and ledger-audit interfaces. It is
mathematical work; it does not add Lean declarations or assert an EVM
implementation.

## 1. Finite data and authentication

Fix a finite player set P, a finite time horizon, a finite source program with
finite payload domains, and finite bounds on attempts, bodies and broadcast
copies. Initialization has finite support, as does every source sampling
kernel on every reachable retained or raw state. The fixed horizon therefore
has finitely many source and runtime histories; a finite program by itself
would not imply this. Its private source values may be
arbitrarily correlated. Auxiliary names, network coins and service coins are
independent of the whole source realization, except for dependence on already
public semantic parameters fixed at the entry to the current window. These
parameters remain fixed for that window's service law.

An authenticated application body e has an immutable author auth(e), session,
domain tag, bounded fields and an ideal authentic signature over the complete
body. A player may create bodies under its own identity and retransmit bodies
it knows. It cannot create another player's signature. Actual occurrences also
record their broadcaster; forwarding does not change the signed author.

Authentication for the fresh current session is an outer requirement. A valid
signature made for an unrelated session is not a chargeable current-session
body, even if somebody forwards it here. The intrinsic domain defects below
concern malformed inner action/domain tags inside an authenticated current-
session envelope. They never turn somebody else's forwarding of an outside-
session signature into an offense by its original signer.

The finite message algebra is typed and nonnested. A source value, a handle,
an opening certificate and an authenticated application body are distinct
sorts. Application fields cannot contain another authenticated application
body or an arbitrary encoding of one. The separate reporting extension uses
an expressly defined finite list type. The primary direct-ledger proof does
not need an own-free report bundle, but still uses the declared finite typed
message domain. It is not a claim about arbitrary byte-string protocols.

An ideal commitment handle has one immutable private typed meaning once it is
bound, and its public name reveals no function of that meaning. A usable
binding has a unique verifiable opening at its declared component. A private
unusable candidate has no such opening. Phase authorization and accepted-binding
certificates are distinct from the opening proof. The first certifies an
actually installed public phase; the second identifies the exact accepted
component binding. Initial bindings also need the actual resolve-phase
authorization before a protocol opening is allowed.

These ideal primitives exclude a separate unauthenticated preimage or arbitrary
chat channel. If such a channel is admitted, its information and evidence
effects need their own theorem. A signature on one body cannot be used to
attribute a modified or stripped body to its original author.

Let E_tx be the finite set of all bounded authenticated current-session
application bodies. Outer recording is total on this domain. Proper calls,
malformed inner calls, stale calls, conflicts and exact retransmissions all
use this same interface. In the primary construction E_raw is empty: there
is no authenticated body class which can be broadcast but is refused recording.
An unrelated-session signature or unauthenticated string is not silently
reclassified as a chargeable current-session body. An enlarged communication
interface admitting such traffic needs its own information and incentive proof.

## 2. Private plans do not consume future semantic menus

Each physical attempt and source component has a reserved fresh namespace.
The current legal fresh names depend on public syntax and ordinary operational
freshness records, not on private source values, carrier nonces, or a count of
unpublished private plans. The primary construction uses one canonical name
and one canonical proof representation per current slot. Every declared raw
body is still recordable; a second conflicting representation cannot cancel
the canonical body's job. Old-public-body replay coordinates retain their
positive product law. There is no unspecified representation-floor error.
Canonicality is part of the valid current-slot grammar or the ideal primitive's
unique representation, not merely a reference-policy convention. A different
current representation is a positively verifiable structural fault. If a
backend instead permits several valid first representations, it must retain
and analyze those aliases; choosing one in the reference policy is insufficient.

A player may keep arbitrary bounded private scratch plans: intended values,
possible handles, coins and proposed future messages. Planning changes no
network queue, public certificate, service credit or physical component
binding. It cannot reserve all of a future slot's names, freeze a name's
meaning, spend a future submission allowance, or remove a core source action
from its future menu. Changing a
private plan before its first binding use is therefore still private planning.

At the first qualifying binding transmission for an unused physical component,
the runtime atomically assigns that component's selected fresh handle its
private meaning and records the emitted opaque handle. This is the semantic
choice point. The current source observation is already available there.
A raw choice may have an unusable or guard-invalid meaning. Reusing an already
bound handle in another component is a distinct, positively witnessable case;
it does not change the old meaning.

This gives the required pre-public-exit private-shadow interface. Given a raw scratch plan,
the comparator remembers it in private virtual memory. At its first proper
binding use it chooses an admitted value from its actual current source
observation and installs that value behind the same still-unused public name.
The raw and comparator private heaps differ, but the opaque wire is the same.
No earlier source information is used clairvoyantly. The comparator's scratch
simulation cannot consume a reserved current namespace or a transaction credit.

After public exit, newly chosen structurally clean raw handler bindings are
copied literally. No guard-admitted selector is assumed to exist at an
arbitrary failure state. A pre-exit hidden difference has either reached its
irreversible bad save, where the comparison stops, or has been erased by the
commitment rollback. Old discarded values can remain in virtual memory but
cannot create a new authorized current opening.

Initial source bindings are different: their values come from initialization
and are retained exactly. They are not replaced by this shadow construction.

## 3. Funded body keys and transaction validity

For each potential qualifying body e, use a collision-free canonical key k(e).
The mathematical key space is finite. Different conflicting bodies have
different keys even when their application slot is the same. The primary
construction has no report-body domain.

An immutable inbox/account validator fixes the following rules for the whole
session:

1. A valid operation for k(e) can do only one thing: record the complete exact
   body e in the public inbox. A replacement using that key must record that
   same e. It cannot call a cancellation, transfer away the allowance, or
   record a different body.
2. The key is consumed only together with that full public record. If a later
   operation finds the key consumed, e is already public. There is no outcome
   which merely spends the key or fee allowance without recording e.
3. The record operation is total and has a declared resource bound. Validation
   rejects insufficient execution resources. Inner game rejection does not
   revert the outer record: recording and the bounded, failure-returning game
   interpreter are separate stages.
4. Each author has a segregated reserve for the largest number of distinct
   bodies it can submit in one run. Submission irrevocably earmarks the
   recording allowance for that actual body key. Other jobs cannot spend it.
   Uncommitted funds and earmarked allowances remain locked through publication
   and audit; the validator cannot be changed during the session.
5. Canonical copies of e share its key. Sending another copy does not create a
   new publication job or reset its start time.

These rules do not reserve money for every possible payload. If author i has
at most H_i action opportunities and may introduce at most b_i fresh bodies
per opportunity, put N_i=H_i*b_i. With per-body recording cost at most c_i,
reserve N_i*c_i for that author. At a prefix after k opportunities at most
k*b_i jobs have consumed earmarks, so at least (H_i-k)*b_i full allowances
remain. Every later permitted fresh batch is still funded. Earlier raw
choices and private planning cannot exhaust a later core choice's allowance.
Different authors' reserves are disjoint.

Canonical retransmissions create no new job or earmark. A current-session
body first becomes known to a nonauthor only through a prior broadcast or
public record; forwarding it therefore cannot introduce an unbudgeted new
author job. Initial source commitments are not a library of unsubmitted
current-session signed envelopes. Fixed genesis records, if present, are
funded and counted separately. The model does not grant future phase
capabilities by enumerating certificate atoms.

The relevant validity invariant is

    submitted(e,a) and not recorded(e,t)
       implies e still has a valid funded recording operation at time t.   (1)

To prove (1), inspect every transition. Another body uses another key. An
identical copy leaves the job and key unchanged. A purported cancellation or
different-body replacement is rejected by rule 1. Spending the same key
establishes recorded(e,t) by rule 2. Fee depletion, withdrawal and code changes
are excluded by rules 3 and 4. Game expiry affects only the inner interpreter.
This is an invariant about public validation and locked resources, not a relay's
promise to remember something.

Thus the publication reserve is sum_i N_i*c_i, sized by one execution's
largest possible submission count, not by |E_tx|. Audit collateral is separate.
Every occurrence, including a replay, also has a declared intake cost covered
by its per-step multiplicity bound. A player's raw flood cannot consume
another author's reserve or an already earmarked job allowance. This accounting
removes affordability interference; it does not prove delivery or inclusion.

The crucial remaining service premise is that the chain's timely-inclusion
contract applies to these persistently valid funded body-key operations.
Ordinary signed account-nonce transactions do not imply (1): a different
transaction may consume their shared nonce without recording the old body.

[ERC-4337](https://eips.ethereum.org/EIPS/eip-4337) provides account-defined
validation, keyed nonce domains and paymaster mechanisms, which are useful
components of such a design. The standard also permits same-nonce replacement,
withdrawable deposits and execution failures. Those components alone prove
neither the body-bound invariant (1) nor timely inclusion of a user operation.
An implementation must enforce the stronger immutable validation, funding and
nonreverting-record rules, and establish the inclusion service separately.
No deployed realization is asserted here.

## 4. Global runtime state and transition order

A state contains:

* a public clock t, public inbox L, the public controller state and its issued
  certificates;
* the private source cells and each player's scratch/owned-binding state;
* a body-key map, recording jobs and in-flight broadcast occurrences;
* each player's complete own action and receipt history;
* base-game and audit phase markers and their separate balances.

The full mathematical state can contain a body which no player has received.
That does not place it in any player's observation. The public ledger is the
source of common public records.

At a block decision, a player chooses up to b_i fresh own signed bodies and
a bounded replay multiset of known bodies. Each replay coordinate has a
fixed finite multiplicity bound. There is no smaller aggregate cap coupling
these coordinates: one new current body remains available together with
every legal replay selection. In the proper core the current body has a
canonical representation. Fresh bodies and replay occurrences have separately
bounded intake work. All fields and alphabets remain finite.

Here a replayable known body is one already broadcast in this run or a fixed
genesis record. Knowing a privately prepared or signed plan does not make its
first transmission a replay: that first network use consumes the fresh-body
cap. Own recall and authenticated receipt determine these categories locally.

If G is the number of fixed genesis bodies and L bounds each replay
multiplicity, at most G+sum_i N_i distinct bodies can be known in one run.
Thus one action has at most b_i+L*(G+sum_i N_i) occurrences. This per-run
bound funds intake without reserving for every payload in the alphabet and
without introducing a shared cap that couples a current action to old replays.

The following transitions define the communication interface.

**Private planning.** Change only the actor's scratch state, as in section 2.

**Broadcast/submission.** Emit the chosen ordinary network occurrences. For
each e in E_tx whose key has not previously been submitted or recorded, create
its publication job with admission time a=t. This is an actual submission
transition of this runtime, not an inference made from another player's
receipt. There is no E_raw case in the primary model.

**Partial observation.** Chance produces the permitted observations of
broadcast traffic. The sender cannot select a confidential audience. Players
may observe different bodies, opaque metadata, counts or duplicates. Complete
body receipt is not an audit requirement. The factorization, freshness and
reset conditions in section 5 restrict these kernels; arbitrary value-blind
projections are not automatically admitted. Author and broadcaster are distinct.

**Public recording.** When e's job is included, append its complete body and
key to L and consume that key. Then evaluate its inner game call. Rejection,
staleness or an unusable opening changes the inner result, not L. This is the
only way a previously unseen body can change the game controller. The body is
public at or before that effect, rather than merely retained by an ingress.

**Settlement.** At a public window boundary, first apply all inbox records
through that boundary, then compute completion, missing owners and excluded
owners. The next semantic decision is disabled until this result and the
required recording interval are public.

**Freeze and drain.** At the public terminal point T0, freeze base payoffs and
end new strategic submissions. Pending publication and observation events
continue. Set TA>=T0+Delta, so every submitted body is recorded by audit.
The final verifier consumes actual public bodies, never a private monitor's
assertion. The optional reporting extension in section 8 uses a later
submission cutoff instead.

## 5. A fresh independent inclusion service

For a first qualifying submission e at a, the base service gives an inclusion
time T_e in {a+1,...,a+Delta}. Its law can depend on the public body class and
a, conditioned on the fixed public parameters at this window's entry. The
body class cannot inspect semantic payload values, including values already
disclosed elsewhere. New within-window publications, receipts and controller
updates do not change this law. The service coins are fresh relative to
all observations before that first submission, and independent of other
bodies' service processes. Subsequent sends, cancellations, replacements,
replays and raw floods cannot alter this job.

For a finite explicit instance, draw a body-local delay d_e from a fixed finite
law when its first submission occurs and set T_e=a+d_e. The laws may be
deterministic. Another instance uses independent body-local inclusion coins
at successive blocks and compulsory inclusion by a+Delta. Neither instance
requires positive probability of every delayed-receipt pattern for the fresh
proof.

Reserve enough application recording capacity to include at most sum_i N_i
due bodies under the per-run raw bound, accounting for their maximum sizes.
Thus the inclusion rule is well-defined under
every deviation. It need not clear unrelated transactions, and it may include
only a subset of the application's jobs in an earlier block. There is no
shared nonce, allowance or congestion queue which lets one body interfere
with another. Reducing this deliberately generous capacity is a separate
refinement problem.

From (1) and this inclusion premise,

    submitted(e,a) implies recorded(e,t) for some t<=a+Delta,                (2)

under every subsequent raw strategy profile. This is the retained-prefix
publication lemma. If a conflicting operation consumed the same key, rule 1
already gives the desired full record of e. A different body cannot consume
that key.

For a deadline D, put p_e(a)=Pr(T_e<=D). Before a first submission, no observed
network history predicts its fresh job coins. Hence

    q*_e(t) = max_{a>=t} p_e(a)

where a ranges over the finite remaining admissible current-window times,
with never-submit included at value zero. This maximum is attainable by a
common clock-based submission policy. At protected times
a<=D-Delta, p_e(a)=1. Conditional on any fixed foreign first-admission,
failure and archive scenario C, an adaptive policy tau has success probability
E[p_e(tau)|C]<=q*_e(t). This is the precise timing input to the fresh proof;
cross-body independence and conditional freshness are substantive premises.

The observation conditions are separate from audit collection:

1. **Semantic opacity and factorization.** At a binding window, conditional on
   the retained source information J, the operational observation law cannot
   inspect unrevealed candidate meanings or other hidden semantic values. The
   source/operational path law factors into the source weight and a mechanical
   weight. At reveal windows, authorized visible payloads may be included;
   their selection mask depends on mechanical data rather than their values.
2. **Own-service freshness.** No pre-submission observation predicts the
   fresh coins of the not-yet-submitted own body. Together with independent
   service, this gives the conditional-on-C timing calculation above.
3. **Independent service.** Other broadcasts, replays and observation events
   cannot change an admitted body's service law or create service competition.
4. **Reset compatibility.** The next namespace's observations and service
   are independent of discarded old traffic, including changes to old replay
   policies. The actual old record is a causal auxiliary observation of the
   retained coarse own history, and actual menus factor into current actions
   and inert old replay coordinates. This is the action/information quotient
   proved in the fresh-service construction, not an instruction to forget.

Complete observation, partial bodies, metadata and counts can satisfy these
conditions. For example, counts indexed by the current namespace and generated
from its fresh mechanical process can be retained while old-namespace records
are auxiliary. An unlabeled total count mixing old flights with new traffic
need not satisfy the reset condition: remembered old flights may reveal which
new event produced a count. Value blindness alone does not prove the required
conditional factorization or reset. Complete-body receipt is unnecessary for
the primary audit, because the body is unavoidably recorded after submission.

## 6. Source windows, rollback and reset

Keep the source's maximal private-choice blocks and original public samples.
A binding transmission batches one opaque handle per component, not the
disclosure of every component. A reveal transmission opens only components
of the current original reveal block. Apply their source transitions in the
original syntax order. A guard remains pending until its last input is public;
do not move a reveal across an intervening sample or commitment to check it
earlier.

Each window has fixed public readiness r, last protected time A and settlement
D=A+Delta. Its readiness and end are not advanced by an earlier arrival.
Every owner may submit at the modeled times. A qualifying late body can still
arrive before D; waiting past A is not itself an audit offense.

If a commitment window fails, roll back the whole unsaved current commitment
block and exclude its missing owners. A saved earlier binding and its guard
dependencies survive later rollback. Every live saved obligation eventually
receives its truthful publication, is genuinely erased while still unsaved,
or has an excluded owner. A missing publication or a rejected completed guard
excludes its owner. Terminal settlement cannot leave an active owner's saved
obligation unchecked.

After a reveal closure c, wait until at least c+Delta before enabling the next
binding choice. Every qualifying opening submitted by c is then actually
public by (2), even if its game call was rejected or its owner is excluded.
No player is instructed to infer an unpublished opening from someone else's
private receipt.

For the fresh-service proof, use the explicit intermediate reset from
[the support-weakening construction](se-asynchronous-support-weakening.md).
It retains the public archive, excluded set, live private inputs/bindings and
saved obligations. It discards only the effective use of failed unsaved
choices and old operational metadata. All old-namespace replay occurrences
are filtered by the prescribed continuation, with independent full-support
replay coordinates. They remain legal and visible. Fresh namespaces and
independent new service make their effective action a no-op. Positive offenses
and excluded owners' first old disclosures are temporarily restricted and
restored by the final action-extension comparison.

This action/information quotient matters. A forgotten private candidate may
otherwise provide an extra authentic opening action, and old duplicate
history may otherwise predict noise in a future replay signaling channel.

## 7. Submission gives unavoidable ledger evidence

Let A_bad be the first submission of an auditable forbidden body before base
freeze T0, unless semantic debt or own exclusion has already supplied the
stopping comparison. This is an action event, not the first receipt or first
observable effect. If it occurs in a batch, the whole batch is committed to
recording by the same transition. A violation involving two new components
of that batch therefore has both witnesses.

Every authenticated body is in E_tx. Equation (2) makes the submitted body
public by TA, under every later raw profile. Earlier retained counterparts
have the same persistent promise. For the deterministic positive verifier:

| Violation | Actual final public witness |
| --- | --- |
| Intrinsic inner format, owner, phase or certificate defect | The submitted current-session body itself |
| A conflicting second body for one physical slot | Both submitted bodies |
| Reuse of one handle across bindings/components | Both binding bodies, or both indexed components in one body |
| An active owner's new body for a closed old slot | The new body and that slot's accepted public body |
| An excluded owner's first historically valid old disclosure | Use permanent own payoff; do not invent an offense |

Thus every positive witness W needed at A_bad satisfies

    W subseteq P_final,                                                   (3)

where P_final is the actual application inbox at TA. The verifier uses
unordered positive pairs; it does not need a guessed global emission order.
Nobody must privately receive, recognize, preserve or report the witness.
The publication job is an explicit consequence of submission, not common
knowledge of the body before recording.

The causal semantic shadow still handles non-auditable bad private choices.
Before public exit it can replace an unusable or guard-invalid current choice
behind the same canonical opaque name. The raw and shadow wire is identical.
An unsaved current block may be erased by rollback before any genuine opening
is authorized. If its earliest bad obligation is irreversibly saved, truthful
completion eventually checks its false guard; withholding or an unusable
opening instead excludes its owner. In either case that owner's eventual
base payoff is F_i. Guard checking occurs when the last required input is
public, not necessarily at the first changed opening. After public exit new
structurally clean raw handler choices are copied literally.

At A_bad, the comparator can stop sending the offending body and continue
quietly. Subsequent raw observations may change arbitrarily within the stated
runtime: the complete audit charge is already inevitable. There is no need
to simulate a suppressed body's flights until receipt or to impose a
complete-envelope observation condition for this comparison. Before A_bad,
matching physical broadcasts and shadow-compatible private meanings give the
same observations by semantic opacity.

For refundable collateral D_i>=U_i-F_i, submission of the positive witness
caps the raw terminal net payoff by U_i-D_i<=F_i. Own exclusion or saved bad
debt also caps it by F_i. A clean retained quiet continuation has payoff at
least F_i. On a branch with no stopping event before base freeze, the coupled
base utilities agree and later nonnegative audit charges cannot improve the
raw payoff. This proves the direct continuation comparison for one causal
policy over the entire actual retained information set. It quantifies over
all extending raw opponents' profiles; no reporting strategy is fixed.

## 8. Strategic reporting as a separate extension tool

The primary construction has no strategic reports, report reserve or report
incentive assumption. Its time names are T0 for base freeze and last strategic
submission, and TA>=T0+Delta for final ledger audit.

For a different model with authenticated bodies that can be observed but are
not recordable, the [strategic reporting construction](se-strategic-reporting-mathematics.md)
is a separate tool. Use TK=T0 for the frozen evidence snapshot, TS for the
last reporting/application submission in that extension, and
TA>=max(TS+Delta,TS+Delta_R) for its final drain and audit. Physical observations
continue after TK; the snapshot is only the prescribed strategy's remembered
input.

That extension requires complete positive witnesses to be held by nonauthors
or eventually be public; guaranteed delivery of chosen canonical reports;
segregated reporting entitlements; monotone authorwise verification; and
zero incremental reporting cost with no payoff redistribution. Its common
fully mixed sequence proves a selected report-all equilibrium. The primary
ledger theorem uses none of these reporting incentives.

Reporting does not by itself close an announcement-only interface for proper
protocol bodies. A failed owner's privately announced value may remain
unpublished at the next semantic binding decision even if reported at terminal
audit. Such a change affects the retained timing/information proof as well as
final evidence collection. It must be analyzed separately.

## 9. Exact scope of the runtime theorem

For the finite target specified here, all authenticated bounded session bodies
are recordable. Body-key validation proves persistent eligibility; the
nonrevocable timely-inclusion assumption turns actual submissions into final
public records. Positive audit witnesses are therefore collected directly,
without a trusted monitor and without strategic reporting. Source timing,
rollback and semantic repair use the separate observation and reset conditions
stated above.

The substantive runtime assumptions are a closed authenticated message domain;
one broadcast/submission primitive; immutable body-key recording; fresh
independent inclusion with sufficient per-run capacity; the stated source and
reset observation factorization; and fixed public windows/barriers. They are
not consequences of source compilation or of an ordinary transaction deadline.
No publication event is invented from another player's receipt.

In particular, a different API may let a player show the same chain-valid
signed bytes to peers without submitting them to this service. Then observing
those bytes proves neither a job nor equation (2). A retained-prefix body can
be absent from the final ledger, and a failed owner's announced value can
remain private past the next binding barrier. Nor may an omitted transaction
wrapper be blamed on the original signer: another party might have stripped it.

That larger interface is not refuted here. Its correct-but-uncompleted opening
still leads to its author's exclusion, and an opening which completes makes
its value public. Those facts do not alone supply a legal comparison under
every extending opponents' policy. Either include announcements in a retained
timing/information construction and prove its comparisons, or specify an
independently authenticated auditable message class with actual evidence
availability. Calling every observed envelope a submission does neither.
