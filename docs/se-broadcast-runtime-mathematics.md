# A finite broadcast runtime with strategic evidence reporting

This document specifies the runtime used by a fresh-service preservation
argument without an honest auditor, relay or evidence collector. It separates
three objects which must not be conflated: an authenticated application body,
a qualifying transaction submission, and a participant's observation of a
network occurrence.

The target has one broadcast/submission primitive. Broadcasting a qualifying
funded transaction creates the chain obligation defined below. Receiving an
arbitrary signed envelope does not create that obligation. There is no second
operation which sends the exact qualifying transaction bytes to a private
audience while declining the submission transition. This is an explicit
restriction of the runtime communication model. It is not a consequence of a
compiler, transaction signatures, or ordinary account-nonce replacement.

The chain's stated inclusion contract is an assumption about the blockchain
service. Evidence is obtained either from an actual public chain record or
from strategic players who received it and later choose to report. No unseen
observer's private retention is counted as collection.

The [fresh-service proof](se-asynchronous-support-weakening.md) supplies the
proper-core timing and reset argument. The
[authenticated comparison](se-asynchronous-authenticated-construction.md)
supplies the semantic repair and raw-action comparison. This specification
gives their concrete transaction, receipt and reporting interfaces. It is
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
body or an arbitrary encoding of one. Reports are a separate, expressly
defined finite list type. This restriction is needed by the reporting
incentive proof; it is not a claim about arbitrary byte-string protocols.

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

Let E_tx be the finite set of possible qualifying authenticated inbox bodies.
Let E_raw contain the other authenticated session bodies. An ordinary proper
binding or opening is in E_tx. A malformed inner game call may also be in
E_tx: chain eligibility is deliberately broader than game acceptance.
Every body in E_raw has a positive intrinsic format/domain/authorization
violation, unless it is an explicitly retained transport alias. A body which
is perfectly valid protocol communication but is neither submitted nor
intrinsically faulty is not silently placed in E_raw; that is the separate
announcement-only boundary discussed below.

## 2. Private plans do not consume future semantic menus

Each physical attempt and source component has a reserved fresh namespace.
The current legal fresh names depend on public syntax and ordinary operational
freshness records, not on private source values, carrier nonces, or a count of
unpublished private plans. A fixed full-support fresh-name law can be used,
with service and policies equivariant under consistent renaming. One canonical
name per slot is a simpler special case.

A player may keep arbitrary bounded private scratch plans: intended values,
possible handles, coins and proposed future messages. Planning changes no
network queue, public certificate, service credit or physical component
binding. It cannot reserve all of a future slot's names, freeze a name's
meaning, or remove a core source action from its future menu. Changing a
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
different keys even when their application slot is the same. A report body
uses a disjoint key and funding domain.

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
4. Funds for every key which can occur in the declared raw domain are locked
   until its publication obligation and the final audit are discharged. Other
   bodies cannot spend that key's allowance. The validator and these rules
   cannot be changed or withdrawn during the session.
5. Canonical copies of e share its key. Sending another copy does not create a
   new publication job or reset its start time.

These rules can be described without assuming that every body is known at
deployment: a fixed body-indexed validation rule and a reserve covering the
entire finite domain suffice. The mathematical model does not give players
future phase capabilities by enumerating opaque certificate atoms.

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

For a finite bound N_tx on distinct qualifying bodies and a maximum recording
cost c_tx, a reserve N_tx*c_tx suffices for this deliberately large baseline.
Use separate reserves for base-game obligations, audit collateral and report
transactions. A player's raw flood cannot consume another body's or another
reporter's allowance. This accounting removes affordability interference; it
does not prove network delivery or inclusion.

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
* base-game, reporting and audit phase markers and their separate balances.

The full mathematical state can contain a body which no player has received.
That does not place it in any player's observation. The public ledger is the
source of common public records.

At a block decision, a player chooses a bounded multiset of new own signed
bodies and known signed bodies to retransmit. Each known-body coordinate has
a fixed finite multiplicity bound. There is no smaller aggregate cap which
would prevent an otherwise available current submission while retaining
the selected replay coordinates. All fields and alphabets remain finite.

The following transitions define the communication interface.

**Private planning.** Change only the actor's scratch state, as in section 2.

**Broadcast/submission.** Emit the chosen ordinary network occurrences. For
each e in E_tx whose key has not previously been submitted or recorded, create
its publication job with admission time a=t. This is an actual submission
transition of this runtime, not an inference made from another player's
receipt. For e in E_raw, create occurrences but no chain publication promise.

**Partial receipt.** Chance delivers complete occurrences to some players.
The sender cannot select a confidential audience. Players may receive
different bodies at different times and may observe duplicates. Author and
broadcaster are not conflated. Unreceived occurrences have no effect on other
occurrences' delivery, inclusion jobs, controller state or player observations.

**Public recording.** When e's job is included, append its complete body and
key to L and consume that key. Then evaluate its inner game call. Rejection,
staleness or an unusable opening changes the inner result, not L. This is the
only way a previously unseen body can change the game controller. The body is
public at or before that effect, rather than merely retained by an ingress.

**Settlement.** At a public window boundary, first apply all inbox records
through that boundary, then compute completion, missing owners and excluded
owners. The next semantic decision is disabled until this result and the
required recording interval are public.

**Freeze.** At the public terminal point T, freeze base payoffs. Each player
records its then-current knowledge K_i for its prescribed reporting strategy.
The physical network does not stop delivering messages, and the player does
not lose later observations. Pending publication obligations continue to
record. Later communication cannot change the frozen base game or revoke
already submitted recording/reporting jobs.

**Reporting and audit.** Apply sections 7 and 8. The final verifier consumes
actual public bodies, never a private monitor's assertion.

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

Reserve enough application recording capacity to include every due body under
the declared finite raw bound. Thus the inclusion rule is well-defined under
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

is attainable by a common clock-based submission policy. At protected times
a<=D-Delta, p_e(a)=1. Conditional on any fixed foreign first-admission,
failure and archive scenario C, an adaptive policy tau has success probability
E[p_e(tau)|C]<=q*_e(t). This is the precise timing input to the fresh proof;
cross-body independence and conditional freshness are substantive premises.

Receipt kernels can be deterministic complete observation or partial packet-
local observation. New-body receipt kernels must be independent of discarded
old traffic after a reset. Mere blindness to source values does not justify a
persistent router state which predicts later service or changes later new-body
reception.

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

## 7. Freeze knowledge, then let players report

There is no monitor. At freeze time T, let K_j be the complete authenticated
application bodies actually received or read from the ledger by player j.
Perfect recall retains them. Reports concern these frozen sets, not messages
newly learned from another report.

Use a fixed finite set of simultaneous reporting rounds, with an opportunity
for every player before a public cutoff T_R regardless of previous reports
or raw communication. A player may submit a canonical bundle of any known
foreign-authored bodies, with enough capacity to report its entire frozen
foreign set, or omit it. A partial, malformed or omitted earlier report does
not consume the ability to submit the canonical bundle at a later round.
There is no first-report quota. The separate
report funding and capacity cover the entire finite reporting domain, under
every profile, even if players flooded the gameplay network.

The declared raw tail may also contain new application submissions through
T_R. After that last submission cutoff only the fixed service and audit drain
remain; there is no new unbounded stream of strategic submissions.

A qualifying report submission is another actual funded chain operation.
Its immutable inclusion deadline is no later than T_R+Delta_R. An adversary
cannot cancel another report, make another reporter's allowance unavailable,
or displace that report with its own spending. The audit waits until

    T_audit >= max(T_R+Delta, T_R+Delta_R).                                  (3)

The first term also finishes every tail-created application job. In particular,
it makes all pre-freeze qualifying counterparts available even if they were
not public when knowledge was frozen. A reporter need not yet
know which earlier body will complete a conflict witness: report the body it
has, then let the final deterministic verifier combine actual public records.

The report-all strategy submits K_j restricted to authors other than j.
It has zero net player cost and no positive bounty. Penalties are not paid
to other game players. Each penalty against i uses only i-authored application
bodies and fixed public controller records. The nonnested message algebra
ensures that reporting a foreign body does not also disclose an unlisted
i-authored application body hidden inside it.

Fix a reporting information set. Already submitted foreign bundles remain
fixed; the prescribed future canonical bundles are fixed by each reporter's
own snapshot and do not depend on later receipts or the current report.
The snapshot is a strategy record, not an artificial restriction on what
players physically know. All qualifying reports arrive by (3).
Changing player i's report of foreign bodies therefore changes no terminal
evidence against i, no frozen base utility and no fee paid by i. Report-all
is a best response at every such information set. If extra report actions
voluntarily reveal one's own incriminating body, they can only lower that
player's payoff.

This proves a strategic reporting equilibrium. It does not assume players
honestly report every observation under every strategy profile. The raw
comparison is first made in the reduced game with report-all fixed; a
vanishing fully mixed reporting perturbation then supplies one consistent
equilibrium of the strategic-reporting game. Its finite-horizon reporting
error tends to zero uniformly.

## 8. Exposure gives actual evidence, without private capture

Before the base freeze T, let the effective exposure of a previously
suppressed body e be the first of:

* full receipt by a game player j different from auth(e); or
* full public recording of e in the inbox.

Private retention by an unnamed ingress is not an exposure used by this
lemma. If e can affect execution, the record transition has already exposed
the full body publicly. If e has not been received by a nonauthor and is not
public, packet-local noninterference says it has not changed anybody else's
information, any other service job, or the controller. Own scratch and
unreceived flights can be simulated privately.

At an effective exposure e before freeze, the reduced report-all game has the
following collection facts.

| Violation | Source of the actual final witness |
| --- | --- |
| Intrinsic format, owner, phase or certificate defect | e itself, from the public inbox or a nonauthor reporter |
| A conflicting second body for one physical slot | e plus the retained earlier proper body's public record guaranteed by (2) |
| Reuse of one handle across bindings/components | The two signed binding records, or the two indexed components of one signed body |
| An active owner's new body for a closed old slot | e plus that slot's already accepted public record |
| An excluded owner's first historically valid old disclosure | No fabricated offense: use the permanent own-payoff comparison |

For a private conflict, no reporter must already hold both bodies. The earlier
retained body is an actual qualifying submission, so it remains due for
publication under every later deviation. The final verifier uses unordered
positive pairs, not a guessed global emission order. If e is never effectively
exposed before freeze, it had no effect on the base game; an unreported body
known only to its author cannot create an additional base-game advantage.

For malformed inner calls which are nevertheless in E_tx, full public logging
alone supplies the first row. For nonqualifying e in E_raw, nonauthor receipt
and strategic reporting supply it. These are two different proofs of
availability. Neither treats signature validity as evidence retention.

The clean retained semantic shadow has the usual stopping alternatives.
An unsaved bad binding may be erased by rollback before a genuine opening is
authorized. An irreversibly saved earliest bad binding forces its owner to
exclusion: truthful completion eventually checks its false guard, while
withholding or an unusable opening also excludes it. A directly forbidden
body stops at effective exposure and yields the positive witness above.
All private simulations and stopping choices use one causal own-information
policy, not hidden-state-dependent comparator selection.

With permanent base floor F_i, upper base bound U_i and refundable charge
D_i>=U_i-F_i, an exposed offense has raw net payoff at most F_i in the reduced
report-all game. Own exclusion or a saved bad obligation also caps raw net
payoff at F_i. A clean legal comparator can remain quiet and obtain at least
F_i. This is the direct continuation comparison required by the action-
restriction extension. It needs no lower bound on the probability of exposure.

## 9. What is proved, and the exact communication boundary

For the finite target specified here, availability follows from actual public
logging or a nonauthor strategic report. There is no honest monitor premise.
The body-key validator proves validity persistence; the explicitly assumed
chain service turns it into bounded publication; the reporting game supplies
the remaining received nontransaction evidence. The source timing/reset and
semantic-shadow arguments can therefore use these concrete local interfaces.

The target still has substantive runtime assumptions: a closed authenticated
message algebra; one broadcast/submission primitive; funded body-key recording
whose inclusion law is fresh and isolated; sufficient finite capacity;
packet-local exposure; and a funded report stage. These are not consequences
of source-language compilation alone.

In particular, a different API may let a player show the same chain-valid
signed bytes to peers without submitting them to the chain service. Then
seeing those bytes proves neither a job nor (2). A retained-prefix body could
be absent at audit, and a failed owner's announced value could remain private
past the next binding barrier. Terminal report-all does not make it public
earlier. Nor may an omitted transaction wrapper simply be blamed on the
original signer: another party might have stripped it.

That larger announce-only model is not refuted here. A correct announced
opening which never completes caps its own author's payoff by exclusion; an
announced opening which completes reveals the same value publicly. These facts
are useful normalization cases. They do not by themselves supply a legal
comparison under every extending opponents' policy: early unsubmitted signals
can reach information sets excluded by the retained publication bound and
change a foreign-failure continuation. Either include those announcements in
the retained timing/information game and prove its comparisons, or give them
an independently authenticated protocol format with a positive offense.
Simply renaming an observed envelope a submission does neither.
