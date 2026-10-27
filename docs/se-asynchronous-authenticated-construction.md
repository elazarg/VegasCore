# An authenticated asynchronous audit construction

This construction separates the retained runtime from its raw communication
extension. The retained runtime uses proper semantic choices before the first
public exit and the full audited raw handler afterward. The
[pre-exit construction](se-asynchronous-pre-exit-construction.md) builds its
equilibrium from the selected intended-game SE, with the handler bound specified
below. This document supplies the authenticated extension and reporting
composition. It does not assume public sender turns, a full mempool flush, or an
auditor who knows the complete traffic history.

The claim is about the explicit channel and cryptographic idealization below.
It is not a theorem for every Internet side channel or every raw EVM transaction.
The source and service interfaces remain those of the
[finite asynchronous service](se-asynchronous-fixed-window-construction.md).

## The finite authenticated message domain

Fix a session, finitely many players and physical attempts/slots, a finite message
alphabet, and a finite transmission-opportunity process. Every player-originated
session transmission has an authenticated author and a complete bounded body.
An invalid inner call is still inside that authentic outer session envelope;
an unverified claimed sender name is never evidence against that player.
There is one broadcast primitive into a partially observed network. Players
choose contents and transmission time; chance determines the observer subset.
There is no sender-selected confidential subchannel. Receipt events need not
be public.

Use ideal authentic signatures and ideal opaque commitment handles. Each owner
has a finite sufficiently large pool of fresh names. An unused name has no
pre-existing publicly verifiable relation to a semantic value. Its private heap
assigns it one typed value, immutably. An unusable raw preparation has no valid
opening capability. Opening certificates are publicly verifiable. Signatures
and certificate representations are canonical; arbitrary extra bytes are not
a free second message field. The body is canonical once its handles and values
are fixed.

At every retained index, allocate distinct fresh labels with a fixed full-support
law independent of semantic values. The fresh-label set is determined by
operational metadata, not private source values. Service, routing and legal
controller transitions are invariant under consistent fresh-label renaming.
Construct the auxiliary timing game on the label-erased state and lift its
policy to ignore names; semantic strategies also ignore names. Thus a different
fresh name has no verifiable semantic meaning, and its likelihood contributes
only an operational factor. Label-blind service alone would not justify this
if the prescribed other players reacted to names. A canonical name per physical
slot is a simpler special case, but is not required.

These are substantive idealizations. An ordinary sender-selected hash commitment
does not enforce malicious-sender opacity: a sender may choose a publicly known
salt. Signatures alone also do not provide a sending timestamp. A cryptographic
implementation must justify the appropriate computational replacement; it is
not supplied by this finite exact argument.

For the simple reporting construction, use a typed, nonnested message algebra:
source values, commitment/opening certificates and authenticated application
entries are distinct sorts, and an entry has no field containing another
authenticated application entry or an arbitrary encoding of one. Raw messages
may have invalid field combinations and certificates; they are not arbitrary
authenticated byte strings with hidden extra signed payloads. This is an explicit
ideal-domain limitation. Otherwise reporting a foreign malformed body could
reveal the reporter's own incriminating signature nested inside it, and the
zero-cost reporting proof below would need a different producer. A zero-knowledge
proof of the positive violation, exposing no unrelated witness contents, is one
possible stronger backend; its soundness and privacy would be additional premises.

The canonical signed application body names:

* the session, author, physical attempt, owned transaction window and component
  event identifiers;
* either a commitment handle or a typed opening and its certificate;
* an actual public readiness/phase certificate;
* for an opening, the public accepted-binding certificate for that exact
  physical resolve slot, or its initial-binding certificate together with the
  actual resolve readiness certificate.

Transmission batching preserves component identities. A binding packet lists
one opaque handle per owned component of the current private-choice block, with
distinct handles. An opening packet contains only the components designated by
the current source reveal block; it never releases the whole committed vector
early. The accepted-binding reference for a component is the vector packet's
record together with its component index and handle. Omitting a required
component, duplicating an index, or exposing a future reveal component is a
format/authorization defect. Two components assigned the same handle can be
witnessed within one signed packet.

The public controller issues a readiness certificate only after that phase is
actually installed. A predictable future phase label is not a certificate.
An authentic certificate is a capability created at that installation, not a
string a player can pre-sign or guess and have become valid later. Players can
transmit held authentic capabilities or invalid strings; the latter never
subsequently become authentic certificates. This makes an intrinsic defect
persistent rather than dependent on the verifier's current clock.
Opening authorization binds the accepted physical binding and handle, not just
the source variable's name. An abandoned commitment attempt cannot authorize a
resolve phase that was never installed.
The obligation record also identifies its immutable guard-input references.
Some required own commitment values may be published later than the subject;
the controller checks the guard once the last required input is public, using
those references rather than a later post-rollback context.

Initial commitment certification proves the initial binding only. It never
authorizes an initial secret's disclosure before its actual resolve phase.

The identity of an application entry is its canonical signed body. Physical
retransmission of that same entry is a separate transport occurrence. It does
not create a second authored application entry. An outer transaction, including
its fee fields and account nonce, is a carrier; it is not the application entry's
identity. A sender cannot make a genuine conflicting pair disappear by replacing
one carrier transaction.

## Public controller and retained transmissions

The controller keeps public accepted-entry/nullifier records. Each physical
owned transaction slot accepts at most one canonical entry; indexed components
identify the separate source bindings inside it. It issues an opening certificate
only for the accepted binding. A public phase closes only after each relevant
owned slot has completed or its owner has been permanently excluded.

Before the first public exit, the retained menu contains silence, private planning, semantically admitted
current-phase bindings and exact retransmissions of its entries. It contains one
first authored entry per physical slot and prohibits reuse of a commitment
handle across distinct bindings. A retained binding has an admitted typed value
in its private heap. Retained publication exposes that value with the genuine
resolve authorization. All local memory needed by a randomized controller is
retained; it need not be encoded in a public packet.

After the first public exit, the retained menu is the entire raw handler menu,
with the actual audit settlement. The restriction is therefore the identity on
handler choices. No post-exit source guard satisfiability or admitted-value
selector is assumed. Handler policies are completed jointly on their actual
information, as in the pre-exit construction.

Choose F_i at most every nonexcluded raw **base** terminal utility of player i,
including any default terminal value. These are finitely many fixed quantities,
so such a floor exists. This changes the failure settlement, not the intended
game's utilities. Audit forfeitures are not redistributed as positive game-player
rewards, and reporting has zero net player cost. An audit-clean quiet
continuation consequently guarantees at least F_i even in a raw handler.
Arbitrary audited handler continuations may pay less than F_i; no lower bound
on their net utilities is assumed.

A raw binding may instead have no usable value or have a value its source guard
rejects. Its opaque public handle does not reveal this defect. Such a binding is
not automatically an auditable offense at commitment time. The private repair
argument below handles it without adding it to the semantically proper core.

Exact retransmissions are deliberately retained. A signature on an old body does
not prove who later copied it, and one body cannot supply indefinitely many new
offense witnesses. The retained runtime's timing proof must cover the physical
effects allowed for these transmissions. Application-level idempotence alone is
not that proof.

### Irrevocable publication of the retained prefix

Require an individual service promise for every qualifying authenticated body
broadcast into the session network. The primary service uses one joint
broadcast-to-recording kernel with bound Delta, the delayed-delivery support
specified by the proper-core construction, and independent per-body randomness.
Intermediate chance-selected observations and final recording belong to that
same kernel. An evidence-retaining ingress receives the complete body no later
than its recording. Every distinct bounded qualifying application body is
recorded, including conflicting and stale inner calls. Later player actions
cannot revoke that promise. The promise prescribes neither sender turns nor
an emptying of unrelated queues.

One implementation interface uses a sponsor-funded inbox and an honest relay
which submits with its own account nonce. The game player cannot cancel that
relay transaction by replacing its own transaction. Admission must mean actual
acceptance of this irreversible obligation; an ordinary private-RPC acknowledgment
is not enough. The channel's retained-send action must provide this qualifying
admission, perhaps after a bounded routing delay while earlier private copies
are already possible. Separate bounds Delta_route and Delta_chain would imply
the publication bound Delta_route+Delta_chain, but not the normal-explanation
support used by the proper-core theorem. Such a two-leg implementation needs
its own proof of that support and the relevant coupling. The primary hand
construction uses the single joint kernel specified above.

The relay deduplicates identical canonical bodies, not all bodies for a physical
slot. Two conflicting bodies receive separate publication jobs; the one emitted
later may reach the relay or chain earlier. The game controller may execute
only the first accepted proper body, but the outer inbox still records the
other. No hidden global emission-order registry is required. Retransmission of
one canonical body cannot revoke its publication job or reset its deadline.
This is an explicit asynchronous service interface, not an inference from
ordinary sender-nonce replacement behavior.

The key quantifier is preservation under arbitrary subsequent raw behavior:
every entry in a retained prefix remains due for publication after the first
departure. A guarantee that disappears when its sender changes policy would not
support the following witness argument.

Funding must cover the declared raw domain. If at most M distinct bounded
entries can be admitted and each relay transaction costs at most c_send, reserve
M*c_send rather than a budget based only on intended-path traffic. A fresh
proper entry's eligibility cannot disappear because an earlier unobserved bad
flight consumed a hidden shared allowance. Either the whole declared allowance
is funded or the simulator must account for that shared state. Funding removes
this affordability failure; it does not itself prove the inclusion promise.

## Positive witnesses without a complete traffic list

The verifier accepts only positive, finite evidence. It does not judge an entry
by the absence of another privately sent entry.

| Extra entry at a retained prefix | Collectible witness |
| --- | --- |
| Malformed, wrong-owner, wrong-type, reserved-handle or invalidly certified signed body | The authenticated body and fixed public verification data |
| Opening without an actual installed resolve certificate or using a different accepted handle | The body and public phase/binding records |
| A distinct second body for a physical slot | The two authenticated bodies with the same slot |
| Reuse of a handle for a distinct binding/component | Two authenticated binding records, or two indexed components of one signed packet |
| A new historical body from an active owner whose old slot completed | The body and the earlier public accepted entry |
| An exact retransmission of an existing body | No new offense merely from identical content; it is retained transport behavior |
| A first old body from a permanently excluded owner | Use the excluded-owner payoff comparison or a separately proved late-record rule |

For old slots, the controller invariant matters. If the owner is still active
when an owned slot has completed, successful completion supplies the accepted
entry. If there was no successful accepted entry, that owner's slot must have
completed by exclusion. Merely saying that a phase has ended would not prove
this classification.

For a conflicting current binding, the earlier packet need not already be
public when the second packet is received. It belongs to the retained prefix,
so its irrevocable individual publication promise makes it public by audit time.
A recipient can retain the conflicting body and combine it with that earlier
emission's eventual record. The witness is an unordered pair of distinct bodies
for the same slot; it does not claim which was emitted or included first.
Thus public acceptance can give an immediately available counterpart, but
eventual publication of the retained earlier emission also suffices.

This distinction repairs a real otherwise-missing case. Two distinct commitment
bodies can be sent privately before either appears on chain. A recipient holding
only the second body cannot prove that the first exists. A sender-chosen serial
or hash-chain does not provide the missing first body. If the earlier retained
entry can be cancelled and disappear, the proposed pair-witness guarantee fails.

In the finite-fresh-label grammar, another fresh name is a retained alias choice
for the first entry, but a second distinct body for that same physical slot
needs the pair comparison. Exact copies are retransmissions, and a second
different value cannot replace an immutable private binding. Merely declaring
handles opaque would not justify names that encode verifiable semantic
information; the alias-law and label-erased-policy conditions above are used.

The certificate design also removes a negative-information test from the
verifier. It checks the publicly accepted binding named by the actual resolve
certificate. It does not ask whether an unobserved later eligible binding exists
somewhere in a global signed-message list.

### Relation to the existing audit interface

The current `Vegas.EventGraphRuntime.PhaseCount.Evidence` in
[PhaseCountMenu](../Vegas/Pending/PhaseCountMenu.lean) is a pair containing the
full traffic list and an accused packet. Its coverage premise in
[PhaseCountCollection](../Vegas/Pending/PhaseCountCollection.lean) concerns
observation of that entire evidence object. The positive witness grammar above
is therefore a new backend adapter, not an existing consequence of receiving a
single pending envelope.

The existing first-departure and permanent-floor extension principles remain
applicable once their actual comparison premises are established. The concrete
verifier must have its own soundness and witness-completeness argument; it cannot
inherit them by renaming the full-traffic evidence type.

## Repairing a semantically invalid opaque binding

Before the first public exit, the owner can determine the admitted values from
its source observation and the intended-history invariant gives nonemptiness.
Fix a deterministic admitted-value selector on that observation. After public
exit, the retained handler permits every raw binding, so new handler bindings
are copied literally rather than repaired. A pre-exit hidden repair either
reaches irreversible save, where the comparison stops, or is erased by the
first commitment rollback. This avoids assuming source well-formedness at
arbitrary post-failure contexts.
For a raw unusable or guard-rejected candidate w, the comparator places an
admitted value u behind the **same opaque public handle**, and remembers w in
its private virtual memory. This changes the counterfactual private heap, not
an already accepted commitment in one execution. Each individual execution
still has immutable handles.

Preparation may precede the public information needed to select u. The
comparator therefore uses **lazy allocation**: it simulates the raw preparation
and reserves its private handle name in scratch memory, but does not yet assign
that name an actual comparator binding. At the handle's first proper public use,
it selects u from its then-current legal source observation and allocates the
still-unused handle once. This is possible only because private planning has no
external or service effect, carries no authenticated preparation timestamp, and
the same unused opaque name can be allocated later. A prior public use is instead
a reuse case and cannot be repaired by changing its value. Without these rules,
choosing u using future guard information would be an illegal clairvoyant
preparation. Ordinary hash commitments do not automatically have this lazy
same-name property.

For a block with several own bindings, choose the admitted vector in source
order, using the repaired prefix for each later admission test. Keep equal
values whenever the raw value is still admitted. The first changed coordinate
is therefore the earliest actual semantic defect; previous own values agree.
The selector depends only on the comparator's legal own source observation.
Remembering the raw vector for future virtual decisions does not authorize
the comparator to read a foreign hidden state.

Before commitment-block settlement, public messages, public controller state and
all other players' observations agree. Foreign guards cannot read another
player's hidden bindings. A genuine resolve authorization is issued only after
that commitment block has been saved. An earlier changed-value disclosure is
therefore an unauthorized opening, handled by the ordinary positive witness.

**Saved-debt lemma.** If a commitment block containing a changed binding is
irreversibly saved, the raw owner's eventual base payoff is F_i under every
later raw continuation. To prove this, take the earliest changed binding in
source introduction order in the live saved prefix. All commitments read by
its guard were introduced earlier. Their raw and repaired values agree:
otherwise an earlier live binding would have been changed. Public data and
previous publications in that guard were already fixed when it was introduced.
Thus either this earliest candidate has no usable opening, or its guard predicts
rejection on the actual raw earlier inputs.

Saved-prefix persistence is essential. Rollback erases only an unsaved current
commitment block, together with its dependents, before any genuine resolve for
that block. It cannot erase an earlier saved binding or its guard dependencies.
Hence choosing the earliest **live saved** change does not accidentally use a
discarded attempt as a guard input.

Now suppose the raw owner remains active until terminal settlement. Every own
commitment required by this saved obligation must then have a truthful typed
publication; missing, unusable or invalid publication would exclude that owner
by its finite deadline. Once the subject and the last required own input have
been published, the guard verdict equals its original prediction. The exact
identity is `Vegas.SourceProgram.Obligation.accepts_eq_predicts` in
[GuardPrediction](../Vegas/Source/GuardPrediction.lean). Its revealed-input and
truthful-own-publication hypotheses hold at that completion point. The guard
therefore rejects, which also excludes the owner. This contradiction proves
eventual exclusion. Nonnegative audit charges can only reduce the resulting F_i.

A guard may be checked at the **last** publication of its inputs. Its subject
can open earlier, even before another player's source choice. Nothing in this
argument reorders those publications or asserts that the first changed opening
already has a publicly false guard. The comparison stops earlier, at irreversible
save, using inevitable own exclusion rather than an immediate audit witness.

The controller rules used here are explicit: every live saved obligation and
its dependencies persist through foreign exit; each required publication has a
finite deadline; missing publication and a rejected completed guard exclude its
owner; terminal settlement cannot leave an active owner's obligation unchecked.
These are rules of the proposed controller. Existing saved-debt results supply
an analogous statement for the reserved service, not an automatic adapter for
every new scheduler.

The private repair therefore has two outcomes before any genuine changed
opening. If the block is saved, stop: raw net payoff is at most F_i, while a
clean quiet retained continuation gives at least F_i. If foreign commitment
failure rolls the block back first, both public applications erase the whole
current block. Their live semantic states agree again. The old raw values remain
only in the simulator's private memory, and the abandoned attempt never obtains
a resolve authorization.

### Entering the full raw handler

After such a foreign exit and rollback, the retained handler has the same raw
menu as the target. New handler bindings can be copied literally, without any
admitted-value selector. Old private handles from the erased block need not be
forgotten; exposing a changed old opening would require a nonexistent resolve
authorization and is handled by the exposure comparison. No live invalid
saved binding needs to be carried into the handler: the comparison would
already have stopped at its irreversible save.

The comparator need not copy an audit-bad handler transmission merely because
the handler menu permits it. It can suppress that transmission until exposure,
keep its own reserve clean and use the positive-witness comparison. At exposure
it remains quiet; the global base floor gives net utility at least F_i.
If a newly copied raw handler binding is itself unusable or guard-invalid,
apply the saved-debt stop to its irreversible save as well. Here both heaps
already contain the same raw value; no admitted selector is needed. The earliest
actual invalid binding supplies the same prediction-and-persistence proof of
own exclusion. Thus no guard-invalid opening needs an immediate audit witness,
and the comparator's reserve remains clean before every exposure comparison.

## Proper-core and audited-handler composition

The proper-core construction fixes the intended source strategy before first
public exit, chooses its operational timing strategy, and completes all raw
handler information agents jointly with positive action floors. The handler
payoff is the actual reduced report-all audit settlement, not an unaudited
placeholder game.

At a first-exiter information set reached from a clean pre-exit history, every
continuation has net payoff at most F_i. The pure quiet continuation has payoff
exactly F_i: permanent exclusion fixes base utility, previous own entries are
audit clean, no new own entry is sent, and another player cannot forge an
authentic new offense by i. This statement uses the persistent positive verifier,
not a time-dependent reclassification of earlier legal messages.

Let delta_n bound every local pure-action regret of the constrained handler
profile, and let H bound the number of remaining decisions. Finite
one-deviation telescoping gives a whole-policy gain bound H*delta_n. Perfect
recall and Bayes own-policy cancellation justify using the same conditional
beliefs at future information sets reached by the quiet deviation. Therefore
the handler value for a clean first exiter lies in

    [F_i-H*delta_n, F_i].

The action-floor payoff-range estimate gives delta_n tending to zero. This
adds a vanishing H*delta_n term to the pre-exit comparison. It does not require
the handler's perturbed value to equal F_i exactly. Completing handlers and
choosing the pre-exit perturbations in one finite game then gives the retained
SE described by the pre-exit construction.

Next apply the authenticated raw comparison below. Its only extra-action
obligations are at pre-exit retained sites: after exit the retained and target
menus already agree. Finally lift the reduced report-all equilibrium through
the strategic reporting stage. These are three different steps on specified
finite games; the construction does not assume an unexplained raw-runtime SE.

## Causal partial observation of broadcast

The broadcast network delivers complete authenticated envelopes to a
chance-selected subset of observers. Before delivery, neither a
packet's contents nor its mere presence affects another player's observations,
another packet's delivery, or execution service state. Delivery schedules may be
private and asynchronous. They may depend on public routing metadata, but not on
an unseen semantic payload in a way observable elsewhere.

A concrete sufficient kernel assigns each in-flight envelope fresh delivery
randomness independent of the source draw, other service randomness and other
in-flight envelopes, conditional on its public routing metadata. Empty receipt
opportunities reveal no global queue information.
Removing an undelivered extra envelope therefore preserves every other actor's
observation and transition until that envelope reaches an external recipient.
The sender can simulate its own private flight bookkeeping with independent
local randomness. A more general correlated flight law needs its own causal
simulation proof; source-independent initial randomness alone is insufficient.

Every execution ingress that can let a packet affect inclusion, public state or
other packets is also an evidence-retaining recipient. A receipt there supplies
the same complete authenticated body. An unseen packet cannot slow the public
service first and become observable only if somebody later decides to inspect it.
An implementation with such congestion effects needs a different comparison.

The arbitrary existing pending-ID selector is broader than this channel. It can
choose whether to reveal innocent marker X or Y as a function of an unseen bad
packet's payload. The observer then learns that payload's bit without obtaining
the offending signature. Receiving complete selected packets does not prevent
this indirect leak. The channel restriction above rules it out at the kernel
level; it must not be inferred merely from the format of a received packet.

## Terminal report-all supplies collection after exposure

Freeze the base game at a public terminal point. Let K_j be the bounded set of
complete entries actually held by each player or evidence-retaining ingress.
Public prefix entries remain available from the ledger. Each participant can
send a canonical bundle of all known foreign-authored entries. Reports are
sponsored and have zero net cost and zero positive reward for game players.

Use the following finite report service:

1. Knowledge for the reporting decision is frozen; report bundles cannot create
   new game actions or change the base payoff.
2. Every participant that still has a report choice has a reporting opportunity
   before a fixed submission cutoff, independently of another player's choice.
3. Every properly funded admissible report submitted by that cutoff is finalized
   by the audit cutoff, for every bounded reporting profile. Already submitted
   reports retain this guarantee.
4. The penalty against i uses only i-authored entries and fixed public records.
   A report from i contains no i-authored entry, including nested entries.

At any reached reporting prefix, each other player's already chosen bundle is
fixed, and each remaining report-all bundle is fixed by frozen knowledge. All
these bundles arrive by the cutoff. Player i's reporting action cannot change
the terminal i-authored evidence set. Report-all is therefore sequentially
optimal for i under every belief. No independence of inclusion times is needed:
the guarantee is equality of the final relevant set.

This is the concrete final-set producer for the separate-evidence-stream
condition in the [reporting analysis](se-asynchronous-audit-feasibility.md).
Positive per-entry perturbations of report-all have a uniform finite-horizon
error bound. Taking them with the pre-report consistency sequence gives an SE
of the strategic-reporting game from an SE of the reduced report-all game.
It does not make withholding an impossible raw strategy.

More precisely, let H_R bound the number of remaining reporting coins and let
B_R bound net-utility differences, including audit collateral. If each future
coin departs from report-all with probability at most rho_n, the conditional
probability of any future reporting perturbation is at most H_R*rho_n from
every reached history. The induced continuation-value error is at most
B_R*H_R*rho_n, and a two-action gain error is at most twice that bound. Earlier
reporting errors do not require division by the current site's reach mass.
Future reports leave every pre-report reach probability and Bayes belief
unchanged exactly, so no hierarchy relative to a rare pre-report information
mass is needed. Choose rho_n tending to zero and take one common subsequence
of the full finite Bayesian assessments.

If there are r registered reporters, at most M canonical entries, and a bound
c_bundle(M) on the total cost of each proper report bundle, a segregated reserve
of at least r*c_bundle(M) funds the chosen report policy. Eligibility is not a
first-reporter race, and another report cannot consume a participant's allowance.
An independently established gas/fee bound and the stated liveness contract are
both required. These accounting bounds introduce no public reporting order.

If a nonculprit receives a new bad body, report-all delivers that body. Its
retained-prefix counterpart, when required, is public by audit time. The verifier
therefore collects the charge with probability one in the reduced game.
Separate recipients can supply separate parts of a witness. No recipient needs
to possess the entire traffic history or know at receipt time that a violation
has occurred.

## The first-exposure comparison

Let R be the retained finite runtime and G its authenticated raw-message
extension, with the retained SE constructed as above. Let U_i bound G's base
payoff and use the global base floor F_i fixed above. At an exposure stopping
point the comparator switches to its clean quiet continuation, which gives at
least F_i. No global lower bound on audited handler payoffs is substituted for
that comparator. The reserve is refundable on every audit-clean execution;
raw handler offenses can still be charged.

Fix a retained information set of an active player i and an arbitrary unilateral
raw continuation. Simulate it with a retained controller as follows. Repair
semantic candidates as above and preserve their raw values in virtual private
memory. Emit the identical opaque binding entries, other retained proper entries
and retained retransmissions. Suppress an externally forbidden entry
from the physical channel while remembering its virtual flight. All other
players' states and observations remain coupled until such an entry reaches
an external recipient or the saved-debt/own-exclusion stopping condition occurs.

This simulation uses the retained private-memory and preparation interface
specified above. It is a causal randomized policy based on the player's own
observations and private randomness, not a different policy selected using a
hidden source state. Its independent virtual flight seeds can be incorporated
in a mixed strategy and realized behaviorally by perfect recall.
The comparator samples these seeds itself. It may switch to quiet when its
virtual flight is scheduled to expose a suppressed packet, even though the
real sender need not observe that receipt. In the coupling, the same seed
drives the raw packet's flight; the raw strategy is not given that seed.
Its marginal observation/strategy law is unchanged. This construction uses
no access to actual hidden network state by the comparator.

Maintain a virtual retained prefix P. Before exposure, the two public controller
states and all nondeviators' observations agree. A new audit-clean entry whose
wire body is compatible with the paired heaps is emitted in both executions;
it extends P and acquires the same irrevocable
publication promise. A forbidden entry is suppressed in the comparator, and
the witness table gives an intrinsic proof or a conflict with an earlier entry
of P. A semantically changed binding instead reaches the saved-debt stopping
condition before any genuine changed opening. Raw preparation
is preserved in the virtual table, so suppressing a transmission does not require
forgetting its value or later choosing it using hidden information. The physical
comparator heap contains admitted bindings; an opaque local preparation by itself
is not an auditable offense. After public exit, membership in the full raw
handler menu is not the emission test: audit-bad handler entries are still
suppressed, and any newly copied semantic defect still triggers the bad-save
stopping condition.

No suppressed packet can alter the common public state or another player's
information before its first external reception. Thus this invariant continues
through silent flight steps and through the identical processing of matching
entries. When a suppressed packet first arrives at an execution ingress, that
ingress already holds its full body; its effect cannot precede the exposure
event. Every earlier conflicting entry in P remains due for public recording.
This is the induction needed for the comparison; a compiler whose preparation
or channel transitions violate one of these clauses does not instantiate it.

Stop the comparison also if the focal player is permanently excluded, or a
semantically changed commitment block is irreversibly saved, before such
exposure. In either case its eventual raw base payoff is F_i and its net payoff
is at most F_i. A clean quiet retained continuation gives at least F_i. These
branches contribute a nonpositive gain without an audit witness.

Let E be external exposure of a suppressed forbidden entry before either
payoff-cap stopping boundary. If none of these stops occurs, every changed
binding block must have been rolled back rather than saved, so the terminal
initialized game and utility laws agree. On E the raw player's base gain over the retained
comparator is at most U_i-F_i, and the terminal report-all audit collects at
least one previously clean charge. Hence

    E[raw net utility - retained utility]
      <= (U_i-F_i-D_i) Pr(E).

A reserve D_i>=U_i-F_i makes this nonpositive. There is no required positive
lower bound on Pr(E). The same comparison holds for every belief at the retained
information set, provided the simulation and exposure/witness invariant hold
from every underlying retained history under the same legal controller.

This is stronger than assuming that every attempted packet gets observed. It
instead compares gain and collection on the same event. It is weaker than
claiming safety for arbitrary congestion or indirect-observation channels: those
can invalidate equality on E's complement.

For a permanently excluded actor with fixed base payoff F_i and no incoming
rewards, arbitrary nonnegative audit penalties give raw net payoff at most F_i.
A clean retained continuation gives F_i. The direct extension comparison applies
without a new charge for every old disclosure. Residual communication reserves
can strengthen this to strict deterrence for new provable offenses, subject to
the incremental conditions in the [post-exit analysis](se-post-exit-deterrence.md).

The restriction-extension construction then preserves the retained SE in the
reduced report-all game. Lifting through the reporting stage supplies common
consistent beliefs and rational reporting in the actual finite game. On the
retained equilibrium path there are no charges, so the initialized base-outcome
and realized net-settlement laws are unchanged.

## Exact construction boundary

The positive route needs all of the following facts, each at its stated scope:

* ideal authenticity and opaque immutable commitments;
* actual public phase and accepted-binding certificates;
* irreversible publication of retained-prefix entries under arbitrary later
  raw deviations;
* a positive witness for every externally effective suppressed entry;
* a causal private-shadow simulation until such exposure;
* complete-envelope reception without effects from unseen packets elsewhere;
* frozen, sponsored reporting with the final-set delivery guarantee;
* funded collateral, a clean retained comparator and matched realized settlement.

The receipt/prefix witness classification, virtual-prefix induction and report-all
final-set argument are explicit above for this ideal message game. Instantiating
them for a particular compiler requires its exact private-preparation menu,
phase controller and transport transitions to satisfy the stated equations;
citing a generic extension theorem does not supply that correspondence.

In particular, allowing a player to send a perfectly valid inner message only
to a chosen private peer, bypassing the qualifying broadcast primitive, is a
different action model. The signed content does not prove whether a qualifying
broadcast happened. One must either include that routing choice in the retained
runtime's analysis or prove a different attributable violation. Likewise,
unauthenticated disclosures, informative partial hints, payload-dependent
selectors and unobserved congestion are not silently covered by this theorem.

For this specified finite controller, ideal authenticated-message algebra and
joint broadcast service, the stopped comparator and reporting lift give the
complete mathematical raw-action extension. Together with the proper-core
construction they yield the [finite preservation theorem](se-asynchronous-preservation-theorem.md).
This is a hand theorem for the constructed model. No correspondence to the
current Lean implementation, ordinary hash commitments, arbitrary byte-message
traffic or an unchanged blockchain network is asserted.
