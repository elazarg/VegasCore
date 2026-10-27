# Asynchronous publication, authorization and private reception

This note separates the publication argument from the information argument for
an asynchronous ledger. Owners can transmit after public prerequisites are
satisfied; they do not know other owners' local opportunities or transmission
times. Private reception remains private. The ledger supplies the public
history. There is no public callback calendar and no requirement to clear the
entire queue in one block.

The results below are finite mathematical derivations. They are not new Lean
theorems. The existing native counted-action ingredients are in
[the native adapter](se-publication-native-adapter.md); the generic probability
argument is in [the causal transfer theorem](se-publication-transfer-mathematics.md).
This document identifies which parts survive asynchronous scheduling and which
require an additional refined-reference incentive argument.

## A precise finite asynchronous model

Fix a finite horizon and finite supported initial law. An execution is a finite
interleaving of the following events:

* a public finalized-ledger update, possibly recording only part of the queue;
* a local opportunity for one owner to observe, wait, or transmit;
* a private reception event, represented as a local observation opportunity
  with a silent response when no transmission is selected;
* a public source chance step or contract clock/timeout step.

The interleaving need not be public. A player recalls its own opportunities,
observations, actual ledger history and actions. The future service schedule is
not revealed. The underlying fixed service law and the bounded action menus do
not change along a consistency sequence. Waiting is legal, so a transmission
time can be chosen strategically among the owner's available opportunities.

Every protocol entry has an immutable identity, authenticated principal and
canonical body. The body fixes the physical event, handle, opening value when
present, and authorization evidence. A distinct transport occurrence can
carry an already registered entry. An occurrence is not automatically a second
signature by the original principal. Keep these identities separate when
specifying replay and audit rules.

The ledger retains rejected as well as accepted entries. Its public history
contains the actual recorded entries and public contract transitions, not an
assumed list of all privately sent packets. A participant may possess a signed
body before transmission; that private construction does not itself create a
network entry or public event.

For the publication theorem, use this explicit inclusion contract for the
retained counted class of first entries:

> If a qualifying first entry is admitted at time a, then it is recorded in
> the finalized ledger by time a+Delta, even if its inner game action has
> expired or become obsolete before recording.

The qualification predicate must be stated independently of the subsequent
semantic success of the call. A funded, correctly formed inbox transaction can
qualify while the enclosed opening later fails its game deadline. A guarantee
only for calls that are still semantically applicable is insufficient below.
No claim is made that an ordinary fee-dependent public mempool supplies this
contract for every visible byte string.

This is an individual-entry deadline. Inclusion can be staggered, reordered or
split across blocks. The proof needs neither FIFO inclusion nor one full batch.
If an implementation offers only an aggregate throughput guarantee, it must
derive this deadline from its queue and arrival bounds; a block-time bound
alone is not an entry-inclusion bound.

Admission time, the deadline Delta and finalized-ledger time use the same
monotone time coordinate. The bound concerns finalized recording, not merely
tentative block inclusion. If an implementation measures delivery in wall time
but enables phases from a ledger timestamp or height, it must establish the
corresponding conversion; an unchecked timestamp jump cannot count as elapsed
publication time.

## A public publication delay

Let a reveal phase close at public finalized time c. The compiler stores that
closure and withholds the next semantic binding phase until a finalized ledger
watermark at least c+Delta has been reached. At the boundary, enabling happens
after the watermark's promised entries have actually been recorded. Equivalently,
use a strictly later public time if the time convention does not order inclusion
and enabling at equality.

The delay is contract state, not a requirement that a participant request a
callback at a prescribed time. During the delay there is no new owned binding
request. The next owned event's deadline starts at its eventual readiness,
after the delay. The source program's commitment blocks and source choices are
unchanged. A compiler can represent the delay by a public cooldown phase; a
source-padding implementation is another option if its scheduler proves the
same public-time separation.

### Publication lemma

Consider a retained counted history reaching the next binding callback. Let
q be any opening first admitted during the preceding reveal phase, at time a.
Because it was a current-phase entry, a<=c. It qualifies for the stated
inclusion contract. Therefore

\[
              \operatorname{recordedAt}(q)
                   \le a+\Delta\le c+\Delta.
\]

The binding phase is enabled only after that recording watermark. Hence q is
already in the actual public ledger before the callback. This argument is
pointwise in the history: it does not use a probability, a typical schedule,
an expected delay or a participant's knowledge of foreign send times.

Every retained current-phase opening from an earlier reveal block satisfies
the same argument at its own boundary. There is no opening first emitted from
a future reveal block. Commitment retries add no new opening. Thus at every
retained binding callback,

\[
  \{\text{typed proposals in submitted first opening entries}\}
   =\{\text{typed proposals in ledgered opening entries}\}.
\]

The forward inclusion is the delay lemma; the reverse inclusion is ordinary
entry provenance. Repeated transport occurrences of one entry do not change
these sets. Ledger publication may reveal an opening that the game handler
rejected: semantic acceptance is not a premise.

### Exact boundaries

Three shortcuts would invalidate the proof.

1. A high-probability or eventual inclusion guarantee cannot replace the
   deterministic bound when asserting pointwise archive equality.
2. If a transaction loses its inclusion guarantee when its game event expires,
   an opening sent just before c can remain private after c+Delta. The inner
   call's rejection must not cancel the outer publication obligation.
3. A participant can retain an old authorization and make a new first admission
   after c. The inequality a<=c then fails. Such actions are handled by the
   raw extension, not by pretending the public delay publishes unsent data.

The last case is compatible with preservation. Genuine unused old owned-event
allowances belong to an excluded owner once that event has finished; an active
owner's completed event already has its first packet. The exact classification
and attempt/accepted-handle authorization are in
[the authorization analysis](se-publication-authorization.md). At a copied
excluded-owner site, every raw continuation has base utility F_i and
nonnegative penalties give net utility at most F_i. The clean source
continuation pays F_i. The localized restriction extension can therefore
complete survivors' new information sites after a late private disclosure
without requiring the archive identity there.

## Public authorization is ledger information

An authorization certifies an actual public ledger state in which the named
physical phase was installed, the owner's event was ready and the owner was
unexcluded. An opening authorization also fixes the accepted binding handle.
It remains valid historical evidence after the phase ends. A guessed future
phase identifier or an attempt-free readiness token is not equivalent evidence.

In the asynchronous model, take the actual public ledger history as part of
the information model on both the reference and implementation sides. The
canonical authorization is a function of that public history. There is no need
to reconstruct it from hidden foreign callback times or from differences between
periodic local snapshots. In particular, the proof does not rely on the
deterministic-calendar reconstruction used in a different service instance.

This is an explicit choice of observed public data. If an existing reference
theorem was proved with a smaller public observation, its incentive bounds
must be proved at the refined information sets. Adding public history is not
justified by marginal outcome equality. The kernel and continuation arguments
below allow that refinement, but do not manufacture its sequential-rationality
premise.

Certificate serialization is canonical. Its bytes and availability are fixed
by the recorded public state, rather than a sender-selected proof variant or
random memo. The actual reception kernel may inspect those bytes. A reference
that knows the public ledger history and the pending core entries can construct
the corresponding enriched pending entries before applying that kernel.

The public state machine itself need not contain hidden commitment values.
Binding changes the public accepted handle and completion status independently
of private candidate decoding. A valid opening exposes the certified value;
the source guards read public cells and already published commitment inputs.
Samples, clocks, exclusions and public rollback checkpoints are then replayable
from actual public events. The private typed source state remains proof state.

## Local pending reconstruction does not need a global calendar

First consider transport with one occurrence per newly submitted entry and
private learning only at the modeled local opportunities. Complete reception
means that at each such opportunity the reference player learns all currently
pending foreign entries. The player does not learn when other callbacks occurred.

Enumerate one player's own opportunities by k. Let P_k be the ordered pending
list just before its kth complete draw, L_k its current public ledger, R_k its
accumulated complete learned list after the draw, and E_k its own emitted entry
at the following response, as an empty or singleton list. Let D_k be the new
suffix of R_k relative to R_(k−1). Then

\[
 P_0=D_0,\qquad
 P_k=\operatorname{filter}_{\mathrm{id}\notin L_k}
        (P_{k-1}\mathbin{+\!+}E_{k-1})
       \mathbin{+\!+}D_k.
\]

The first equation uses an empty initial network and no earlier own response.
Between two consecutive own opportunities there is no other own transmission.
All new foreign entries still pending have fresh identities and occur in D_k,
in their pending order. New entries already included are absent from pending.
Previously pending entries retain their order unless inclusion removes them;
the ledger identifies exactly those removals. This proves the recurrence.

The proof permits arbitrarily many foreign opportunities, arbitrary interleaving,
and arbitrary inclusion order. Inclusion must remove entries without reordering
the ones remaining in the queue, and submitted identities must be unique.
These are the existing operations in
[MessageNetwork](../Interaction/MessageNetwork.lean). A different queue discipline
needs the corresponding readback equation.

Thus the current stateless pending-observation kernel can be simulated from the
complete player's own recall at each local opportunity. No foreign send-time
metadata, callback count or public calendar is required for this base case.
If receipt events can occur independently of transmission decisions, include
them among the local opportunities and retain them in own recall.

### The minimum receipt data for this lemma

The recurrence uses stable entry identity, retained payload, append order of
newly learned entries, own emitted entries, and public inclusion membership.
It does not use a claimed send time. If the actual channel samples an unordered
subset and its update appends selected packets in pending order, the reference
reconstructs the ordered input and performs exactly that update.

If receipts instead carry intermediate arrival times, route traces, counters of
duplicate occurrences or signals from a hidden network state, these are extra
observations. Either their exact conditional law must be generated from the
reference's information and retained local record, or the reference must be
refined. Knowledge of the current pending set alone does not establish this.

## Why visible replay needs more than the old local readback

A replay occurrence can be observed before it is recorded even when its entry
was already public. Erasing that occurrence to WAIT loses an operational event.
The old complete-pending information need not determine its likelihood.

Here is a finite counterexample to that likelihood claim. At a common reached
prefix, a canonical entry q is publicly ledgered. Nature chooses b uniformly
in {0,1}. At time 1,
owner B has a private local opportunity exactly when b=1; when b=0 the service
stutters. In the erased base game its only action there is WAIT. At time 2,
owner A acts. The public clock, ledger, application state and base pending list
are identical in both cases, and A has no earlier own opportunity. Its old
complete information value is therefore the same F.

In the replay expansion B replays q with probability r>0 when its opportunity
exists. The occurrence remains pending until after A's opportunity; this is
compatible with a bounded recording delay. Let A's actual reception reveal
this pending occurrence. Then

\[
 \Pr(I=\mathrm{received\ replay}\mid b=0)=0,
 \qquad
 \Pr(I=\mathrm{received\ replay}\mid b=1)=r.
\]

Both histories have the same old F. Consequently no kernel K(I|F), constant on
that information fiber, can produce the actual observation. Every replay choice
can be source-value independent, and b can be independent of the source initial
state; neither fact repairs this exact failure.

This refutes the proposed old-information likelihood factorization. It is not
by itself an impossibility result for SE preservation in the intended game:
the extra information may concern only service, and a separate gain argument
might be insensitive to it. It does show why reconstructing the global send
word from an unpublicized callback calendar cannot be assumed.

## A proof-only operational refinement for replay

There is a precise probability construction that avoids giving actual players
the global order. Refine the reference player's information to

\[
 F_i^*(h,t)=(F_i(h),\;\text{complete past operational prefix in }(h,t)).
\]

The extra prefix records actual past callback opportunities, entry emissions,
inclusions, public ledger updates, public samples and clock steps. It records
the wire and public effects, not foreign private preparation syntax or hidden
typed binding choices. It also records elapsed latent service flags when they
are not determined by the realized commands. For example, enabled processing
on an empty queue and disabled processing can both produce WAIT, yet a replay
would distinguish them. The extra record contains only elapsed coordinates,
not future service tape. This is a mathematical reference information value;
the actual player is never given it.

Use an explicit latent service history (h,t), where h is the ordinary native
history and t the original service seed. Its actual joint reach weight is

\[
 w_n(h,t)=\operatorname{prior}(t)r_n^t(h)
        =r_n(h)\Pr_n(t\mid h).
\]

The conditional seed law is the actual service posterior after the observed
prefix. It need not be independent of h. Merely attaching a fresh independent
seed to a behavioralized history would be wrong. Summing this joint law over
t gives the original physical history law. If all relevant elapsed service
data are already determined by h, the explicit seed coordinate can be omitted.

The reference effective strategy at F_i^* must remain the selected common
class law at F_i. The probability argument alone does not prove that this
more-informed reference is approximately sequentially rational. That is the
separate refined-reference obligation discussed below.

### Global auxiliary process

Fix a reference latent history (h,t). Its past operational prefix determines the
order in which observation/replay kernels are evaluated, without requiring any
actual participant to know that order. At each local opportunity:

1. Build the actual occurrence queue from the earlier simulated occurrences
   and the fixed base-entry admissions/inclusions in the prefix.
2. Draw the actual fixed reception kernel on that queue and update the
   participant's remembered transport data.
3. For the fixed base class, draw an actual literal representative. For a base
   WAIT, this may be silence or a permitted replay of a known registered entry.
   The replay splitting kernel depends only on that transport record and public
   data, not on a private untransmitted candidate or hidden source value.
4. Retain the focal player's literal preparation aliases and reconstruct its
   private catalogue from its own recalled actions. Sum foreign preparation
   aliases out when they do not affect wire, class menus or future replay
   kernels, as proved by the counted catalogue quotient.

Every auxiliary kernel is normalized. Menus of known replay entries may differ
between actual private histories; normalization is over the actual menu at that
history. The construction does not copy the complete player's larger replay
menu into a private player's information set.

Let K_(i,n)(F_i^*,I) be the resulting probability of the focal actual information
value I after all other auxiliary records are summed out. It may depend on n
through alias and replay rates. The game, service and reception kernels remain
fixed. The current response is not drawn when defining this kernel; only past
base classes and the current reception are used.

For a fixed reference latent history, multiply its chance and common class factors and
then its auxiliary factors. The common class factors do not depend on the
simulated private receipts or aliases. Foreign private preparation factors sum
to one. The remaining auxiliary sum is a function of F_i^*, because that value
contains the entire operational prefix and the focal own fine spine. Therefore

\[
 \Pr_n(H=h,T=t,I)=w_n(h,t)
                 K_{i,n}(F_i^*(h,t),I).
\]

This proves the likelihood factorization rather than assuming independence of
source types. Actual I may mix many refined reference information sets. Bayes
normalization produces their mixture weights, and the native controlled
successor identity gives the same mixture for every one-step gain. Marginalize
over t when comparing ordinary initialized physical laws. Continuation values
must use the posterior conditional on the actual refined signal, including
its elapsed flags; the old posterior given h alone may differ.

### Required transport projection

The displayed factorization also needs the physical projection to be exact.
Erasing a replay must not change the application transition or the inclusion
law of first entries on which the reference payoff depends. This can be
implemented by separate base-entry admission and idempotent occurrence tracking:
first-entry service is allocated independently of duplicate transport load,
while private observers can still see duplicate occurrences.

It is not enough that replay has no second contract-state effect. If a replay
changes which first entry is included, changes its inclusion time, consumes a
fee affecting utility, or changes an adversarial builder's continuation law,
erasure need not preserve the physical runner. A capacity reservation can prove
that these effects are absent, or they can be included in a richer reference
operational game. Bounded eventual inclusion alone does not imply exact
continuation equality at a game deadline.

For instance, with one inclusion slot before a deadline, adding an earlier
duplicate can displace another player's otherwise timely first entry. The
application is idempotent, but the terminal exclusion outcome changes. The
queue-service projection is therefore an actual premise to derive, not a
consequence of duplicate application handling.

## The remaining incentive interface

If one fixed fully mixed reference sequence on the refined F_i^* has uniform
local regret epsilon_n->0, the preceding factorization and controlled
continuation identities prove

\[
 G_{\mathrm{actual},n}(I,a)
   =\sum_{F^*}\Pr_n(F^*\mid I)
                   G_{\mathrm{refined},n}(F^*,\pi_I(a))
   \le\epsilon_n.
\]

One compactness subsequence of the actual fully mixed Bayesian assessments
then gives the actual SE and its projected initialized law. Global send-order
knowledge was used only by the proof reference, never by actual players.

The existing concurrent source comparison contains the mechanical-history-indexed
`Vegas.PhaseProposalQualifiedBinding.qualified_annotation_native_balance` in
[Likelihood](../Vegas/Game/QualifiedBinding/Likelihood.lean), while its
bad-preparation repairs preserve network and environment recall. Those are
plausible producers for a refined-reference
bound under the existing service family: filtering by a past operational word
can preserve an action-independent source likelihood factor. This must be
checked at every local action case, especially waiting, reset and future-service
comparisons. A theorem for an old coarse information set does not automatically
hold after the refinement.

The finite filtered-index and refined-posterior arguments are derived in
[asynchronous reference information](se-asynchronous-reference-information.md).
That note also gives a bounded-inclusion service where no copied,
coarse-measurable reference sequence has uniformly vanishing regret after a
past-service refinement. Thus the refined-reference obligation cannot be
discharged for an arbitrary service solely by calling the added signal
operational.

Likewise, an asynchronous bounded-inclusion contract is not interchangeable
with the existing reserved-tape runner merely because both have a delay bound.
The source comparison still needs legal policy transport, a fixed common
consistency sequence, and the selected joint terminal/payoff law. The
publication lemma above discharges the archive-readback obligation; it does
not alone discharge those service-dependent incentive obligations.

The useful division is therefore exact. Public delay handles unsynchronized
publication of qualifying first entries. Historical authorization and the
excluded-owner comparator handle genuinely late new disclosures. Local pending
readback handles ordinary private reception without a calendar. Visible replay
requires either a controlled occurrence-service projection plus a justified
operationally refined reference, or a separate argument tailored to its actual
continuation gains. None of these steps invents common knowledge of the mempool.
