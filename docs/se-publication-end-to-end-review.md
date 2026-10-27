# Registered transport, replay and equilibrium extension

This note separates three extensions of the padded counted game: observable
retransmission, genuinely new historical disclosures, and audited raw writes.
The distinctions matter because a repeated payload need not be an unobservable
action, and a signature authenticates its author rather than the person who
later retransmits its bytes.

The underlying counted preservation argument is in
[the transfer mathematics](se-publication-transfer-mathematics.md),
[the native adapter](se-publication-native-adapter.md), and
[the padding calculation](se-publication-padding-mathematics.md). The audit
interface is in [the audit boundary](se-publication-audit-boundary.md). The
claims below are finite mathematical arguments, not new Lean theorems.

## 1. One extension with two continuation comparisons

Let R be the padded counted game with its base utility, and fix a selected SE
whose original initialized outcome and payoff law is to be preserved.

1. Add any retained, genuinely neutral network behavior for which a controlled
   strategy and belief construction has been proved. Section 3 gives one such
   construction for visible retransmission under a public deterministic
   transport calendar.
2. Extend directly to all authenticated writes in one application of localized
   enforcement. At copied sites of an active actor, additional actions have
   persistent, completely ledger-observable violation witnesses. At copied
   sites of an already excluded actor, use its permanently fixed base payoff
   and the nonnegativity of audit deductions as a direct comparison.
3. Implement the terminal audit by actual escrow settlement, retaining the
   realized monetary vector jointly with the original outcome.

The source R of this single extension has zero audit charge on every retained
history, including off-path histories. Arbitrary target continuations after
an excluded actor's additional action may incur charges. Their net payoff is
at most its fixed floor, which suffices; equality with the floor is unnecessary.

There is no need to make an excluded actor's new information public. New-only
information sets are completed by an equilibrium-extension theorem, not by
pretending that the original source-policy decoder applies there.

## 2. The mixed comparator and an optional payoff-fixed extension

Let G be the full authenticated action extension of R. At a copied information
set I of player i, define the collection-enforced predicate to mean that i is
not excluded. Exclusion is public, so this is constant across the hidden
histories at I. Use nonnegative deposit D_i and nonnegative audit charge C_i.

For an active actor's additional action, the persistent witness and final
drain give certain collection. With L_i <= base_i <= U_i and
D_i >= U_i-L_i, its target continuation utility is at most L_i. Any retained
source continuation pays at least L_i and is audit clean.

For an excluded actor's additional action, fix arbitrary source and extending
target profiles, any belief on I, and any literal additional action. Permanent
exclusion gives base_i=F_i after every target continuation. Therefore

    E_target[base_i-D_i C_i] <= F_i = E_source[sourcePayoff_i].

Choose the original source profile itself as the source continuation. This
inequality is pointwise in every hidden history before averaging and requires
no evidence collection for this action. In particular, it covers a genuine
old first disclosure, a malformed write, or an additional write that is itself
charged. Other players may react arbitrarily after it.

These are exactly the collection/comparator and direct-comparison
branches of
`GameTheory.Protocol.InformationModel.ActionRestriction.sequential_equilibrium_extends_of_local_collection`
in [LocalizedEnforcement](../GameTheoryExtensions/Analysis/Protocol/LocalizedEnforcement.lean).
One call supplies the raw SE, retained beliefs, and exact initialized joint
terminal-history/payoff law. Its direct comparator is a **source
continuation**; no arbitrary raw continuation is presumed audit clean.

The current-runtime invariant already quantifies over arbitrary response
menus and profiles:
`Vegas.phase_excluded_terminal_payoff` and
`Vegas.phase_excluded_expected_payoff` in
[PhaseExclusionPayoff](../Vegas/Game/PhaseExclusionPayoff.lean).
The backend's additional transitions must preserve that permanent exclusion
and base-payoff definition.

An optional two-stage decomposition is also valid when the first-stage added
actions and all their retained continuations are audit clean. Its elementary
payoff-fixed corollary is as follows.

Suppose an action restriction embeds a finite perfect-recall game R into G.
At every embedded information set I of actor i, every additional action a has
the following property, for every hidden history in I and every continuation
profile in G: all terminal continuations after a give i the same utility F_i.
Assume also that every terminal continuation from I in R gives i F_i.

Then every SE of R extends to an SE of G with exactly its embedded terminal
history and utility law. To verify the actual generic theorem, take the audit
charge and deposit to be zero and classify no action as collection-enforced.
For any source profile, any extending target profile, any belief at I, and any
additional a, the target expectation is F_i. A legal source continuation has
the same expectation. This proves the required direct comparison. The theorem
supplies one consistent rational completion at all new information sets.

The same owning theorem supplies this special case. Arbitrary reactions by
surviving players do not invalidate its source-continuation comparison. The
conclusion does not say that disclosure is irrelevant to those survivors.

A complete action restriction is required: compatible initial states,
histories, information sets, dependent menus, termination, and commuting
retained transitions. Identifying only terminal outcomes is insufficient.

For historical messages the unit of the classification is the physical
attempt/event, not a particular signed body. A closed owned event of an active
survivor must already have an authenticated completing packet in the retained
ledger. A different body for that event is therefore a conflicting second
packet; an identical body is a retransmission. If an event closed without such
a packet, its owner was excluded. This includes commitment events in a failed
commitment block: rollback waits for the block to finish and does not turn an
uncompleted active owner's event into a completed one. The authorization
argument and its source correspondence are given in
[historical authorization](se-publication-authorization.md).

Authorization must certify that the physical phase was actually reached and,
for an opening, that the claimed handle was accepted in that phase. Merely
signing a predictable event/attempt name is not this certificate.

## 3. Observable retransmission without an invisible-ingress assumption

### 3.1 A concrete finite transport instance

Use a fixed public cycle calendar. Every cycle has, in this order:

* one atomic processing batch;
* one callback for each registered player, in a fixed public order;
* the public sample, expiry, and clock updates of the compiled game.

Every processing batch drains every admitted occurrence from the preceding
cycle. It executes the application once for each newly admitted immutable
protocol entry, in canonical first-admission order, and treats further
occurrences of the same entry as application stutters. No strategic callback
or private learn step occurs inside a processing batch. The batch still
records every occurrence and its transport metadata in the public ledger.

An immutable protocol entry and a transport occurrence have different
identifiers. Retransmitting an entry does not consume a new protocol nonce,
change a commitment handle, mutate the private candidate catalogue, or create
a second semantic application input. Its actual receipt and occurrence
metadata remain observable. If a backend increments its semantic nonce or
changes a later legal menu on retransmission, it does not satisfy this model.

At most one chosen transmission occurs per registered callback. For C cycles
and m players, at most mC occurrences require processing. A batch reservation
of mC is a simple sufficient finite bound; with this calendar the sharper
per-cycle bound m suffices before the final tail, provided initialization has
no additional pending traffic. Other initialization traffic must be included
explicitly. Processing and callback capacity are reserved independently of
the application's decision to accept a packet.

The public deterministic calendar is a sufficient concrete instance of bounded
service. It is deliberately narrower than an arbitrary hidden reserved tape.
It gives no player a complete view of the mempool.

### 3.2 What the original fine information determines

Consider the original complete-pending counted game on that calendar. At any
callback of player i, its perfect recall determines the complete transport
history through that callback: the first-admitted protocol entry, if any, at
each earlier callback and the public processing history. This assertion is
about transport entries, not private source values hidden behind commitments.

**Proof.** Before i's first callback, each earlier player in the fixed order
has had at most one callback, and all entries it emitted are in the current
complete pending pool. Between two consecutive callbacks of i, every other
player has exactly one callback. An entry emitted after i's previous callback
is in the next batch's retained ledger; an entry emitted earlier in the
current cycle is in the current pending pool. No entry disappears. Its
authenticated author identifies its unique possible callback in that
interval. Absence of an entry identifies a nonemitting callback. The fixed
calendar gives their order. Player i knows its own outputs. Induction over
i's callbacks reconstructs the whole word. The ledger seen at each callback
in a cycle is the same batch ledger, so the induction also reconstructs the
public ledger available at every earlier player's callback. The deterministic
processing schedule supplies the empty batches as well. ∎

Include in this reconstructed word the public sample outcomes and the phase
installation records used by canonical authorization. There is at most one
sample between consecutive focal callbacks, its fresh public variable remains
visible, and public phase transitions can be replayed from the ordered batch
and public sample/expiry commands. The authorization readback argument in
[historical authorization](se-publication-authorization.md) supplies those
records; it does not infer a private candidate's value.

Denote the resulting transport/public word by T(F), where F is the original
fine information of the observing player. A private reception law that reads
only the pending transport data, together with causal local receipt memory,
can therefore be simulated conditional on T(F). It cannot read an
untransmitted source value or a private preparation catalogue.

### 3.3 A full-support replay construction

At a nonemitting callback allow an additional choice: retransmit an immutable
entry already known to that broadcaster. Knowledge is causal transport
knowledge: its own previously admitted entries, entries in the public ledger,
and entries received through the specified observation kernels. Initial
signature capabilities are fixed by authentication; arbitrary correlated
source inputs do not grant another player's signing key or an unobserved
authenticated entry. A new signed body is a first admission, not a replay.

Choose a positive replay-splitting law at every such callback. It has positive
mass on ordinary silence and on every currently known replay entry. Its
parameters depend only on the broadcaster's transport knowledge and public
transport history. They do not depend on a hidden source input, private
commitment value, or discarded preparation alias. The ordinary-silence mass
tends to one, uniformly over the finite collection of local transport states.
Full support is retained at every positive index.

Start with the original fine fully mixed reference profile beta_n. First draw
its effective action. If it emits a fresh protocol entry, emit it. If it is
nonemitting, use the positive splitting law to choose silence or a known
retransmission. Private preparation components of the retained action, if
present, are preserved; retransmission adds only transport occurrence data.
This specifies the retained enlarged action menus precisely. Additional
private preparations must be accounted for by the existing controlled alias
adapter rather than silently discarded.

Let w denote the complete auxiliary word of private reception draws and
replay choices before a fine callback. Along a fixed original transport word
T, its probability is a product of normalized finite conditional reception
and replay kernels. The set of nonemitting callback slots is determined by T.
The body menu at every auxiliary choice is determined by the already generated
own transport record. Thus this product is a kernel K_n(T,w), independent of
the source state once T is fixed. Summing over complete auxiliary words gives
one, by backward summation of the normalized finite kernels.

Consequently, at aligned callback cuts, the expanded reach weight factors as

    r_n^+(h,w) = r_n(h) K_n(T(h),w).

For h in one original fine information set F, T(h)=T(F). Conditioning further
on any recorded auxiliary information multiplies every such h by the same
likelihood. Its normalized conditional belief is therefore the original
Bayes belief at F. Zero-mass records are omitted before division; every
feasible record has positive reach under the full-support sequence.

This argument also permits retransmission of a **still-pending** entry that
the broadcaster actually knows. The entry need not already be public: its
body and first admission are part of T(F), and the private knowledge process
is generated by transport kernels. It does not permit a first transmission
of a privately retained, previously unadmitted signed body. Historical first
admissions belong to Section 2 or to the audit classification.

### 3.4 Controlled gains and law preservation

Erase duplicate occurrences and their metadata at callback and batch cuts.
Each ordinary action projects to its original effective action; each replay
projects to the corresponding nonemitting action. An atomic batch has the
same projected application successor as the original batch: duplicate
application transitions are identities, canonical new-entry order agrees,
and no player chooses inside the batch. The fixed clock and sample/expiry
positions are unchanged.

Prescribed future class policies read the projected original information.
They ignore the auxiliary receipt/replay word. Future transport replay laws
can change that auxiliary word, but cannot change the projected chance law,
application state, menus, or payoffs. Backward induction therefore proves,
for every original history h and every added record w, equality of projected
terminal laws under the prescribed continuation. The same equality holds
after forcing any current enlarged action, with its projected original
action forced at h.

Together with the posterior factorization, this gives the exact local-gain
identity

    G_n^+(F,w,a) = G_n(F,pi(a)).

For a replay pi(a) is WAIT; it is not a new source move. Uniform vanishing
original fine regret therefore remains uniform vanishing regret in the
enlarged fine game. Taking a common subsequential limit yields an SE with the
same initialized projected outcome/payoff law. The replay probabilities can
vanish in that limit, preserving even the original no-replay execution law.

For actual private reception, use the same probability argument directly on
the **masked physical/effective base tree** of the native adapter. At each
actual information set draw the common semantic class law, choose an ordinary
literal alias from its positive normalized fibre, and split its nonemitting
class over that actor's actually known replay entries. The replay splitting
reads only transport knowledge, not the private preparation catalogue or the
ordinary alias record except through emitted transport data. These replay
menus can differ from the complete-observation menus; no player is asked to
copy an unknown packet. The source query supplied by the publication barrier
makes the semantic class law measurable in actual information.

Ordinary aliases require a separate summation from replay noise. Fix a masked
physical/effective base path h and a complete transport/reception/replay word.
Every ordinary alias in the fixed class has the same controlled masked
successor and exact emitted packet. Future common class laws depend on the
masked path and common source key, rather than on discarded alias memory.
Replay kernels also ignore that memory. Sum the ordinary alias choices of
each **foreign** player from last to first. Each conditional alias fibre sums
to one, even if its probabilities and literal menu depend on that player's
private source input, catalogue, or earlier aliases. No independence of
players' initial inputs is used. The native controlled-menu result guarantees
that every fixed base class still has its positive normalized fibre after
every such alias history.

For the focal player retain its actual alias word, because it belongs to its
information I. Its probability is a product of the focal alias kernels. Each
kernel's arguments can be reconstructed from the original fine own spine,
the initial own catalogue, the focal literal record already generated, and
the simulated transport receptions. This is exactly the causal own-catalogue
property of the native adapter. It is not a claim that the literal record is
determined by the masked path.

After foreign-alias summation, sum all private reception/replay words that
produce I. All semantic class factors are the original factors. The remaining
factor is therefore **K_i,n(F,I)**: its transport part depends on T(F), and its
retained focal-alias part depends on F and the causal focal record. It need
not be a function of transport alone. At aligned callback cuts,

    r_actual,n(h,I) = r_n(h) K_i,n(F(h),I).

All normalization is conditional on the already fixed past: foreign alias
fibres sum to one, replay kernels sum to one on their actual known-entry
menus, and reception kernels sum to one. Thus K_i,n is normalized over
feasible focal records for each F. The actual projected posterior is a mixture
of the original fine posteriors, exactly as in the transfer document.
Controlled continuation equality gives

    G_actual,n(I,a)
      = sum_F Pr_n(F | I) G_n(F,pi(a)).

This proves the same uniform regret bound. The global auxiliary-word
factorization is essential here: merely treating all replays as equal fine
and actual action menus would be false for still-private entries. Every
literal replay is covered by the WAIT projection; actual receipt memories
remain in I. Finiteness and the one fully mixed actual sequence complete the
SE limit argument.

The controlled suffix statement also holds after every literal one-step
deviation. For an ordinary alternative, use the native all-class controlled
successor equation and retain its actual new private alias record. For a
replay, retain its occurrence and own memory while projecting to the chosen
nonemitting class; the replay does not change catalogue or semantic nonce.
Thereafter each prescribed foreign alias fibre again sums to one, every
replay kernel is normalized on its actual knowledge menu, and the same common
semantic class law applies. Induction on the remaining finite horizon proves
the terminal-law equality from these modified successors. Thus the displayed
gain identity uses actual continuation after the deviation, not merely the
initialized projected law.

This is an explicit sequence construction, not an application of the
payoff-fixed extension lemma. A still-active broadcaster is generally not
indifferent under arbitrary continuation profiles after replay; the specified
continuations and the likelihood factorization are essential.

### 3.5 The hidden-calendar boundary

State-neutral replay is not enough for the preceding proof if processing
epochs are hidden. Suppose an otherwise empty queue has an optional
processing epoch. Without replay, the actor's original fine information
cannot distinguish whether it happened. With a replay in the queue, its
ledger inclusion reveals the epoch. If the service tape has correlated
coordinates, this can reveal information about future service. The original
fine information does not determine the replay transcript's likelihood.

Similarly, if only a player in one hidden state is offered an auxiliary
callback, observing its message reveals that state even when the offered
menu and the chosen coin are individually state independent. Public menus
alone do not establish the required posterior factorization.

The deterministic public calendar above removes both issues. An extension to
arbitrary hidden activation/processing tapes needs another information and
gain argument; it does not follow from deduplication or eventual inclusion.

## 4. First departure, not repeated re-proving of the decoder

In a retained history with no earlier nonstandard action, classify the first
new authenticated admission by its physical event:

* It is an ordinary current retained action.
* It is an exact retransmission already covered by the controlled replay
  extension, or a transport redelivery of the same immutable admission.
* It is a genuinely authorized historical first event packet by an already
  excluded actor, covered by the direct fixed-base-payoff comparison.
* It carries a persistent audit witness, such as intrinsic malformed
  content, false authorization, a conflicting second event packet, or
  forbidden handle reuse.

Once an excluded-owner disclosure occurs, later active players can know
and relay that newly disclosed value. Those histories need not satisfy the
old source-archive decoder. They lie in the full extension's new region,
where the joint consistent completion is supplied. Likewise,
after an audited first departure, the enforcement theorem quantifies over
arbitrary subsequent policies. It is a mistake to require the original decoder
again at every descendant of either departure.

The classification must be exhaustive for the actual action domain. An actor
cannot evade it merely by calling a first admission a replay: immutable entry
identity and prior admission must be checked. An outer signature identifies
the author of that entry, not necessarily the broadcaster of its later byte
copy. New authenticated ingress writes and network redelivery of an existing
ingress item are different events.

## 5. Audit and settlement requirements that remain physical

For a registered finite session, admit and retain every bounded authenticated
outer write, regardless of its inner application's validity. Close new
strategic admission, drain every remaining admitted write to the ledger, and
compute a deterministic public violation predicate. This realizes observation
and collection probabilities equal to one; no strategic reporting decision is
needed. An audit witness must persist under addition of later traffic.

With bounded base utility L_i <= u_i <= U_i and one Boolean charge C_i, choose
collectible collateral D_i >= U_i-L_i. After a first forbidden write,

    E[u_i-D_i C_i] <= U_i-D_i <= L_i.

A retained clean source continuation pays at least L_i. The inequality is
uniform in every later policy and hidden history and uses no independence
between utility and collection. Use it for active actors' additional actions.
Excluded actors' additional actions use the direct upper bound F_i from
Section 2. Thus historical first disclosures do not require a separate
audit-clean intermediate game.

The terminal payout must actually have the form

    transfer_i(z) - D_i C_i

with declared private valuation added only when evaluating utility. Funds
reserved for the audit must be collectible without depending on the actor's
cooperation or on receiving future incoming transfers. Ordinary source
transfers and service costs need their own funded account. Returning the
original stake on a clean path is a cash-flow operation, not an extra source
reward. An unconditional service subsidy or a specified pre-funded service
budget is part of the backend's economic model and must not silently alter
the selected net payoff vector.

The existing monetary APIs explicitly retain actual receipts jointly with
outcomes; see
`GameTheory.Enforcement.TerminalAudit.jointSettlement_add_valuation` and
`GameTheory.Enforcement.TerminalAudit.jointSettlement_sub_valuation` in
[QuasilinearSettlement](../GameTheoryExtensions/Analysis/QuasilinearSettlement.lean).
An abstract expected-utility inequality alone does not prove that the proposed
escrow can pay every realized transfer vector.

## 6. Scope of the closed transport model

The finite reserved-session construction covers every authenticated message
that becomes visible through that session's transport. It does not by itself
cover arbitrary private Internet messages or an underfunded transaction that
is privately shown to one opponent but never admitted to the retained
transport. Such a message may reveal a verifiable private value without
leaving collectable ledger evidence.

This is not repaired by increasing the deposit. If the collection probability
for a profitable disclosure is zero, the expected charge is zero at every
deposit size. Either the communication is included in the game and supplied
with an authentic collection mechanism, or the preservation claim must state
the registered communication boundary. The same qualification applies to
cryptographic implementation of ideal opaque commitments and authentic
certificates: the finite theorem uses their stated ideal behavior, not an
unproved assertion of exact information-theoretic security for a concrete
hash implementation.
