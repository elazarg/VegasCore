# Private service signals with an exclusion loss above the payoff range

**Deterrence: aggregate bound checked · concurrent common-abort proof below · general native SE open.**

The full three-player native equilibrium obstruction remains pending. This
note changes neither the preservation target nor the service assumptions in
the checklist.

The model here has permanent exclusion, commitment-phase reset, and the
count audit. Exclusion replaces the owner's payoff by a fixed constant. This
is not the older additive-forfeit model, which keeps the program utility and
subtracts a penalty for each failed reveal.

## A sufficient stronger exclusion loss

For the failure-reward class below, a loss above one player's reward range
is unnecessarily weak. A loss exceeding the total reward that one exclusion
can give the other players rules out exclusion in **every equilibrium**.
This is a positive result for the whole class, regardless of the service's
private signals or the players' adaptive timing policies.

Let there be \(n\) players and let \(E_i\) be the event that player \(i\)
is excluded. Normalize the failure-free payoff to zero. Suppose that:

- each player has a feasible unilateral continuation guaranteeing expected
  net payoff at least zero against the equilibrium opponents;
- on \(E_i\), its net payoff is at most \(-F_i\);
- off \(E_i\), its net payoff is at most
  \(R_i\sum_{j\ne i}\mathbf1_{E_j}\), where \(R_i>0\).

Nonnegative audit deductions are allowed. The last condition includes reward
at most \(R_i\) for any foreign exclusion, even if several exclusions do not
give several rewards. The first condition is a security guarantee; it does
not follow merely from equilibrium in an arbitrary source game.

**Theorem.** If

\[
 F_i>(n-1)R_i\qquad\text{for every }i,
\]

then every Nash equilibrium, and hence every sequential equilibrium, has
\(\Pr(E_i)=0\) for every player.

The finite-law conclusion is checked in
`GameTheory.FailureReward.supported_exclusion_free` and
`GameTheory.FailureReward.exclusion_probabilities`, from actual supported
terminal payoff bounds and nonnegative expected payoffs. A native game
application must supply those premises from its own strategy and security
theorems. The result does not assume an inequality about failure probabilities
in place of the terminal payoff argument.

**Proof.** Use the equilibrium's actual initialized law throughout and put
\(p_i=\Pr(E_i)\). The security guarantee and best response imply
\(\mathbb E U_i\ge0\). The terminal bounds imply

\[
 0\le\mathbb E U_i
 \le R_i\sum_{j\ne i}p_j-F_i p_i.
\]

Divide by \(R_i\) and sum over players. Each \(p_j\) occurs in precisely
\(n-1\) foreign sums, giving

\[
 0\le\sum_i\left(n-1-\frac{F_i}{R_i}\right)p_i.
\]

Every coefficient is strictly negative and every probability is nonnegative.
Thus all \(p_i\) are zero. No independence or lower bound on a late packet's
failure probability is used. This argument concerns initialized equilibrium
payoffs; it does not assert a separate security guarantee after every
off-path observation.

For the three-player reward-one construction, **\(F>2\), for example
\(F=3\), suffices** under the stated security guarantee. If raw forbidden
packets are excluded using the existing silent-comparator audit argument,
its charge must also be increased: charge \(K>F+1\), for example \(K=5\)
when \(F=3\). Then a charged continuation has payoff at most \(1-K<-F\).
These numbers are independent of the builder's late-inclusion probabilities.
The installed fixture still has \(F=3/2\) and charge 3; changing those
constants has not been mechanized as a native theorem.

This theorem removes the failure-reward incentive, rather than prescribing
a particular waiting policy. It does **not** yet preserve a selected source
equilibrium's value distribution. For general source utilities, a protected
continuation may guarantee only the utility floor, below the selected
equilibrium value; the preceding summation then contains nonzero slack.
Moreover, timing may transmit private source information even when exclusion
does not occur. Those are the remaining obligations for general preservation,
not consequences of the aggregate bound.

## Common abort for general source utilities

A stronger settlement removes the reward for another player's delivery
failure altogether: **the first physical failure stops execution and gives
every player its fixed low abort payoff** \(C_i\le\min u_i\). Completion
still pays the source utility \(u_i\). This section proves sufficiency for
concurrent blocks under the service interface stated here. Both this
settlement and that interface are proposed alternatives; they are not the
current reset/exclusion semantics or consequences of `AsyncContract` alone.

Use the [value-blind delivery interface](commit-reveal-research/whole-game-delivery-preservation.md)
with the following concurrent extension. There are finitely many fixed
blocks, independent of values. In a commitment block, incomparable source
choices retain their original information until their respective values
are fixed; opaque foreign commitments disclose no new source value. Here
incomparability concerns source dependencies, not statistical independence:
original private parameters and values may be correlated. A choice becomes
selectable only after all its source-information predecessors; from its
first eligible selection until locking, its source information stays fixed. Within
a reveal block, values are already fixed, and the next genuine source
choice waits for the source barrier. Own dependent choices retain their
original source order. Every legal logical choice, including a legal
decline if present, has the same mechanical carrier interface.

The service has a finite mechanical game whose state records tasks, clocks,
callbacks, receipts and operational randomness. Its initial randomness is
independent of the source parameters. Mechanical transitions, menus and
observations ignore **all logical data, including earlier public results**.
At mechanical view \(W=w\), the identities of any source fields exposed by
pending or received packets are determined by \(w\); their values form a
logical view \(S\). A genuine source decision observes exactly its original
information \(I\), mechanical recall \(W\), and fields determined by them.
These are requirements on complete remembered inputs and transition laws,
not a hypothesis that arbitrary observations add no knowledge.

**Theorem for this interface.** For each service, one can choose a delivery
policy, independently of the selected source equilibrium, such that every
source SE extends to a target SE. Conditional on completion, its joint law
of original parameters, source results and payoffs is exact. If there is a
canonical delivery policy completing surely, the preservation is
unconditional, and abort never occurs on equilibrium paths.

**Proof.** Give every decision agent in the mechanical game payoff one for
whole-execution completion and zero for abort. For each sufficiently small
\(\varepsilon>0\), maximize completion probability over the compact product
of action simplexes with every probability at least \(\varepsilon\).
At every legal mechanical information set \(W\), reach is positive. Divide
the maximizer's one-site comparison by that reach *before* taking limits.
For a menu of size \(m_W\), conditional regret against any pure action is
at most \((m_W-1)\varepsilon\). One common convergent subsequence of
strategies and all Bayes beliefs therefore supplies a consistent mechanical
assessment with optimal local completion probability \(q(W,\cdot)\),
including at limiting zero-reach inputs. Global maximization also makes its
initialized completion probability at least that of every fallback policy.

Combine this sequence with the chosen source SE's fully mixed consistency
sequence. Virtually sample a commitment block's source choices in their
canonical source order. This is only a coupling: it adds no observations
and forces no earlier physical action. Unchanged source information makes
their joint law independent of the mechanical callback order. Let \(g\)
contain the logical prefix and these virtual choices, and \(\omega\) the
mechanical prefix. Multiplying the actual kernels gives prefix weights

\[
 w'_n(g,\omega)=w_n(g)Q_n(\omega).
\]

Compatibility uses the task positions recorded in \(\omega\). At each
barrier, append the original source transition and chance kernel. For fixed
\(W=w\), the event \(S=s\) imposes a restriction \(L(s,w)\) on \(g\)
alone. Thus the actual conditional belief at \((S,W)\) is the product

\[
 \Pr_n(g\mid L(s,w))\,
 \Pr_n^{\rm mechanical}(\omega\mid W=w).
\]

Partial reveals can change the first factor. They leave the second factor
equal to the mechanical assessment's own posterior. The combined sequence,
with a further common subsequence for the finitely many extra beliefs,
gives consistency of the target assessment.

At a delivery decision, let \(V_i(g)\) be the expected source utility after
completion and the prescribed logical continuation. The gain from a
mechanical action \(a\) is

\[
 \bigl(\mathbb E[V_i(g)\mid S,W]-C_i\bigr)
 \bigl(q(W,a)-q(W,\pi_*)\bigr)\le0.
\]

The first factor is nonnegative by the abort floor; the second is
nonpositive by the mechanical comparison. At a source decision, completion
is independent of the selected value and entire logical continuation, so
the target gain equals \(q_J\) times the source gain. It is nonpositive by
source sequential rationality. If an actual menu combines `WAIT` with
`SEND(value)`, write \(V^*\) for the prescribed source value. Any joint
alternative satisfies

\[
 q_a(V(v)-C_i)\le q_a(V^*-C_i)
                 \le q_{\pi_*}(V^*-C_i).
\]

Waiting here preserves source information, and sending makes the value
immutable. These comparisons cover arbitrary local actions at full inputs;
they do not restrict deviations to value-blind policies. Finite perfect
recall gives rationality against whole adaptive continuations.

Finally, the completed joint law factors as \(pQ_\sigma\), with remaining
mass on the distinct abort outcome. A surely completing fallback gives
\(p=1\), since the mechanical maximizer does at least as well. That
fallback requires actual timely callbacks, admission of valid packets,
sufficient deadline margin and finite barrier advancement. A receipt which
can report rejection does not suffice.

**Boundary.** The interface does not include arbitrary raw payloads or
source-dependent future service. Extra raw messages still require the
existing audit and consistent-completion argument. If future service
reliability depends on a public source result, \(q\) can depend on the
logical continuation and the displayed products need not hold. Thus common
abort is a proved mathematical alternative for the specified concurrent
interface, not yet a preservation theorem for the existing bounded raw
runtime. The interface, raw adapter and settlement would all need explicit
adoption and mechanization before any preservation checklist box could close.

## Payoffs and source program

There are three owners, Alice, Bob and Carol. Each commits one Boolean under
a TRUE guard, and then reveals it. Commitments form one concurrent phase;
the reveals form a later concurrent phase. The initial context is empty and
there is no Nature draw. Boolean values do not affect utility.

For each owner, a successful terminal publication pays 1 if at least one
other owner's publication fails, and otherwise pays 0. Own exclusion pays
the constant

\[
 a=-F=-\frac32.
\]

Thus the entire nonexcluded payoff range is \([0,1]\), of width 1, and
\(F=3/2>1\). Multiple foreign failures never add multiple rewards. A count
charge of 3 is collected once from an owner who takes a forbidden action.
The gross terminal range, including exclusion, has width \(5/2<3\).

Every honest source profile has all three publications successful and gives
every owner zero. In particular, committing TRUE and revealing it is an
honest source sequential equilibrium.

The proposed native conclusion is stronger than failure of a particular
delivery prescription: **every native sequential equilibrium gives Alice
expected net payoff at least \(21/1000\)**. Consequently none preserves that
honest source payoff law. The native formalization must establish this
universal claim, not merely exhibit a profitable deviation against one
candidate equilibrium.

## Checked boundary

The [native fixture](../Vegas/Examples/CommitSeedBroadcast.lean) includes checked
source well-formedness, zero honest payoff and honest SE existence
(`Vegas.Examples.CommitSeedBroadcast.exists_honest_sequentialEquilibrium`).
The initialized service law has independent original coordinates
(`Vegas.Examples.CommitSeedBroadcast.nativeSeedLaw_independent`) and the exact
order/cut factorization
(`Vegas.Examples.CommitSeedBroadcast.nativeSeedLaw_partition_expect`).

The actual first-late physical kernel retains every private preparation,
pending packet and own response record
(`Vegas.Examples.CommitSeedBroadcast.nohelper_first_late_physical_kernel`).
Its initialized full-input likelihoods satisfy the bad and all-good bounds
(`Vegas.Examples.CommitSeedBroadcast.quiet_firstLate_bad_mass_le`,
`Vegas.Examples.CommitSeedBroadcast.quiet_firstLate_all_good_mass`). These
quiet-prefix kernel statements do not assume that fully mixed consistency
approximants themselves always WAIT initially.

Actual raw audit incentives restrict the unchanged assessed continuation to
the count menu
(`Vegas.Examples.CommitSeedBroadcast.counted_assessment_finish_eq`). All raw
plays complete within horizon 128, and every ready owner has its opportunity
(`Vegas.Examples.CommitSeedBroadcast.family_completesPlay`,
`Vegas.Examples.CommitSeedBroadcast.family_opportunity`).

The checked service contracts include
`Vegas.Examples.CommitSeedBroadcast.family_asyncContract`,
`Vegas.Examples.CommitSeedBroadcast.family_privateActivationCalendar` and
`Vegas.Examples.CommitSeedBroadcast.family_privateBindingSuccess`.
The full assessed first-late bounds are
`Vegas.Examples.CommitSeedBroadcast.assessed_firstLate_bad_le` and
`Vegas.Examples.CommitSeedBroadcast.assessed_firstLate_regular_lower`.
They imply the actual unchanged equilibrium response cannot WAIT at the
empty-ledger first-late input
(`Vegas.Examples.CommitSeedBroadcast.raw_first_late_response_ne_wait`).
This includes off-path inputs; it assumes neither a clean belief nor the
desired future survival. Proper continuations survive after original admission
(`Vegas.Examples.CommitSeedBroadcast.scheduled_proper_original_binding_survives`).
Complete observations transport a counted representative to every raw history
in the same full information fiber
(`Vegas.Examples.CommitSeedBroadcast.counted_input_raw_fiber_trace`).

All 230 owners passed warning-strict checks and the full 7,131-job public
build. Selected capstones have guarded axiom reports
containing only `propext`, `Classical.choice` and `Quot.sound`.
The remaining proof includes the helper's later conditional belief argument,
continuation payoff comparisons and the all-equilibrium contradiction. No preservation checklist
box closes on these partial results.

The actual equilibrium waits at the helper's bad clock-two slot
(`Vegas.Examples.CommitSeedBroadcast.raw_helper_clock_two_response_wait`)
and transmits at its last opportunity after the remembered receipt signal
(`Vegas.Examples.CommitSeedBroadcast.raw_clock_three_response_ne_wait`).
Protected opening incentives imply actual equilibrium survival
(`Vegas.Examples.CommitSeedBroadcast.counted_assessed_publication_finish_survives`).
Regular all-good prefixes admit every original binding
(`Vegas.Examples.CommitSeedBroadcast.regular_assessed_original_admission`).
An admitted unusable original preparation then has the fixed loss, derived
from its actual recorded declaration and all three original receipts
(`Vegas.Examples.CommitSeedBroadcast.all_original_admissions_unusable_record_payoff`).
Supported original preparations at the empty-receipt clock-two input and at
the initial opportunity are usable Boolean material
(`Vegas.Examples.CommitSeedBroadcast.raw_first_late_response_usable`,
`Vegas.Examples.CommitSeedBroadcast.raw_early_response_usable`).
The clock-two comparison gives a strict expected gain of at least \(1/32\)
(`Vegas.Examples.CommitSeedBroadcast.raw_unusable_clock_two_context_gap`).
The exact quiet initial controls and their original seed posterior are also
checked, as is the initialized quiet proper deviation's payoff lower bound
of \(21/1000\)
(`Vegas.Examples.CommitSeedBroadcast.quiet_initialized_proper_clock_two_value_lower`).
This last bound assumes quiet initial policy responses; the backward argument
that forces those responses remains open.

## Original service experiment

Each original commitment has an independent private bit, good with probability
\(q=9/10\) and bad with probability \(\delta=1/10\). Independently, draw a
uniform permutation \(\pi\) of the three owners. The permutation belongs to
the builder's remainder randomness. All later retry and publication service
is protected and deterministic; it does not need these original bits.

The original schedule is as follows. Each poll has a fixed command slot;
an inactive poll is an identity WAIT. No extra player response accompanies
an identity WAIT.

1. At clock 0, activate Alice, Bob and Carol in that fixed order. Retain the
   immutable snapshot of packets emitted at these three callbacks. Call
   these the EARLY packets.
2. Advance to clock 2. In permutation order, poll each good owner once.
   Bad owners' slots are identity WAITs.
3. Still at clock 2, include all EARLY packets from the retained snapshot.
   Use separate ordinary inclusion commands, with no player callbacks
   between them. Empty snapshot slots are identity WAITs. Do not include
   packets emitted at clock 2 in this middle block.
4. Still at clock 2, in permutation order poll each bad owner once.
   Good owners' slots are identity WAITs. A completed original coordinate
   is skipped.
5. Only after all clock-2 polls, include the original packets emitted at
   clock 2 by good owners. Packets emitted at clock 2 by bad owners do not
   obtain original acceptance.
6. At clock 3, give the remaining original owners their next callbacks.
   Afterwards include their clock-3 original packets exactly for bad owners.
7. At deadline 6, expire unresolved original coordinates. Apply the actual
   commitment reset or exhausted close, then run the protected retry and
   publication tail.

An original packet sent at clock 0 is protected. For example, a bound of 5
and deadline 6 permits its inclusion at clock 2, while protected inclusion
does not force admission of packets first sent at clock 2 or 3. Late
admission reads the owner's original bit and its actual emission clock.
Its accepting native handler still checks the genuine owned fresh handle.
An admitted commitment can have an unusable hidden preparation: admission
and eventual successful publication are different facts.

This is a finite command schedule built from the existing activation,
inclusion, clock-advance and expiry operations. Its native certificate must
give a uniform finite horizon, all-raw completion, and the exact service
predicates for original, retried, skipped and retired coordinates. The audit
does **not** charge a player for a service omission. It charges forbidden
emissions; silence and an ordinary first packet remain uncharged.

The privacy interpretation is the existing addressed service interpretation:
independent local service seeds, with the remainder reacting to history.
The counterexample does not assume an additional clock-word sufficiency or
knowledge-neutrality condition. Establishing the native contract under this
interpretation is part of the pending certificate, not a new premise being
silently added to the preservation target.

## Why the first late input does not identify its seed

Let \(K\) be the number of good owners, and let \(\sigma\) be the permutation
obtained by listing the good owners in their \(\pi\)-order and then the bad
owners in their \(\pi\)-order. For each fixed permutation \(s\) and
\(k\in\{0,1,2,3\}\),

\[
 \Pr(\sigma=s,K=k)
 =\frac{\binom3k}{3!}q^k\delta^{3-k}
 =\frac1{3!}\Pr(K=k).
\]

Indeed, the good set must be the first \(k\) entries of \(s\), and there
are \(\binom3k\) interleavings of its prescribed order with the prescribed
bad-owner order. Hence \(\sigma\) is uniform and independent of \(K\).

Suppose all initial responses were WAIT. The middle inclusion block is
then an identity block. Before every first late response, the clock is 2,
there has been no inclusion or expiry, and the observable response order
is a prefix of \(\sigma\). Changing the split point \(K\) while retaining
\(\sigma\) does not change that physical input. This retains the entire
own recall, pending envelopes, private own catalogue, public typed store
and receipt list, not just the current clock or an unobserved environment
log. Previous responses use those same inputs, so their behavioral
likelihood factors also agree. This holds for arbitrary behavioral
policies and private preparations.

Consequently, at every positive no-helper first-late full input, \(K\)
still has its binomial law. The owner may learn its position in
\(\sigma\); that does not reveal \(K\). Its conditional bad probability
is at most

\[
 p\leq\Pr(K<3)=1-q^3=\frac{271}{1000}.
\]

The same upper bound holds at the relevant full inputs with an empty
receipt ledger that mix these histories with histories having an EARLY
helper. In a helper history, a callback after the middle block has a
retained true EARLY receipt. Thus a helper history in an empty-ledger
fiber has its current owner in the good group; it adds no bad mass.
This argument does not identify an arbitrary pending commitment envelope
as EARLY. A clock-0 packet and a prior clock-2 packet can have the same
visible form. In particular, an empty ledger need not tell an owner that
a helper exists.

The factorization is a statement about the original seed experiment and
the complete native input. For zero-probability inputs under an assessment,
apply the same uniform likelihood inequality to its fully mixed consistency
sequence and pass to the limit. It is not an assertion of fairness after
conditioning on a physical environment log or on an arbitrary deviation.

## Which raw information fibers are used

The argument needs the inputs reached from a quiet initial prefix, and
those reached after a permitted EARLY packet or a proper unilateral
continuation. Complete pending observation, the public ledger, and the
owner's literal recall expose every transmitted envelope. Their retained
packet counts and shapes must therefore be classified on the **whole** raw
information fiber before using the acceptance statements below.

A counted representative supplies a direct full-fiber test. At a genuine
callback, complete pending observation together with the public ledger exposes
every foreign submitted envelope; literal own recall exposes every own one.
Equal complete inputs therefore identify the entire submitted envelope set.
The count verdict depends only on membership and earlier authored serials,
so every raw realization of that same input has a clean signed record. A
forbidden recorded action could not precede that endpoint: its envelope and
forbidden verdict persist. Anchoring the actual retained actions consequently
recovers a counted trace at the identical physical control. This transfers
counted continuation results to the raw belief fiber without assuming a
counted consistent assessment.

This does not require usable hidden preparations. Hidden preparation and operationally invisible evidence aliases
are retained. What matters for original commitment admission is the
observable first owned commitment envelope and its genuinely fresh handle;
an unusable preparation still has that admission. Histories with visible
extra packets, malformed markers or incompatible addresses cannot be
inserted into this classification merely because some other actual run
was clean.

The count audit supplies the other reduction. At any information set with
an uncharged own past, taking a forbidden action gives net payoff at most
\(1-3=-2\), under every later continuation. A charge-free continuation
gives at least \(-3/2\). Thus no such action is supported in a sequential
equilibrium, including at off-path raw information sets. Silence or a
permitted first owned packet exhaust the relevant choices. After a first
packet, a second packet is forbidden. This is the load-bearing one-packet
restriction; a player cannot send at both eligible late clocks for free.

## First-late timing and hidden preparations

Consider an unsent owner's first late callback at a genuine counted input,
with empty receipt ledger.
Its initial own response was WAIT. If it WAITs at clock 2, a good seed
can never obtain original admission: the sole good late slot has passed.
Waiting cannot obtain an early reset that saves this missing coordinate;
the original phase cannot close before that coordinate resolves. On a bad
seed its terminal payoff is at most 1. Hence its WAIT value is at most

\[
 p-\frac32(1-p).
\]

A proper first packet at clock 2, followed by a proper protected tail,
survives on every good seed and has payoff at least 0 there; a bad seed
pays \(-3/2\). This whole continuation has value at least \(-3p/2\).
The difference is

\[
 F(1-2p)-p\geq\frac32-4\frac{271}{1000}
 =\frac{416}{1000}>0.
\]

Here \(p\leq271/1000<3/8\), the strict-comparison threshold. Thus every
relevant first-late empty-ledger input uses a nonsilent first packet at clock 2. The
inequality is uniform over its full raw belief fiber. It
compares a whole feasible continuation with the incumbent WAIT value;
sequential optimality then rules out WAIT in its current support.

If a first-late callback has a true middle EARLY receipt, it is after the
middle block and its owner knows that its seed is bad. SEND at clock 2
then loses original admission surely. WAIT followed by a proper clock-3
packet guarantees survival, so the owner waits at 2. At the clock-3
callback the earlier receipt and WAIT are in its perfect recall. It sends
in its known eligible slot. A later empty ledger at clock 3 is not used
as a substitute for that recalled receipt.

These timing conclusions do not assume usable private preparation. They
first determine the original admission pattern. Without any EARLY packet,
all first-late responses are sent at 2, and original admission is exactly
the vector of independent good bits. With an EARLY packet, every original
binding is admitted: EARLY bindings in the middle block, good unsent
owners' packets at 2, and bad unsent owners' packets at 3. There is then
no commitment reset.

Usable preparation requires a separate comparison. The all-good posterior
bound alone does not give a positive probability of no reset at an arbitrary
off-path input: consistency beliefs can retain an earlier owner's mistaken
WAIT at clock 2. The following prefix rearrangement supplies that probability.

Fix a relevant full input \(I\) with empty receipt ledger. In each physical
prefix in its fiber, retain the literal initial three responses, including
their hidden preparations, and every earlier clock-2 emission in order.
Choose the all-good seed and the permutation consisting of those emitting
owners, then the current owner, then the remaining owners in fixed order.
This moves the earlier silent clock-2 callbacks behind the current callback.
The resulting prefix is genuine and lies in the same full-input fiber.

To check this assertion, a silent response changes no native state, packet,
receipt or other owner's observation. It changes the silent owner's recall
and learned network knowledge, and the hidden environment log. Each retained
emitter and the current owner has only its initial response before its unique
clock-2 callback, so none reads that changed foreign recall. Every retained
response therefore has exactly its original complete input and behavioral
likelihood factor. The current owner's entire input, including its initial
view and literal WAIT record, is unchanged. This asserts equality of these
player inputs, not equality of whole physical executions.

The construction preserves all hidden choices in retained responses. Given
the constructed prefix and an original chance outcome, the original prefix
is reconstructed by inserting the unique silent responses in their original
slots. Hence it has at most 48 preimages, the number of original chance
outcomes. A chance atom with \(k\) good bits has mass \(9^k/6000\), whereas
the constructed all-good atom has mass \(729/6000\). Retained response
factors agree, and deleted WAIT factors are at most one. For every fully
mixed behavioral profile, summing gives

\[
 \Pr(I)\leq48\Pr(I\text{ at a rearranged all-good prefix}).
\]

The native history occupation factor is \(1/128\) for each prefix's unique
first-late callback, so it cancels even though hidden command indices differ.
The inequality therefore applies to the actual Bayes weights. Passing along
the consistency sequence gives assessed mass at least \(1/48\) to all-good
prefixes in which every earlier unsent owner's clock-2 slot produced a
packet. All other unsent owners still have their clock-2 slot ahead of them.
The pointwise timing result forces their packets there. EARLY packets are
included in the middle block. A current first packet consequently has
positive conditional probability of all original bindings being admitted.

The rearrangement and native Bayes bound are checked in
`Vegas.Examples.CommitSeedBroadcast.assessed_firstLate_regular_lower`.
The resulting all-admission continuation is checked in
`Vegas.Examples.CommitSeedBroadcast.regular_assessed_original_admission`;
it passes the full public build. This uses the actual assessed
continuation from each regular prefix, so a separate future-tremble limit
is unnecessary here. The observable-envelope classification is necessary: a
malformed rejected
marker cannot be treated as an admitted EARLY binding. The preparation and
initial-incentive arguments below use this positive no-reset mass, rather
than identifying the all-good posterior bound with no-reset probability.

The later clock-3 input needs a different argument, since the owner's
remembered clock-2 WAIT cannot be removed. In fact an arbitrary counted
clock-3 fiber can force a foreign original miss: a foreign bad owner might
have sent at 2, leaving the same ineligible packet pending in both the
remembered clock-2 view and the current view. Usable preparation need not be
strictly optimal there, since the reset will erase it. The claim needed here
concerns clock-3 inputs reached by the limiting continuation after an EARLY
packet, whose earlier timing responses have already been determined.

Fix the public envelope word \(P\) from the three initial callbacks. Its
probability \(c_n(P)>0\) in a fully mixed consistency profile sums over the
hidden preparations and evidence aliases producing those same envelopes.
At the relevant clock-3 input this word is identifiable: the remembered bad
clock-2 before-view contains the complete middle ledger, after all EARLY
inclusions and before any late inclusion. Its envelopes determine \(P\) in
the fixed initial owner order. The full information fiber therefore has the
same \(P\); competing probabilities of different initial words are not mixed.
Every alias of a valid first fresh owned envelope is count-permitted; this
permission reads the envelope, not its hidden preparation. Before original
admission finishes, the unsent owners' complete inputs depend on \(P\) and
the subsequent public traffic, independently of those hidden helper choices.
A helper's private binding value is not yet published. Its possible clock-2
callback has already used its one packet, so the audit forces WAIT there.

Finiteness makes convergence to this WAIT law uniform over helper inputs.
Conditional on \(P\), the original-stage law therefore differs by a vanishing
error from the law which forces these helper callbacks to WAIT. That latter
law is independent of hidden helper preparations and converges to the
actual limiting continuation after \(P\). For every input \(I\) in its
support, its conditional mass tends to some \(\alpha(I)>0\), while the mass
of earlier timing errors tends to zero. Dividing the joint weights cancels
the common \(c_n(P)\), even if the initial EARLY word itself becomes rare.
Its assessed beliefs are consequently supported on timing-correct histories.
All original bindings are admitted on those helper histories, so the relevant
clock-3 preparation comparison has no-reset probability one. This public-word
likelihood cancellation also remains to be mechanized. It does not assert
that every off-path clock-3 belief discards earlier mistakes.

Replace an unusable current preparation by the canonical fresh proper packet
and use a proper continuation. The handle may change, so opponents may change
their subsequent hidden preparations. Freshness follows from the owner's
literal unsent past. At an empty-ledger clock-2 input, condition first on a
particular compatible physical prefix and original seed. If the focal seed
is bad, both current packets miss original admission and pay \(-F\).

If the focal seed is good, its callback precedes the middle inclusion block
and all bad owners' clock-2 callbacks. Earlier good owners' admission is fixed
by their retained packets; an earlier mistaken WAIT remains a miss under
both deviations. Future good owners transmit at 2 unless they already sent
EARLY. Future bad owners transmit at 2 without a helper, and wait for 3 with
a helper. The two deviations retain the same initial EARLY word and earlier
responses. Thus they give the same foreign original-miss indicator under
each seed, despite possibly different later preparations. This statement
allows earlier off-path timing errors; it does not identify every compatible
prefix with a play that followed the timing rules from the beginning.
At the relevant helper clock-3 inputs, the public-word argument above removes
those earlier errors, so all originals are admitted there.

On an own original miss both choices
pay \(-F\). If a foreign original binding misses while this owner is
admitted, the actual reset permanently excludes a foreign owner. Proper
retry and publication then give this owner payoff 1, the absolute ceiling;
there is no need to reproduce the bad action's private remembered word.
On the no-reset branch, the unusable binding stands and pays \(-F\),
whereas the proper continuation gives at least 0. The positive all-admitted
mass makes this comparison strict: the first-late lower bound alone gives
a gain of at least \(F/48=1/32\). Consequently unusable preparations are
unsupported at the relevant inputs. This ceiling argument also covers a
reset leaving two survivors.

The same checked comparison applies to every initial EARLY response,
including EARLY responses by owners other than the one whose incentive is
being evaluated. The timing result with a helper was proved independently
of preparation: all original bindings are admitted, so no reset can erase
an unusable EARLY binding. Sending a canonical fresh proper EARLY packet
and taking a proper tail gives at least 0. Changing that envelope may change
later initial responses, but a helper still exists and all bindings are admitted;
the unusable EARLY choice gives \(-F\). It is therefore strictly excluded
from support. Together with the late-preparation comparison, this makes
all other owners survive after an EARLY packet. Merely proving that the
current EARLY sender has a proper alternative would not establish its
payoff upper bound if another EARLY sender could retain a bad preparation.

Once successful stored bindings enter the protected publication suffix,
withholding at the sole usable publication opportunity gives \(-F\),
whereas a truthful opening guarantees survival. Actual sequential
optimality therefore gives successful publications there. No assumption
that an optional-opening posterior is uninformative is involved.

## Initial incentives and backward induction

At an initial callback after a quiet prefix, consider any nonsilent
count-permitted response, including an arbitrary private preparation and
evidence request. Its EARLY packet supplies the middle helper. The timing
and preparation arguments above make every other owner survive. A usable
EARLY binding therefore gives its sender 0; an unusable one gives
\(-F\). Thus every EARLY response has continuation value at most 0.
The argument also applies when other owners had previously sent EARLY.

Now fix an owner and make its initial response WAIT, with all initial
responses quiet. Use its proper clock-2 first packet and proper tail.
Original admission of every other owner is its independent good bit,
regardless of hidden preparations. The focal owner survives on its own
good bit. If any foreign original binding misses, that foreign owner is
permanently excluded and its final publication fails. The focal deviation
therefore has value at least

\[
 q(1-q^2)-\delta F
 =\frac9{10}\frac{19}{100}-\frac1{10}\frac32
 =\frac{21}{1000}>0.
\]

This lower bound does not require the opponents' whole continuation to be
proper. Their first-late timing is forced as above; the deviator itself
uses the protected proper retry and publication continuation. Additional
foreign publication failures can only increase its reward.

Apply this first to Carol's initial callback after Alice and Bob WAIT.
WAIT has strictly positive value; every EARLY response has value at most
zero. Carol therefore WAITs. Next, at Bob's callback after Alice WAIT,
Bob's WAIT reaches precisely that quiet Carol input, so the same strict
comparison forces Bob to WAIT. Finally Alice's initial WAIT reaches those
two prescribed WAITs, and the same comparison forces Alice to WAIT.

These initial quiet physical histories have no hidden earlier declaration:
the context is empty, earlier WAIT responses are unique, the initial
activation order is fixed, and no original seed has yet been read.
Their original seed posterior is the original product law. Perfect recall
and the full-fiber comparisons above justify the continuation claims also
when a quiet prefix is off path under the initially proposed assessment;
one does not replace its assessed beliefs by a deviation posterior.

Alice's equilibrium continuation value is consequently at least
\(21/1000\), by the same feasible unilateral continuation. Honest source
payoff is identically zero. The proposed three-player experiment therefore
obstructs preservation even with fixed exclusion loss strictly above the
whole nonexcluded payoff range. The remaining work is the concrete native
certificate and its full-fiber, service and continuation adapters; the
checked two-player theorem is not that certificate.
