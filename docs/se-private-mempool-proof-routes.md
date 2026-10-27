# Commit–reveal preservation through the ledger

The target is to preserve an intended commit–reveal game's sequential
equilibria in an idealized but realistic blockchain implementation. Recovery,
rollback, penalties, and the larger source game accounting for silence are
implementation and proof choices. They are not the specification to preserve.
The preserved object remains the joint law of original inputs, complete typed
terminal state, public result, and realized net payoffs, without on-path
exclusions or charges.

The [registered-service implementation](se-publication-end-to-end.md) gives
the full finite mathematical construction for one explicit public transport
calendar. It derives historical authorization, observable replay, automatic
ledger audit and funded settlement. The broader padded theorem below uses
the existing runtime interfaces; its statement should not be read as already
implementing those interfaces for arbitrary blockchains.

There is no established impossibility of this target from private mempool
observations. There is also no complete mathematical proof here for the current
concurrent runtime after deleting complete pending observation. Two specific
obstructions to proposed proofs can be established, and a modest compiler
alternative addresses the more concrete one:

* A late opening can remain private when the ledger enables another binding.
  Consequently the current global proposal archive is not always observable.
* Arbitrary rational continuation after a failure does not preserve the value
  of sending now versus waiting.
* A **publication barrier** can make earlier opening proposals public through
  actual ledger inclusion before another binding becomes available. It does
  not reveal still-pending transactions. This restores the archive needed by
  the prescribed source-based continuation, avoiding arbitrary continuation
  selection as the proposed fix.

The barrier can be implemented mathematically by inserting deterministic public
sample instructions, which the existing reserved scheduler executes at most
once per cycle. The finite preservation theorem below composes that padding
with the existing complete-observation counted construction, a causal
private-observation transfer, and the existing raw audit extension. It retains
individual failure rules and concurrent commitment blocks.

This is a hand proof for a proposed padded compiler, not a theorem for the
unchanged immediate-transition compiler. The compiler transformation and
probability adapters have not been implemented or checked in Lean. No
checklist closure is asserted. The
[foundations](se-private-mempool-mathematics.md) and
[compiler analysis](se-private-mempool-compilation.md) contain the general
consistency, completion, and incentive results used here.

The detailed mathematical specification is divided by proof obligation:

| Document | Derived content |
| --- | --- |
| [Source padding and assembly](se-publication-padding-mathematics.md) | Exact instruction/context maps, source beliefs and gains, expanded resource bounds, cycle inequalities, archive equality and final joint-law composition. |
| [Finite private-observation transfer](se-publication-transfer-mathematics.md) | Fixed games and dependent menus, causal reach factorization, actual Bayesian mixtures, every literal one-step deviation and one common consistency sequence. |
| [Native counted adapter](se-publication-native-adapter.md) | Exhaustive action classes, candidate masking, controlled transitions, all-index reference probabilities, private own memory and ordered-pending reconstruction. |
| [Audit and delayed authorization](se-publication-audit-boundary.md) | Conditional evidence coverage, a possible publication/audit tail, excluded-owner disclosure extensions, and the boundary with retained signatures and replay. |

For the concrete end-to-end instance, the
[authorization specification](se-publication-authorization.md),
[registered transport proof](se-publication-end-to-end-review.md), and
[audit implementation](se-publication-audit-implementation.md) discharge those
backend obligations. The public-calendar specialization is explicit. A single
localized equilibrium extension combines the active-player penalty bound with
the excluded-player direct payoff bound.

These derivations expose two separate service requirements. Publication before
the next commitment makes the counted source query available. Collection of
authentic evidence makes the raw-action extension valid. The first does not
imply the second. The current finite model supplies a conditional theorem under
its stated audit interface; a backend must implement that interface, including
traffic from the final gameplay callbacks. Previously signed but unbroadcast
transactions also require the separate authorization adapter described above.

## What private observations actually obstruct

The phase normalizer retries a **commitment** phase when it contains a fresh
exclusion. It does not reopen that commitment phase after a reveal failure.
See [PhaseApplication](../Vegas/Pending/PhaseApplication.lean), particularly
`Vegas.EventGraphRuntime.PhaseRuntimeState.settle`.
Thus an allowed opening does not ordinarily let a player choose that same
phase's commitment again. Extra raw disclosures require the separate audit
analysis; they cannot be treated as harmless private noise.

The observation rule takes an observer and the actual pending list. If two
executions have the identical pending list, they have the identical reception
kernel, even when that rule examines packet contents. Couple them by taking
the same actual reception draw. If its probability is \(p\), both paths acquire
the factor \(p\); it need not be one. Multiply these factors along a finite
history and sum over reception histories the observer did not see.

This replaces deterministic replay with probability-preserving replay. It
does not reconstruct an unseen opening or make its contents common knowledge.
The owning implementation already provides
`Vegas.EventGraphRuntime.BindingShadow.activation_external_coupling` in
[PhaseProposalShadowActivation](../Vegas/Pending/PhaseProposalShadowActivation.lean).
Its marginals are the original activation laws. The associated
[environment coupling](../Vegas/Pending/PhaseProposalShadowEnvironment.lean)
also retains actual chance probabilities.

Before the first public exclusion, a regular binding callback has a useful
property: earlier successful openings are already in its source-public history,
and current commitments carry opaque handles. For a reference profile with
value-independent waiting and handle selection, pair the same complete
operational word across source histories having the same source information
\(J\). Every reception factor is then common across that fiber. If \(x\) is a
source history and \(m\) a compatible operational word, its weight has the form

\[
                 w_n(x)\,q_n(m,J).
\]

Summing operational words consistent with the actual native information \(I\)
gives a factor depending on \(I,J\), not on the hidden source history \(x\).
Bayes normalization therefore retains the source posterior at \(J\).
This is a likelihood statement for that reference profile, not a proof that
waiting with those probabilities is optimal.

There are concrete producers for its premises:

* [PhaseForeignTraffic](../Vegas/Pending/PhaseForeignTraffic.lean) preserves the
  entire focal traffic when a foreign typed binding value changes at the same
  physical handle. It retains the network, scheduler recall and focal recall.
* [PhaseBindingSlotHistory](../Vegas/Pending/PhaseBindingSlotHistory.lean)
  identifies the actual eligible handle set with the physically fresh bounded
  handles. The canonical policy samples a handle before the typed result.
* [PhaseProposalResponseAliases](../Vegas/Pending/PhaseProposalResponseAliases.lean)
  preserves the selected response-class law when splitting its mass among
  literal private aliases. It does not make all aliases identical private states.
* [SourcePhaseInitialNoise](../Vegas/Game/SourcePhaseInitialNoise.lean) retains
  the actual joint input law. None of this requires independent private types:
  source-history weights retain that joint prior rather than resampling private
  coordinates independently.

Pre-sampling an owner's current commitment-block word is a proof device for
physical reordering. Within such a block there is no new external source
observation; guards read public information and the author's own earlier
commitments. Chain multiplication reproduces the original behavioral law.
Unused private draws integrate to one. This does not allow commitments to
cross a reveal or public-sampling barrier.

## A concrete failure of global archive reconstruction

Consider an initial hidden committed bit owned by A. The program first opens
it, then lets C make a new commitment. Let C's pending-observation rule return
nothing. Give the events deadline 7, activate every owner in every cycle, and
disable processing only in cycles congruent to 7 or 8 modulo 10. Processing
occurs before activations; expiry checks follow them. The activation gap is 1,
the processing gap is 3, and the conservative timely margin is
\(1+3+2=6<7\).

A waits in cycles 0 through 5, then sends its first authentic opening in cycle
6. It has missed that cycle's processing prefix. Cycle 7 has no processing, so
expiry excludes A. Cycle 8 has no processing either; C can receive its next
binding callback while A's opening remains pending. The opening is count clean:
it was sent while ready, uses the authentic token and accepted binding, and is
the first packet for that event. A skipped the protected early opportunity, so
this does not violate the service guarantee.

For the two possible bit values, C has the same actual information, while the
global submitted proposal archive contains different opening values. No
function of C's actual information returns that global archive in both cases.
This is an information obstruction to the decoder. It does **not** show that
every native SE changes an intended equilibrium's outcome law.

The relevant definitions are in
[PhaseProposalArchive](../Vegas/Pending/PhaseProposalArchive.lean) and
[PhaseProposalObservation](../Vegas/Pending/PhaseProposalObservation.lean).
The archive contains submitted opening claims, including failed and stale
ones. Its reconstruction theorem currently uses complete pending observation.
In [PhaseProposalQuery](../Vegas/Game/PhaseProposalQuery.lean), the source
control component already has a genuine-source theorem without that assumption;
the displayed complete-observation use supplies the archive equality.

## Bad commitments admit a more precise comparison

An unusable commitment does not immediately fix its owner's final payoff. A
different owner's failure can roll the commitment phase back before the bad
binding is saved. A useful comparison therefore stops at the phase boundary.

At an actual information set \(I\), suppose the owner's source context is
intended and its observation is \(J\). Choose a guard-admitted replacement \(g\)
for its first bad binding \(b\), at the same event, handle and send time.
Well-formedness supplies an admitted value at an intended source history;
the guard depends only on the owner's observation. An arbitrary typed value
is insufficient. In particular, the existing typed replacement by an arbitrary
inhabitant is not yet this source-admitted replacement.

While the commitment phase is unsaved, the physical commitment packets agree.
No opening of its new bindings is phase authorized. The two worlds can retain
the same network, foreign observations, scheduler history and chance draws.
There are three endpoints:

1. If the bad owner is excluded, its base payoff is its floor \(F_i\).
2. If the bad binding is saved, its source obligation becomes persistent failure
   debt. The saved-checkpoint debt theorem forces the same final floor even
   through later foreign failures. A clean good-side continuation pays at least
   \(F_i\).
3. If a foreign failure rolls back the unsaved block, its active semantic
   difference disappears. Its private candidate memory and recall do not
   disappear and must still be simulated.

The existing [saved-debt machinery](../Vegas/Game/PhaseProposalSavedDebt.lean)
persists through arbitrary raw transitions. The source departure lemma is
`Vegas.SourceProgram.ProtocolState.owesFailure_of_deviation` in
[FailedBindingDeviation](../Vegas/Source/FailedBindingDeviation.lean).
Connecting that source obligation to the first newly saved physical checkpoint
is a specific remaining adapter.

The rollback branch has a causal implementation. Keep a private table of the
original candidate meanings indexed by handle, and the original virtual own
observations and responses. At a callback, the current accepted-handle map
identifies the active own binding fields. Substitute the remembered original
meaning only for fields currently associated with those handles. A retired
handle stays in private memory but no longer overrides an active field.
This avoids reconstructing a hidden saved checkpoint or observing every
intermediate scheduler transition.

The controller uses only its owner's information and private randomization.
Perfect-recall behavioralization turns it into an ordinary legal continuation.
[ReactiveBindingShadow](../Vegas/Pending/ReactiveBindingShadow.lean) already
implements virtual own recall in the nonphase API;
[PhaseProposalShadowNormalization](../Vegas/Pending/PhaseProposalShadowNormalization.lean)
provides frames through real retries, exclusions and retired archives.
The initialized [history repair](../Vegas/Pending/PhaseProposalShadowHistory.lean)
is stronger than a clean-attempt argument, but an existential history repair
alone is not a policy-transport theorem.

The crucial provenance invariant is precise. A freshly repaired handle has no
previous authentic opening certificate. Count-clean commitment-phase traffic
cannot issue one. After rollback, a count-clean opening cannot name a retired
handle as the current surviving binding; freshness prevents reusing it.
Foreign players cannot issue that owner's certificate and can only forward
evidence already available. This gives a route to retaining arbitrary foreign
policies while restricting the focal continuation to count-clean actions.
Its full acceptance-and-rejection induction remains to be assembled.

Under those causal and provenance identities, for every count-clean bad continuation
\(\tau_b\) there is a good continuation \(\tau_g\) with
\[
               V_i(b,\tau_b\mid I)\le V_i(g,\tau_g\mid I).
\]
To compare against the *prescribed* continuation, use the downstream-regret
lemma from the [compiler analysis](se-private-mempool-compilation.md):
if later own local regrets are at most \(\eta\), and at most \(H_i\) own
decisions remain, then
\[
       V_i(b,\sigma\mid I)-V_i(g,\sigma\mid I)\le H_i\eta.
\]
This argument retains actual Bayes beliefs and uses backward induction. It
does not assume that a fully mixed profile has no future audit mistakes.

## Why arbitrary post-failure completion does not settle waiting

Sending now and waiting do not have the same physical trace. They can produce
different inclusion times, rollback times, raw ledger records and future tape
posteriors. The private-value shadow comparison does not erase these differences.

A small continuation example isolates the problem. Let a foreign owner B be
about to miss its deadline. A can send now and finish the failed commitment
attempt at clock 7, or wait and finish it at clock 8 while still surviving.
After rollback, A and C have a coordination game: both choosing 0 pays each 0;
both choosing 1 pays each 1; mismatches pay each \(-1\). Both coordinated
profiles are equilibria. A rational continuation may select the first after
clock 7 and the second after clock 8. Waiting then gains 1.

The timing pattern is compatible with reserved service: activate B before A
each cycle, process every cycle, give B deadline 7 and A deadline 10, and
consider A's callback at clock 6. Send at 6 is included at 7; Send at 7 is
included at 8. B's expiry at 7 occurs after the processing prefix. This is a
counterexample to **arbitrary** completion as the wait argument. It is not a
preservation counterexample: choosing the same coordination equilibrium at
both continuation histories removes the incentive.

The current
`Vegas.phaseProposal_unflagged_wait_finish_le` in
[PhaseProposalCleanBindingGain](../Vegas/Game/PhaseProposalCleanBindingGain.lean)
handles earlier waits; it does not equate waiting with irreversible silence.
It compares specified source-query continuations. Its rollback branch uses
the reset payoff-law equality in
[PhaseProposalOriginalResetPayoff](../Vegas/Game/PhaseProposalOriginalResetPayoff.lean).
Replacing those continuations with arbitrary equilibria loses that equality.
The missing result for the unchanged compiler is compatible continuation
selection or an equally strong direct delay comparison.

## A publication barrier supplied by the ledger

The compiler can instead prevent a later binding decision from overtaking
earlier opening publication.

At the end of a reveal block, close its permitted submissions. Before installing
the next commitment block, wait through enough reserved processing service to
record every previously submitted opening. Apply the same rule at recovery
transitions that would enable a new binding. Only then start the new block's
readiness and deadlines.

**Where the waiting interval starts.** Let \(D\) be the actual public clock
when the ledger closes the reveal block: every event in that block has either
been accepted or expired. The interval is measured from \(D\), not from an
honest player's first submission, the last packet someone happened to observe,
or a guessed empty-mempool time. If the service records every already-submitted
packet within a bound \(\Delta\), the next binding is enabled only after the
corresponding \(D+\Delta\) bound, with the scheduler's discrete-slot margin.
Individual reveal acceptance deadlines remain unchanged.

For example, suppose the block closes at clock 100 and the recording bound is
5 cycles. An opening submitted at 99 might be included in time and accepted,
or included at 103 after its event expired. In the latter case the owner still
suffers the specified failure; the packet's data becomes public before the
next binding. Recording a rejected message does not resurrect its opening.
Sending closer to the acceptance deadline is therefore still a deviation with
its actual success probability. The padding argument does not assume that
probability is zero or that every late send fails.

This argument needs bounded **recording**, including stale packets, rather
than just a positive or high probability of inclusion. If inclusion delay has
an unbounded tail, no fixed cooldown establishes the exact archive equality.
The current reserved service supplies the stronger bounded-recording property;
an ordinary probabilistic mempool guarantee does not.

Fresh broadcasts after closure remain possible as raw deviations. They can
arrive after the publication interval, so the cleanup lemma does not cover
them. The existing model classifies their newly emitted old-phase calls as
count forbidden and uses the funded audit extension. This relies on the actual
emission interface: it attaches the current attempt and masks out-of-phase
authorization before the packet enters the network. A concrete blockchain
adapter must justify that interface or account for an old signed message
withheld until after closure. An inclusion timestamp alone cannot certify
when a sender first broadcast a message. The finite model theorem does not
itself implement such an authorization or audit mechanism.

This is an application-visible phase rule. It must not install the next binding
early and merely hope players refrain from acting. Callbacks may continue
during the interval; with no ready source event, the counted effective action
is silence. Arbitrary raw alternatives remain subject to the ordinary audit
analysis. The interval ends by a public clock rule justified by the service
bound, rather than by treating the scheduler's private claim of an empty pool
as public evidence.

**Cleanup lemma.** Suppose no further count-clean opening from the closed block
can be emitted, pending traffic is retained until processing, and a subsequent
processing prefix can include every envelope pending at its start. All opening
proposals from the closed block are in the ledger after that prefix.

Proof: each earlier envelope is already ledgered or remains pending. Processing
appends the entire pending prefix to the ledger, whether the application
accepts or rejects each envelope. There are no interleaved player responses
inside that processing prefix. Ledger persistence proves the claim afterward.

This is already the exact conclusion of
`Vegas.EventGraphRuntime.ReservedEpoch.full_processing_epoch_clears` in
[ReservedEpochEmptyProcessing](../Vegas/Pending/ReservedEpochEmptyProcessing.lean):
\[
 P_{\mathrm{after}}=\varnothing,\qquad
 L_{\mathrm{after}}=L_{\mathrm{before}}\,{+\!\!+}\,P_{\mathrm{before}}.
\]
It also supplies a receipt for every included envelope without assuming semantic
acceptance. The actual reserved scheduler allocates a full-capacity processing
batch; it is not a one-packet queue where an earlier insertion necessarily
displaces a late foreign packet to another cycle.

The bounded-gap result in
[ReservedEpochArrival](../Vegas/Pending/ReservedEpochArrival.lean) supplies
the next processing epoch. A conservative cooldown ends at clock \(c'\) with
\(c+\text{processingGap}+1<c'\), where \(c\) is the closing clock.
The horizon, tape coverage, packet budget and candidate reserve must be
recomputed for the extra cycles. Their old numerical bounds cannot simply
be reused.

**Decision-site archive lemma.** On a counted history obeying this barrier,
the observed proposal archive equals the submitted proposal archive at every
binding callback, for every pending-observation rule.

Proof: every earlier submitted opening is ledgered by cleanup. The only new
count-clean messages during the commitment block are opaque commitments, which
add no opening proposal. Own recall and private receipts contain only genuinely
submitted envelopes. Taking the set of typed opening proposals therefore
gives both inclusions. This remains true when a commitment block retries:
its canceled commitments add no new opening proposal.

This is weaker than recovering every pending message, and sufficient for the
archive component of the actual source query. The opening bit in the preceding
counterexample becomes public because its envelope is included before C's
binding, even though A has already been excluded.

The lemma is intentionally about **counted histories**. A raw player can send a
new forbidden opening immediately before a binding callback; that payload need
not yet be public. The proposal archive records even such claims. Hence a
single phase barrier does not prove the existing all-raw decoder theorem.
The counted-reference construction and raw audit extension must be separated.

## What the barrier buys for probability and incentives

For the proper, unflagged reference, the effective response law ignores
passive private receipts once the archive lemma holds:

* Binding dispatch reads the public request and the genuine source query.
  The waiting probability is fixed, and fresh-handle selection precedes the
  typed source draw.
* Opening dispatch uses the owner's actual stored value and accepted handle.
  The genuine-history opening theorem removes the apparent menu-dependent
  availability test.
* Reception changes the player's retained knowledge, but not the public network
  view or scheduler recall.

Keep the physical application, pending and ledger lists, message serials,
receipts, scheduler tape and cursor, and effective own response history.
Sum out passive reception draws. Each discarded probability kernel sums to
one, and the next effective action kernel is unchanged. Induction on the finite
runner therefore gives the same projected physical and payoff laws for the
specified reference under arbitrary and complete reception.

This establishes an ordinary stochastic projection for the proper reference;
it does **not** identify actual native information sets with complete ones.
For conditional incentives, pair literal operational words within the source
information fiber as above, or use a causal simulation of private reception
inside the complete-observation reference. A common consistency sequence and
legal native deviations are essential; equality of initialized outcome laws
alone is insufficient.

There are two concrete alias obligations. The totalization of response classes
must be inactive at genuine counted source queries. Also an unusable preparation
with missing bytes and one with wrongly typed bytes can have the same response
class but different private candidate catalogues. The class pushforward theorem
does not equate those catalogues. A private-memory simulation, or the separate
bad-binding comparison, must justify this case. Successful typed preparations
retain their actual typed values.

The following two arguments strengthen this proper-reference calculation:
a typed-candidate mask handles the full counted sequence, and causal garbling
transfers actual conditional gains. Deterministic source padding then supplies
the barrier without changing the runtime state machine or reproving its
complete-observation waiting comparison.

## A counted candidate mask preserves private memory correctly

Associate each prepared handle permanently with the event and declared type
of its first signed commitment. Count cleanliness prevents rebinding that
handle, including after rollback. Keep initial candidates exactly. For other
handles, keep freshness and successful decoding at that declared type; replace
every nondecoding raw preparation by one unusable symbol.

The projected transition induction has five cases.

1. A commitment has the same handle, event and no emitted evidence. Its class
   retains exactly the successful typed value or records failure. Both sides
   freeze the handle, so fresh-slot sets agree.
2. A count-clean opening must use the current surviving accepted handle and its
   successful value of the declared type. That value is retained exactly.
   An unusable binding has no counted opening, while a voided handle cannot be
   opened as the surviving binding of another attempt.
3. An unusable candidate's additional raw certificate capability cannot appear
   in counted traffic. Commitment evidence is absent; an opening certificate
   must match its own legitimate call and accepted value. Other players cannot
   issue that owner's evidence.
4. Inclusion, expiry, samples and rollback read the retained typed data, public
   readiness, accepted handles and checkpoints. Their projected transitions,
   receipts, exclusions, ledger entries and clocks consequently agree.
5. The reference query reads the typed source view and public proposal archive.
   It does not inspect the discarded raw candidate bytes. Fresh-slot selection
   and effective response menus agree. After genuine class coverage removes
   totalization, the selected class laws agree at every positive perturbation
   index, and the alias probabilities sum to one within each class.

The fifth point concerns the actual virtual-source query in
[PhaseVirtualBindingView](../Vegas/Game/PhaseVirtualBindingView.lean), not an
arbitrary decoder. The old surviving-view decoder has different dependencies.
The genuine coverage results for the reference are in
[PhaseProposalGenuineSupport](../Vegas/Game/PhaseProposalGenuineSupport.lean);
the barrier supplies their missing archive equality.

Nothing makes the owner forget its bytes. Its unmasked candidate catalogue is
reconstructible from its initial own catalogue and literal past own preparation
actions. Registration freezes immediately; rollback retains the catalogue;
foreign counted actions do not change it. Together with literal own recall,
this is causal private memory, not additional hidden information from Nature.
An arbitrary counted one-step alternative also obeys the same transition
classification; the prescribed continuation then uses the common class policy.

This gives an exact masked transition and payoff comparison for the counted
reference, including failed-preparation aliases. It is not a claim that
arbitrary unmasked policies ignore their private memory. Nor does it allow a
raw packet to expose an otherwise inaccessible certificate: raw alternatives
belong to the subsequent audit extension.

## Conditional gains under causally simulated private reception

Here is a finite transfer theorem. It concerns the entire perturbation sequence,
not just a limiting strategy that happens to ignore extra observations.

Let the physical tree, literal action menus and observation alphabets be finite,
with perfect recall. Fine information \(F\) permits reconstructing the actual
observation kernel's argument at each past own callback. Coarse information
\(I\) retains a causal private channel's outputs and all literal own actions.
The channel may use earlier private outputs but its fresh coins supply no
additional dependence on the hidden physical state.

For every sequence index \(n\), require:

* A statistic \(T\), available from both \(F\) and \(I\), determines the same
  finite effective menu and full-support class policy \(b_n(T)\).
* Each literal menu maps onto that effective menu. After choosing class \(c\),
  a full-support private kernel \(q_n(a\mid c,I)\) selects its literal alias.
* Projected transitions, payoffs, future reference class laws and ordinary
  observations agree under the class map, including after any one-step
  alternative. Discarded private alias observations are causally reconstructible
  from fine history, the private transcript and own alias coins. The candidate
  mask above is a concrete instance of this condition.
* Every fine information set and effective alternative has local gain at most
  \(\epsilon_n\), where \(\epsilon_n\to0\).

Then the actual coarse literal profile is fully mixed and every local gain is
at most \(\epsilon_n\). A common convergent subsequence of its strategies and
Bayes beliefs is a coarse SE, with the same projected terminal-law limit.

**Proof.** Couple initial draws, physical chance and selected classes. Generate
actual receptions and aliases by their causal private kernels. The transition
condition gives the fine physical history law after summing those private
draws. Fix \(I\), a compatible fine information set \(F\), and a hidden fine
history \(h\in F\). Multiplication of the actor's remembered channel and alias
factors gives \(K_n(I\mid F)\). Perfect recall recovers every earlier argument
from \(F,I\), so the factor is constant over \(h\in F\). Other players' private
factors sum to one because their full future class policies are common.
Therefore
\[
 \Pr_n(h,F,I)=\Pr_n^{\mathrm{fine}}(h,F)K_n(I\mid F),
 \qquad
 \Pr_n(h\mid F,I)=\Pr_n^{\mathrm{fine}}(h\mid F).
\]
For a fixed literal alternative \(a\) at \(I\), its class \(c\) is legal at
every compatible \(F\). The forced-action transition condition and common
prescribed continuation yield
\[
 G_n^{\mathrm{private}}(I,a)
   =\sum_F\Pr_n(F\mid I)G_n^{\mathrm{fine}}(F,c)
   \le\epsilon_n.
\]
Thus the posterior mixture controls actual deviations, not just outcome
marginals. Full support follows from the positive class and alias kernels.
Finite compactness gives simultaneous convergence of strategies and Bayes
beliefs. Continuity of local gains and perfect recall give sequential
rationality; the same fully mixed sequence gives consistency. The projected
law identity also passes to the limit.

**The fine observer really can simulate the present observation API.**
An observation rule may depend on the order of the pending list, so set
reconstruction alone would be insufficient. Complete own recall reconstructs
the ordered list as follows. In chronological order, append the new foreign
leaked suffix just before each own action, then its own emitted envelope.
Append the current new leaked suffix. This list has submission order: a
foreign packet pending before an own action was learned at that action's
complete activation; one first learned later cannot have been delivered
earlier and then requeued. Filter out identifiers already in the current
ledger. Unique identifiers, append-only submission and removal without
reordering make the result exactly the current ordered pending list.

Sampling the arbitrary reception kernel on this reconstructed list, then
applying the actual learning filter to a private simulated recall, generates
the actual coarse channel. The coarse player is never given the reconstructed
fine list. This argument uses the current stateless observation API. Hidden,
stateful gossip requires a separate joint-state simulation; finite branching
alone does not supply it.

## A padded compiler with a finite preservation proof

The publication interval can be expressed using existing source instructions.
Let \(p\) be the reserved processing-gap bound. Insert \(p+2\) deterministic
public samples after each maximal reveal block that has a later commitment
block. Give them fresh names and ignore their results in all original guards,
distributions, outputs and utilities. Keep each original commitment block
intact. An equivalent placement is immediately before the next commitment
block, after any intervening original public instructions.

This transformation requires constant distribution syntax and weakening into
the enlarged contexts. The abstract expression interface does not supply these
operations merely by supplying inhabited values. The concrete
[Simple expression language](../Vegas/Expr/Simple.lean) supports a rational
point mass at its existing Boolean type; ordinary structural weakening gives
the context embedding. No new unit type is needed. A generic compiler theorem
must name this expression-language capability.

**Timing.** Suppose the last reveal closes at cycle \(c\). Every sample is its
own phase. Excluded-owner draining cannot perform it, expiry cannot perform it,
and the reserved scheduler has exactly one sample slot per cycle, after owner
activations. Even if the first sample executes in cycle \(c\), the last cannot
execute before \(c+p+1\); a new binding callback cannot occur before \(c+p+2\).
At least one full processing epoch after closure precedes that callback.
The next binding's readiness and deadline begin only after the sample barriers.

These facts come from
[RuntimePhase](../Vegas/Pending/RuntimePhase.lean),
[ExclusionCompletion](../Vegas/Pending/ExclusionCompletion.lean),
[ReservedEpochScheduler](../Vegas/Pending/ReservedEpochScheduler.lean) and
[ReservedEpochSampleProgress](../Vegas/Pending/ReservedEpochSampleProgress.lean).
The samples remain compulsory even when every owner is excluded. Commitment
retries add no opening proposals, so they need no extra padding internally.

**Source equilibrium.** Erase the inserted deterministic chance steps and
fresh unused cells. Original decision histories, information and action menus
correspond bijectively. Every new chance factor is one; the insertion positions
are determined by the original straight-line program, so the padding discloses
no hidden control branch. Lift the original fully mixed consistency sequence
through this correspondence. Its reach weights, Bayes ratios and deviation
gains are unchanged. Thus every intended source SE has an SE of the padded
source with exactly the original joint law after erasing the fresh cells.

**Finite preservation theorem.** Fix a finite intended source game satisfying
the existing well-formedness and initial-value assumptions, with the constant
sample/context-embedding capability just described. Apply this padding, then
the existing concurrent compiler and individual-exclusion payoff rule.
Instantiate the reserved service, finite message bounds, timely deadlines,
candidate reserve and funded authentic count audit for the **expanded**
program. Retain the existing bounded utility and exclusion-floor hypotheses.
The reserved tape is sampled separately from the source initial draw, as in
the existing construction. Correlations among players' initial inputs and
among the tape's coordinates are allowed; arbitrary source–tape correlation
is not an added conclusion.
For any observation rule in the current finite pending-observation API, every
intended source SE has a native raw SE preserving the original initialized joint
law, after erasing the padding cells, with no on-path exclusion or audit charge.

The theorem is a modular hand proof:

1. Lift the source SE through the deterministic padding.
2. Apply the existing **complete-observation counted construction** to this
   padded source. It is still an ordinary source program, so its waiting and
   rollback proofs apply without changing the runtime state machine.
3. Use cleanup to recover the complete proposal archive at every counted
   binding. The genuine source query and class-support arguments then show
   that the prescribed effective class law is available from actual private
   information at every positive perturbation index. The candidate mask
   supplies the full counted alias comparison.
4. Apply the causal-garbling theorem to that counted sequence. It gives a
   private-observation counted SE and the same initialized masked physical law,
   hence the same original outcome and payoff law.
5. Apply the existing raw audit extension **under the actual private observation
   rule**. It preserves the counted terminal-history and settlement laws and
   supplies zero on-path charges. Finally erase the padding cells.

Step 2 uses more than the existential capstone. The argument in
[ConcurrentRawEquilibrium](../Vegas/Game/ConcurrentRawEquilibrium.lean) constructs
fully mixed counted reference assessments and bounds each native local gain by
either a vanishing error or a source local gain plus that error. The finite
source assessments converge to a source SE. The largest positive source pure
local gain therefore tends to zero; mixed alternatives are convex combinations.
Adding the vanishing native error supplies the uniform \(\epsilon_n\) required
by step 4. Hence this is a transfer of the actual common sequence, not a
post-hoc coarsening of an arbitrary fine SE.

That original fine witness uses literal aliases. To obtain its effective-game
gain bound, condition on a masked fine information set and average over its
compatible literal fine information sets. For each class choose a legal literal
representative at each such information set. The mask gives the same prescribed
continuation law, so the effective gain is a convex combination of literal
gains and has the same uniform bound. This justifies the effective fine game
used in the transfer theorem.

For step 5,
`Vegas.EventGraphRuntime.PhaseCount.onePacket_raw_sequentialEquilibrium` in
[PhaseOnePacketExtension](../Vegas/Game/PhaseOnePacketExtension.lean) accepts
arbitrary leaks and any counted SE. Its hypotheses are finite nature, authentic
conditional evidence coverage, nonnegative delivery and deposit, bounded base
utility, and the deposit-spread inequality. It returns exact terminal-history
and randomized settlement laws. No complete-pending premise is needed there.
The raw extension is performed after the counted transfer; arbitrary raw
off-path strategies are not asserted to descend from the fine game.

The proof uses existing semantic rules and theorem constructions as mathematical
ingredients. The source transformation, ordered-pending readout, masked alias
quotient and controlled-garbling theorem have not been assembled in Lean.
Resource and well-formedness preservation also need compiler lemmas. These are
implementation and verification obligations; they must not be reported as
already checked. The theorem does not prove the unpadded compiler preserves SE.

The programmer still writes the original commit–reveal game. Deterministic
samples are an internal compilation and proof device. A concrete backend can
implement the corresponding pause as a public height gate; it need not expose
dummy variables to the programmer. Removing the pause as an optimization would
remove the proof's publication guarantee.

## Comparing the remaining design choices

| Choice | Mathematical benefit | Remaining cost or obstruction |
|---|---|---|
| Current immediate recovery, private reception | Retains current implementation; hidden-value couplings already available. | Late openings defeat the global archive decoder; native continuation selection must replace its use. |
| Publication barrier through deterministic sample padding | Finite hand preservation proof using actual ledger inclusion; retains concurrent commitments and individual failure rules. | Added latency, constant-sample compilation, and the existing guaranteed inclusion/audit assumptions; compiler and proof adapters remain unmechanized. |
| Fixed settlement time alone | Prevents choosing a different rollback clock by delaying. | Different raw records, private receipts, serials and posterior future service remain; not a continuation-equivalence theorem. |
| Keep accepted commitments and remove rollback | Makes an accepted bad binding harder to escape through foreign failure. | Survivor decisions after foreign failure can depend on retained values; deadline resets and timing still need analysis. No complete preservation proof follows. |
| Canonical handles or batched owner submissions | Reduces alias and ordering obligations. | Must account for every native alternative; does not publish a hidden late opening or settle delay incentives by itself. |
| Recoverable encryption / automatic opening | Removes a sender's later ability to withhold an accepted valid value. | Needs validity, release and availability assumptions, and a cryptographic representation theorem. |
| Global absorbing abort with floors | Removes survivor continuation selection. | Stronger changes to failure settlement and survivor liveness; refund-abort can be profitable. It is not forced by private mempools. |
| Turn-based implementation | Removes concurrent recovery interactions and has an existing theorem under its own assumptions. | Does not establish concurrent impossibility; its service, audit and observation premises still need to match the desired blockchain model. |

The publication proposal requires inclusion of the **data**, not successful
application of an expired opening. The current abstract ledger already retains
rejected envelopes. A concrete implementation could use an authenticated,
funded submission inbox whose transaction data remains on chain when its
game-level message is rejected. Merely waiting for a private relay, or assuming
an invalid transaction will eventually be mined, does not supply this property.

A deterministic cooldown requires a known inclusion bound for the admitted
traffic. Eventual delivery after an unknown stabilization time does not imply
such a bound for a chosen deadline. This distinction follows the synchrony
models of [Dwork, Lynch and Stockmeyer](https://groups.csail.mit.edu/tds/papers/Lynch/jacm88.pdf).
Their consensus theorem is not a transaction-inclusion guarantee.

### Compiler policy versus the service promise

An opening can be late for the game's acceptance deadline while remaining a
valid transaction for the publication service. The compiler can preserve this
distinction: record the authenticated opening data, then apply the game's
existing deadline and failure rules. A valid publication transaction need not
be a successful game action. The publication interval and delayed readiness of
the next commitment block are compiler choices.

The compiler cannot itself guarantee that a builder includes the transaction
within a known bound. That guarantee belongs to the service contract. If the
underlying contract already promises bounded recording of every admitted,
funded publication transaction, arranging for expired game openings to remain
in that admitted class uses the same service promise. It does not require a
separate exception for late game actions.

For the current reserved concurrent service, bounded full-batch processing
already records late and rejected envelopes. The padding therefore adds no
service hypothesis relative to that implementation. In contrast, the weaker
recovery contract permits its inclusion obligation to end when the event
completes; it does not imply later publication. Reusing it would require an
explicit transport-publication guarantee or a proved implementation of one.
Calling the late packet a publication transaction does not by itself derive
that guarantee from the existing game-event contract.

The cleanup invariant itself only needs the earlier admissible opening
payloads recorded before the next binding, not publication of every arbitrary
malformed packet. Full-batch flushing is the current sufficient producer.
A narrower producer must still account for capacity and interference from raw
traffic. Keeping a transaction admissible also does not resolve the separate
post-closure broadcast and old-authorization issue described above.

## What would justify an impossibility conclusion

A failure of archive reconstruction, a failure of arbitrary continuation
selection, or a counterexample to post-hoc information coarsening does not
refute intended-game implementation. A genuine refutation must fix an intended
SE and an admissible service/observation configuration, then rule out **every**
native SE with the required joint law.

The substantive boundaries remain:

* Without enough liveness, a finite-deadline compiler cannot guarantee the
  required successful law even when everyone follows its protocol. This is a
  delivery obstruction, independent of sequential rationality.
* If an implementation reveals a strategically useful value before a choice
  that the intended game keeps uninformed, and cannot prevent exploiting it,
  source incentives can fail. The commitment/reveal barriers rule out the
  simplest form of this attack in regular play.
* If an avoidable failure pays more than successful play, refunds can create a
  profitable deviation. The first-failing-player floor addresses a different
  problem from observation; it need not punish all survivors.
* With fees, time preferences, or other physical costs, inserting a publication
  interval can change payoffs. Those quantities must be part of the preserved
  utility or accounted for explicitly.

These are reasons to state and test the actual implementation contract, not
reasons to infer that concurrency with private mempools is impossible. The
most concrete implementation candidate is the sample-padded ledger publication
barrier. The unchanged
compiler remains a separate worthwhile target, with the continuation-selection
problem now isolated.
