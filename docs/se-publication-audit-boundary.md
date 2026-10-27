# Publication, audit, and delayed authorization

The finite preservation argument for the padded compiler has two distinct
boundaries. Its counted game obtains the required public information from actual
ledger inclusion. Its raw extension needs authentic, uniformly collectable
evidence against additional actions. Neither boundary follows merely from a
private mempool observation rule.

This document states the end-to-end hypotheses, verifies the source padding and
resource argument, and separates the present emission semantics from a model
allowing delayed broadcast of previously authorized messages. The mathematical
claims below are finite hand arguments using the linked owning results. They
are not new assembled Lean theorems.

## The preserved object and the padded source

Let P be a well-formed straight-line source program, with a finite supported
initial law and finite binding choices. Fix an intended sequential equilibrium
(sigma,mu). Its initial private inputs may be correlated. Preserve the joint law
of the original initial state, every original typed terminal cell, the original
public result, and the realized net payoff vector.

Let p be a uniform bound on the reserved tape's processing gaps. Insert p+2
deterministic public sample instructions after each maximal reveal block that
has a later commitment block. Give the samples fresh names, a constant
singleton distribution, and no references from original guards, distributions,
payoff expressions, or output readouts. Retain each original commitment block.
Call the resulting source P+ and let pi erase the fresh constant cells and
inserted deterministic steps.

The expression language must support this transformation. The generic `IExpr`
interface supplies inhabited values but neither a pure distribution constructor
nor arbitrary context embeddings. The concrete
[Simple language](../Vegas/Expr/Simple.lean) has weighted rational laws and an
existing Boolean type, so a constant Boolean sample suffices; structural
context weakening must be supplied. A theorem for arbitrary expression
interfaces must explicitly require these operations and their evaluation and
dependency-preservation laws.

For every original strategic history h, inserting the prescribed constant steps
gives one expanded strategic history h+. Projection is its inverse. This is
also an information-set correspondence: source positions are fixed by the
straight-line syntax, so the number and position of constant observations are
determined by information already present. There is no hidden control branch
whose length becomes newly visible. Legal source actions correspond exactly.

Lift a fully mixed consistency sequence sigma_n through that correspondence.
For every strategic h, the reach probability of h+ equals that of h: each extra
Nature factor is one. Thus the Bayes beliefs correspond, every one-step gain
is unchanged, and so is every continuation payoff through pi. The limit is an
intended SE of P+. This proves preservation of the initialized joint readout
after projection. Literal equality of terminal states with different typed
contexts is not asserted.

Source well-formedness is preserved because the original guard observations
and predictions are unchanged under pi, every old admitted value remains
admitted, and the new deterministic samples introduce no commitment obligation.
The original initial law is unchanged. No new binding type is introduced.
The static wire-value condition
`Vegas.EventGraphRuntime.MessageBounds.CoversOutputValues` in
[ReactiveFiniteCompiler](../Vegas/Pending/ReactiveFiniteCompiler.lean) explicitly
ignores public-data sample types.

## The actual cycle calculation

The relevant existing facts are structural:

* Every sample is a singleton runtime phase, including adjacent samples;
  see [RuntimePhase](../Vegas/Pending/RuntimePhase.lean).
* Automatic draining completes only an event owned by an excluded player;
  an ownerless sample cannot be drained. Expiry cannot execute it either.
  See [ExclusionCompletion](../Vegas/Pending/ExclusionCompletion.lean) and
  [PhaseCompletion](../Vegas/Pending/PhaseCompletion.lean).
* The reserved scheduler has one sample slot per cycle, after player activation
  slots and before expiry and clock advancement. See
  [ReservedEpochScheduler](../Vegas/Pending/ReservedEpochScheduler.lean).
* Samples are barriers in the compiled graph. The next commitment does not
  become structurally ready until the last padding sample completes; its
  readiness refresh and deadline therefore start afterward.

Suppose a reveal block closes at clock c. Its first padding sample can execute
as early as the sample slot of cycle c. At most one executes per cycle, so the
(p+2)-nd cannot execute before cycle c+p+1. That cycle's player activations have
already occurred. The first later binding callback is therefore at clock at
least c+p+2. Closure after the sample slot only makes the delay larger.

Every count-clean opening of the closed reveal block was emitted by c. For its
emission clock e and the next binding callback clock b,

    e + (p+1) <= c + (p+1) < c + (p+2) <= b.

Alternatively, start the bounded-next-processing-epoch argument at cycle c+1.
It produces an enabled processing cycle strictly before c+1+p. Its processing
prefix precedes all activations in that cycle. With enough packet capacity,
this prefix drains every envelope pending at its start, including rejected
and stale envelopes. The pending queue is retained rather than erased at a
source rollback. See
`Vegas.EventGraphRuntime.ReservedEpoch.full_processing_epoch_clears` in
[ReservedEpochEmptyProcessing](../Vegas/Pending/ReservedEpochEmptyProcessing.lean).

The result is genuine ledger publication. The network appends an envelope to
its ledger independently of the application's acceptance decision. It is not
necessary to accept an expired opening as a successful game action.

During the inserted sample phases, no owner has a phase-authorized source
request. The counted response is silence. Even if every owner is excluded,
the ownerless samples still execute one by one. Commitment retries afterward
add no new opening proposal, so they retain the established archive equality.

This proves that, at every counted binding callback, the set of all submitted
opening proposals equals the proposal set recoverable from the ledger and own
observations. It does not prove the corresponding all-raw assertion: a raw
player may send a new forbidden opening claim immediately before a binding
callback.

## Resource and environment hypotheses are for the expanded program

The scheduler and completion theorem are instantiated on P+, not on P followed
by an unaccounted delay. In particular recompute:

    C+ = (workBound(graph+) + 1) * (maximumDeadline(runtime+) + 2),
    B+ = submissionBudget(C+),
    H+ = horizon(C+).

These are the owning definitions in
[ReservedEpochExhaustion](../Vegas/Pending/ReservedEpochExhaustion.lean) and
[ReservedEpochCompletion](../Vegas/Pending/ReservedEpochCompletion.lean).
`horizon` also uses the expanded graph's cycle width and the corresponding
packet capacity. Candidate reserve must meet its new horizon bound. The tape
must satisfy the activation and processing gap conditions through C+, and the
deadlines must satisfy the actual timely margin. Old finite-prefix gap coverage
does not imply coverage over the longer execution.

The publication calculation uses a processing prefix capable of draining the
entire bounded queue, not merely one inclusion per cycle. An implementation with
smaller blocks needs a different, explicit backlog bound and a correspondingly
longer padding interval. Neither a nominal block-time bound nor eventual delivery
alone gives the required finite inclusion bound.

The existing concurrent construction samples an exogenous reserved service tape
separately from the source initialization. Correlations among players' private
inputs and among the tape's coordinates are allowed. Arbitrary correlation
between a hidden source input and an unobserved scheduler seed is not supplied
by that construction.

## The counted-to-raw composition uses conditional evidence coverage

The fine construction supplies more than existence of a complete-observation
SE. Its fully mixed counted assessments have every local gain bounded by either
a vanishing error or a mixed source gain plus that error. The finite source
assessments converge to an SE. Taking the maximum positive source pure local
gain over finitely many information sites and actions gives a number e_n tending
to zero. Mixed alternatives are convex combinations, so a uniform fine counted
regret bound epsilon_n also tends to zero.

The source padding makes the source query available at every actual counted
binding site. The candidate mask retains fresh status and successful decoding
at the handle's declared type, while treating nondecoding private preparations
as one unusable class. A counted opening cannot reveal the discarded wrong-type
capability; exact private raw memory is causally reconstructible from own
preparation history. The actual common class law is required at every positive
n, not merely at the limit.

For completeness, passage to the fine effective game also preserves the regret
bound. At an effective fine information set F and class c, choose a legal
literal representative at each compatible literal fine information set I.
The masked transition and prescribed continuation laws are the same, so

    G_effective,n(F,c)
      = sum_I Pr_n(I | F) G_literal,n(I, representative(I,c))
      <= epsilon_n.

The causal-garbling proof then gives the same bound at every actual private
information set. Its conclusion is equality of the initialized **masked**
physical law and original decoded payoff/outcome law. Literal alias histories
and private wrong-typed catalogues need not have equal laws. Compactness of
the one actual fully mixed sequence gives a counted SE. See
[the full proof route](se-private-mempool-proof-routes.md).

The final existing theorem is
`Vegas.EventGraphRuntime.PhaseCount.onePacket_raw_sequentialEquilibrium` in
[PhaseOnePacketExtension](../Vegas/Game/PhaseOnePacketExtension.lean).
It accepts any counted SE under the actual observation rule. Its assumptions
include finite Nature, base payoff bounds L_i <= u_i <= U_i on every
protocol state, a nonnegative deposit D_i, and actual audit coverage rates
alpha_i,beta_i satisfying

    U_i - L_i <= alpha_i * beta_i * D_i.

The lower bound includes the default payoff at incomplete readouts and the
individual exclusion payoff. It is not just a bound along intended play.
The theorem preserves the entire embedded terminal-history law, the joint
terminal-history/realized-settlement law, and zero audit charges on support.
Consequently the counted no-exclusion law and all original joint readouts are
preserved after erasing the padding cells.

Coverage has a strong, necessary quantifier order. For **every** actual final
evidence list A and every forbidden packet report r in A, the observation law
must reveal r with probability at least alpha_i. For **every** supported observed
list S containing r, the reporting/delivery law must include that evidence by
the report deadline with probability at least beta_i. Delivery is conditional
on the whole S; no independence between observation and delivery is assumed.
See `Vegas.EventGraphRuntime.PhaseCount.EvidenceCoverage` in
[PhaseCountCollection](../Vegas/Pending/PhaseCountCollection.lean) and
[ChallengeWindow](../Interaction/ChallengeWindow.lean).

These pointwise conditions imply collection probability at least alpha_i beta_i
after a first forbidden action, uniformly over every later policy and hidden
history. Linearity of expectation gives

    E[net payoff after that action]
      <= U_i - alpha_i beta_i D_i <= L_i.

The retained clean continuation has payoff at least L_i. This is the actual
first-departure comparison; no independence between collection and the base
payoff is needed. A large deposit without a positive conditional collection
bound does not supply this inequality when U_i>L_i.

Private pending reception alone does not establish audit coverage.
`PhaseCount.evidence` currently pairs each signed packet with the complete
submitted traffic list. A complete-evidence service is an available mathematical
instance, not automatically a physical reporting protocol. Authentic reports
must be constructible from data genuinely available to the auditor.

One concrete realization is an **audit tail**: close the game's strategic
submission interval, retain its pending envelopes, drain them into the public
ledger under the stated capacity and gap bound, and only then close the report
and settlement windows. Under the current FIFO service, the fully drained ledger
recovers the complete submitted list, including rejected messages. An automatic
public check, or a reporting protocol with proved coverage, can then provide the
required evidence. The report cutoff, inclusion bound, and settlement time must
cover this tail. The last callback of a finite gameplay horizon does not by
itself ensure that its packet was already included.

Closing submissions means that no further strategic envelope is admitted during
the drain and reporting tail. Otherwise the drained list need not be the complete
gameplay traffic and the stated capacity bound need not cover it. This tail and
its admission cutoff are a proposed backend realization of evidence coverage;
they are not supplied by the existing compiled preservation theorem.

For a builder that reorders inclusion, the full ledger recovers the envelope
set but not necessarily original arrival order. The count predicates use signed
identifiers and membership rather than list order, so a canonical-set evidence
adapter is possible; it should be specified rather than asserting that the two
lists are equal. Reporter incentives, transaction costs, and physical settlement
funding also require their own implementation argument if they are part of the
intended blockchain model.

## Delayed broadcast is outside the present emission model

The current phase emitter attaches a token from the current application view
and masks an out-of-phase call's token. A real participant may retain an earlier
authorization or a previously signed packet and broadcast it after that phase
has closed. Application rejection at that later time does not stop its plaintext
from being received privately. A finite processing delay only drains previously
submitted traffic; it cannot publish a packet that is still withheld off network.

Thus source padding does not, by itself, prove publication of every possible
future old authorized disclosure. The current theorem must not be described as
already covering this larger action model. There is, however, a direct finite
extension for the important excluded-owner case.

### Closed-opening classification

Assume genuine authorization and immutable opening certificates: an old opening
refers to its own source resolve event, accepted binding handle, value and physical
attempt. Once that reveal phase closes, its resolve event is completed. There
are two possibilities.

1. Its publication succeeded. An authenticated opening carrying that same value
   was included, and its envelope is in the ledger. The value is already public.
2. Its publication failed, through expiry or an accepted guard failure. The
   event owner is permanently excluded. Its base terminal payoff is F_i under
   every subsequent policy profile and every subsequent recovery.

The second statement follows from the exclusion transition and payoff invariants
in [PhaseExclusionOrigin](../Vegas/Pending/PhaseExclusionOrigin.lean) and
[PhaseExclusionPayoff](../Vegas/Game/PhaseExclusionPayoff.lean). Commitment rollback
does not reopen an already entered reveal phase. The classification concerns
genuinely authorized openings; a fabricated call or certificate needs a separate
invalid-evidence rule.

Here authorization must include externally checkable provenance that this
opening phase was actually reached with that accepted handle. An owner signature
and a publicly predictable attempt token do not establish this. A sender could
privately sign a hypothetical reveal for an abandoned commitment attempt whose
reveal phase never occurred. Such a packet is not covered by the classification;
the larger backend must supply phase-reach provenance or analyze this case
separately.

“The value is already public” is not sufficient to declare the first case
strategically inert. A new sender nonce, packet occurrence, or delivery time can
signal something else or change queue behavior. Exact-byte replay is harmless
only if ingress deduplication creates **no new network event, observation,
queue effect, or payoff effect**, not merely no second ledger state update.
A distinct second authenticated packet for the same physical event can instead
be treated as duplicate evidence by the audit.

### A payoff-fixed action-extension lemma

Let R be a finite perfect-recall game and G a finite action extension with an
observation-preserving history embedding. On retained actions, transitions,
observations, legal choices and utilities coincide. Assume every extra action
at an embedded R information set I of player i is enabled only where i's payoff
is already fixed: every supported terminal continuation in G after that action
pays i exactly F_i, and every terminal continuation from I within R also pays
i exactly F_i. These statements hold for all profiles and all hidden histories
in I, not merely for equilibrium play.

More precisely, supply an `ActionRestriction`: compatible embeddings of
histories, information sites and dependent action menus, with the retained
one-step transition square commuting. Finite nonempty menus supply a fully
mixed reference profile in G. An informal map on terminal outcomes alone would
not provide this interface.

Then every SE of R extends to an SE of G with the same embedded terminal-history
law and the same payoff law. The comparison is exact: for any source profile,
any extending target profile, any belief on I, and any added action a, choose
any legal retained current response and then follow the source profile.
Both expected continuation payoffs are F_i.
This discharges the direct-comparator premise of the finite restriction-extension
theorem. Its common consistent completion supplies behavior and beliefs at new
information sites. Weak equality suffices; no strict punishment is required.
The relevant generic surface is
`GameTheory.Protocol.InformationModel.ActionRestriction.sequential_equilibrium_extends_of_local_collection`
in [LocalizedEnforcement](../GameTheoryExtensions/Analysis/Protocol/LocalizedEnforcement.lean),
with no actions classified as collection-enforced.

The lemma does not assert that an added disclosure is irrelevant to the other
players. It may change their information and optimal behavior dramatically.
It asserts that its actor cannot improve its own already fixed payoff, and that
a common completion can preserve the selected equilibrium law.

Apply it **before adding audit payoffs**. Start with the padded counted
base-payoff game and allow genuinely old authorized messages by already
excluded owners, with no conflicting second packet or other count violation.
At each retained site where such an action is new, exclusion is public and
permanent, and the owner's base payoff is exactly F_i. The history embedding
uses the same actual observation kernel. It is enough to retain historical
authorization as an own-history capability; no currently valid token is
invented. This gives an SE of the enlarged counted game with exactly the original
terminal law. Newly reachable hidden late proposals need no source-archive
decoder, because the restriction-extension theorem supplies their completion.

Then extend this enlarged counted game to its genuinely raw action domain with
a sound audit covering the remaining violations. Retained histories must have
zero audit charge. The funded first-departure inequality supplies the other
comparator cases. This order matters: after a past raw violation, a prescribed
continuation may have net payoff below F_i, so a fresh claim that “silence pays
F_i” would be false. The source of the second extension is audit clean.

This is a mathematical route for a larger delayed-authorization model, not an
application of the unchanged phase-specific raw theorem. It requires its own
history embedding, authorization provenance, duplicate handling and evidence
adapter. The generic restriction-extension result is the reusable component.

### Receipt-free duplicate evidence and nonce order

The present count proof uses authenticated increasing sender serials. A packet's
verdict depends only on lower-serial own packets, and later emissions cannot
alter it. A pre-signed message with an old nonce arriving after a newer message
does not satisfy that proof's chronology hypothesis. This is a genuine gap in
directly identifying the model with arbitrary pre-signed transaction broadcast.

A time-independent replacement for the duplicate case is pair evidence:
two distinct authenticated packets by the same owner addressing the same physical
attempt/event. The pair proves the violation without a receipt, submission time,
or ordering claim. If one packet was already retained, broadcasting the second
creates this witness under every continuation. A similar pair can certify
forbidden reuse of one prepared handle. Identical-message retransmission is
handled separately by the strong ingress deduplication rule above.

The reporting condition must now cover the actual signed pair, conditional on
the whole observed evidence record. One cannot reuse a theorem that only says
the newly arriving packet's old lower-serial verdict is false: with nonce
reordering it may instead be the earlier-arriving higher-nonce packet that has
become non-first. Existence and persistence of the pair is the correct invariant.
More general invalid-opening and handle-provenance checks still need their own
sound witness format. Pair evidence alone is not a complete raw audit design.

## What adaptive builders do and do not change

The cleanup lemma does not require FIFO order if an actual bounded service
guarantee still includes every old envelope before the next semantic choice.
The ordered-pending reconstruction used for causal garbling also permits arbitrary
delivery order, provided submissions append, delivery removes without reordering
the remaining pool, identifiers are unique, and delivered messages do not requeue.

The masked projection and private-observation simulation continue to work for a
history-dependent environment kernel if that kernel is the same function of the
retained physical history in both compared games. It may observe the full pool
and its own past decisions. It may not secretly depend on the discarded private
alias catalogue or on private reception samples absent from that retained history.

These facts do not extend the fine preservation theorem automatically to every
adaptive builder. The existing fine proof uses the reserved tape and its service
and conditional comparison results. A different scheduler still needs a fine
uniform-regret construction, actual completion and protection of timely honest
packets, and authentic audit/report coverage. A merely average inclusion rate
is insufficient for the conditional comparisons at rare information sets.

Nor can arbitrary correlation with hidden source values be admitted for free.
For example, take a source player who does not observe a fair hidden bit theta,
chooses a guess, and earns one exactly when the guess equals theta. A pure
constant guess is a source SE. If an implementation's public scheduling signal
reveals theta before that choice, every target best response guesses theta and
the prescribed joint law with the constant guess is impossible. This is a
finite information counterexample, not a claim that a builder inspecting opaque
canonical commitments obtains such a bit. It identifies the additional hidden
information that must be excluded or modeled.

The padded theorem therefore closes a specific finite mathematical target with
the stated service, authorization and audit interfaces. A concrete blockchain
realization must supply those interfaces. The excluded-owner extension shows
that delayed old disclosure need not require fabricated common knowledge or a
time-dependent penalty, while leaving replay handling and the remaining raw
evidence obligations explicit.
