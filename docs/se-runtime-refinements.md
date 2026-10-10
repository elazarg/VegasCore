# Checked boundaries for realistic SE preservation

Analysis by Codex. These results separate a useful positive economic mechanism
from the information-consistency obstruction and from the assumptions of the
calendar compiler. They retain the existing source and runtime semantics and
do not change the target or boxes in the [async checklist](se-async-checklist.md).

An abstract source language remains a reasonable goal. A public pending packet
does not, by itself, make SE preservation impossible. What matters is whether
the additional runtime choices can change continuation incentives and whether
the backend supplies enough additional enforceable cost to neutralize them.
The checked results below concern the existing calendar compiler and the
finite late-leak example. They do not assert a preservation theorem for an
ordinary public-mempool blockchain.

## A finite failure penalty can preserve SE despite visible disclosures

In the existing late-leak game, write R for the reward scale, D for the failure
forfeit, c for the charge on a dropped send, and q in (0,1) for late inclusion
probability. The protected opening succeeds; a late send succeeds with
probability q. A dropped first late send discloses its contents to the listener.
There are two late decision turns, and dropping a send terminates that attempt.

The checked positive theorem is:

\[
R\ge 0,\qquad D>R/2,\qquad (1-q)(D+c)>R/2
\quad\Longrightarrow\quad
\text{every target SE has the intended outcome law}.
\]

A target SE exists, so the assertion is nonvacuous. The intended law is that
every type opens at the protected turn and the listener answers safely.
See [CalibratedPenaltyPreservation](../Vegas/Examples/LateLeak/CalibratedPenaltyPreservation.lean),
especially `lateLeak_outcome_preserved_of_half_reward_costs` and
`lateLeak_preserving_equilibrium_of_half_reward_costs`.
Consequently every SE of the intended game has a target SE with exactly the
same full terminal-state law, checked as
`lateLeak_sequentialEquilibrium_preserved_of_half_reward_costs`. This is
equilibrium-outcome preservation for this finite family, rather than a
theorem about one proposed translation's off-path strategies or beliefs.

The outcome conclusion also holds for every sequentially rational assessment
with Bayes beliefs at positive-probability information sets. This is the usual
weak-PBE requirement and needs no consistency restriction on zero-probability
information sets. The checked statement
`lateLeak_outcome_preserved_of_rational_bayes` uses the library's existing
rationality and Bayes predicates rather than defining a different equilibrium
notion. This positive statement uses the displayed cost bounds; it does not
mechanize the separate weak-PBE construction under the negative SE margins.

The proof bounds every deferral continuation, regardless of the listener's
off-path replies. Types with label A or B receive at least R/2 from every
protected reply. Never sending pays at most R-D, and sending late pays at most
R-(1-q)(D+c); both are strictly below R/2. Label C has zero base reward at
failure and at most R/2 at success, so every deferred continuation pays strictly
below zero, while protected opening has nonnegative payoff. This also bounds
the policy that waits through the first late turn before deciding at the second.
Sequential rationality therefore forces protected opening by every type.
These openings retain the prior's uniform label distribution at each
protected-success information set; Bayes consistency then makes the safe reply
strictly better than every label guess.

For any fixed q<1, the checked forfeit-only corollary uses
D=R/[2(1-q)]+1 and c=0. It requires no collection of a charge on dropped
packets. For example, R=2, q=99/100, c=0 and D=101 suffice. The alternative
finite-charge corollary fixes any D>R/2 and uses c=R/[2(1-q)]>=0. These are
sufficient bounds, not optimized collateral requirements. The actual backend
must collect the specified forfeits and charges; this example does not derive
that ability from observing a dropped packet.

The proof using coarse sender payoff bounds in
[PenaltyPreservation](../Vegas/Examples/LateLeak/PenaltyPreservation.lean)
also establishes this game's preservation under the stronger costs D>R and
(1-q)(D+c)>R. The sharper theorem uses this game's particular type payoffs.

This resolves an important quantifier distinction. The negative theorem fixes
finite margins and then chooses sufficiently high q. The positive theorem
fixes q<1 and then chooses sufficiently large margins. They are compatible.
The positive theorem assumes neither invisible pending messages nor autonomous
release. Its limitation is the finite game's actual inclusion and penalty
rules; it is not yet an adapter for arbitrary source games or real chains.

## The negative result has a quantitative gap

Set g=qR-(1-q)(D+c). Under the checked negative margins

\[
q(D-R)>(1-q)c,\qquad g>R/2,
\]

and R>0, D+c>=0, every target SE loses intended protected-safe probability in
some type (v,A). The corresponding full-state total-variation lower bound is

\[
\frac{3}{20}\frac{2g-R}{R}.
\]

At R=2, D=6, c=3 and q=99/100, this is 267/2000. Thus the sample obstruction
also excludes arbitrarily accurate approximation of the intended law by exact
target SE. See [OutcomeSeparation](../Vegas/Examples/LateLeak/OutcomeSeparation.lean).
This statement concerns exact sequential equilibria; it does not establish
the same bound for approximate rationality or for weak PBE.

The full-state law retains initial type, resolution and answer, including the
protected-versus-late distinction. A separate checked readout erases every
transmission-timing detail and retains only initial type, success/failure and
answer. Its sample total-variation gap is still at least 3/2000. In general,
put alpha=2(1-g/R); the corresponding gap is

\[
\frac{3}{20}[1-\max(\alpha,q)]>0.
\]

This coarser theorem requires the negative margins but does not need the extra
D+c>=0 hypothesis of the full-state bound. See
[ObservableOutcomeSeparation](../Vegas/Examples/LateLeak/ObservableOutcomeSeparation.lean).
It excludes preserving the target's joint initial-parameter/public-result law
in this family even when timing is absent from the preservation specification.
It retains initial type; it is not a theorem about only the marginal answer
distribution. Forgetting information can reduce total variation, so every
readout needs its own argument.

## The fixed horizon supports a conditional whole-run probability bound

The probability calculation needed for bounded retries is checked independently
of the game. Let E be the event that all attempts so far have failed, recorded
in the execution state. Suppose each transition, from every compatible state
in E, remains in E with probability at least a>=0. After N transitions,

\[
\Pr(E\text{ after }N)\ge a^N\Pr(E\text{ initially}).
\]

Different floors give the product of the individual floors. No independence
assumption is needed; state can contain the complete history and policies can
adapt to it. The pointwise premise covers every state in E, including states
outside the equilibrium path.
See [Survival](../GameTheoryExtensions/Math/Probability/Survival.lean).

[ReactiveSurvival](../Interaction/ReactiveSurvival.lean) instantiates this result
in the existing reactive scheduler-round evaluator, retaining its full
execution and recall. From any initial execution in E, the bound is a^N;
it is strictly positive for a>0 and finite N. The same result holds when
execution stops adaptively within N rounds, with a<=1: stopped states remain
unchanged, and the floor is needed only at states where execution continues.
A backend must establish the floor
for all permitted fee bids, routes and relevant continuation policies. A bound
averaged over an initial distribution does not establish this premise.

The source's fixed horizon helps bound N only after the backend bounds physical
opportunities per source event. Ordinary liveness does not provide either
this count or a positive conditional failure floor. Furthermore, the failed
event must produce an additional collectible penalty relative to faithful
execution. A shared chain outage or a previously paid charge is insufficient.
These operational adapters remain the substance of a general preservation
theorem; the probability lemma does not assume them into existence.

## The calendar theorem needs less from its unused network policy

The roster calendar issues reserved instructions and never issues the
discretionary `.wire` instruction. Its scheduler law is independent of the
network policy, at every scheduler history and environment view. Consequently
the actual `SourceServiceSpec` and compiler capstone no longer require the
network policy to have finite support. Finite support is still required for
the initial law and pending-observation rule.

This is a genuine assumption removal in the existing capstone, rather than a
second theorem with the same premises.
See [ServiceRoster](../Vegas/Game/ServiceRoster.lean),
[SourceServiceSpec](../Vegas/Game/SourceServiceSpec.lean) and
[SourceServiceCompilation](../Vegas/Game/SourceServiceCompilation.lean).
The finite-support proof for any reserved plan is in
[ReactiveServiceFiniteness](../Vegas/Pending/ReactiveServiceFiniteness.lean).

There is also a checked all-history fact: every activation of a ready event's
owner lies inside its protected inclusion window. It applies to raw legal
histories, including deviations, and does not assume activation coverage.
See [ServiceRosterProtection](../Vegas/Game/ServiceRosterProtection.lean).
This identifies why the calendar avoids the late-turn lottery; it does not
generalize the calendar to arbitrary adaptive or probabilistic scheduling.

## What remains to obtain a realistic compiler theorem

The [general preservation analysis](general-se-preservation.md) packages the
checked no-clock audit extension with deposits chosen before every source SE.
It separates the public stochastic scheduling adapter from raw enforcement
and gives an honest off-path information counterexample to weaker adapters.

The economic result supports bounded-risk enforcement as a real alternative
to requiring secret pending packets. The probability result supports computing
a whole-game bound from conditional backend premises. The calendar result
removes an unnecessary restriction but still uses reserved inclusion.

A broader positive compiler theorem needs a source-compatible runtime subgame,
information and outcome correspondence, consistent rational completion, and
conditional additional-cost bounds for excluded departures. The existing
restriction-extension and audit machinery should be instantiated with those
adapters. The confidential-ledger options and their concrete obligations are
described in the [blockchain target analysis](blockchain-se-preservation-target.md).

The literal necessity claim that every weakening of private admission,
irrevocable ordering or autonomous release destroys preservation is too strong.
Both the calendar and the penalty theorem provide alternative sufficient
mechanisms. Useful necessity results must fix the game class and available
enforcement and exclude compensating changes. General weak-PBE preservation,
the explicit weak-PBE construction, and a confidential-chain compiler adapter
remain unproved here.
