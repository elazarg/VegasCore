# Composition of disclosure phases at genuine public subgames

Analysis by Codex. This is a restricted mathematical composition result and a
description of the missing argument for ordinary programs with retained hidden
bindings. It is a paper proof, not a checked Lean theorem or a source-to-runtime
adapter. It does not introduce an automatic audit, forced disclosure service or
new compiler construct.

The single-phase construction in
[full-public-disclosure-phase-preservation.md](full-public-disclosure-phase-preservation.md)
can be composed by backward induction when the source already has genuine
public subgame boundaries between its phases. Fresh future inputs alone do not
give that property: players may retain old correlated private information and
use it in later decisions.

## The restricted source model

Consider a finite game with perfect recall. Its public control tree contains
ordinary public decisions and disclosure phases. At the entry to each phase
$h$, the past game state is common knowledge. Nature draws a fresh pair of
private types $(i,j)$ from a finite full-support joint kernel
$\pi_h(i,j)>0$, tells the current sender $i$ and the current receiver $j$, and
provides no other private signal during the phase. Sender and receiver are
distinct strategic players. The kernel can depend on the
entire public logical history $h$. It is independent of earlier private state
conditional on that history.

A phase has the source structure used by the single-phase theorem: the sender
opens an immutable value $v_h(i)$ or withholds; success discloses the value;
the receiver then makes one finite terminal phase response. Withholding is a
lawful source action with an intrinsic failure forfeit $D_h$. After that
response, either the whole game ends or the source reaches its next genuine
public subgame boundary. In the latter case, the old private phase information
has already become public through operations present in the source game.
There are no additional strategic decisions between the receiver response and
that boundary.

This last condition is substantive. Examples include a protocol whose failed
disclosure terminates execution and whose successful phase has disclosed all
the phase's old private cells, or a source game with an explicitly stipulated
dealer that reports its previous private draws before dealing again. Reporting
is not assumed to be available to an ordinary blockchain for a value its owner
never supplied. A phase with unresolved hidden bindings followed by more
decisions does not satisfy this model.

The source may branch on earlier public responses, revealed values and publicly
known guards. A false public guard skips the phase according to the source
rules. Every phase that is entered has its prescribed opening available. The
source does not expose a private guard or start a subsequent decision while
the current disclosure is unresolved.

Fix a source SE $A$. Its continuation after every public boundary is an SE of
that public subgame, including boundaries that have zero probability under its
initialized strategy. This restriction follows from sequential rationality and
the same fully mixed source consistency sequence: the probability of the
public entering prefix cancels when conditioning inside the subgame, while
its fresh Nature kernel is fixed.

## Intrinsic forfeits must dominate the whole continuation range

For the sender $p$ at phase $h$, remove only the current phase's forfeit from
its terminal source payoff. Assume the remaining terminal payoffs, across
every legal continuation from this phase, lie in some interval
$[L_h,L_h+R_h]$, and require

$$
D_h>R_h.
$$

The range includes future payoffs, future failure charges and all branches
selected by the current response. It is not merely the immediate phase prize.
Subtracting $L_h$ is a harmless normalization of the current comparison.
Under this hypothesis, withholding yields at most $L_h+R_h-D_h<L_h$, while
successful opening followed by any legal source continuation yields at least
$L_h$. Thus source opening is strictly preferable at every sender type. In
particular the selected source SE always opens at each entered phase.

These inequalities are restrictions on the source game. A compiler cannot
create them by charging a new fine for a lawful source action.

The condition can be arranged without circular parameter choices in a finite
additive model. For example, suppose terminal utility is a bounded base payoff
minus the forfeits at failed phases owned by that player. Choose the forfeits
backward through the finite public control tree, making $D_h$ exceed the base
payoff range plus the sum of all possible later forfeits of the same owner.
If that owner has no later forfeits, its base payoff range already suffices.
If failure changes future availability or guards, those resulting branches
must also be included in the bound. A common fixed forfeit used repeatedly
does not automatically satisfy this condition.

## The target comparison

At each phase replace the opening with the fully public finite-opportunity
comparison from the single-phase note. Protected opening succeeds surely.
At each entering public target prefix $H$, there is a fixed finite list of
late opportunities with publicly known conditional inclusion laws
$q_{H,t}(v)\in[0,1]$. Given the emitted value, these laws do not depend on the
remaining hidden sender type or the receiver's private type. Every emitted
packet discloses its immutable value on either possible resolution branch;
never sending does not. There are no retries, replacements, aliases or other
owned actions in the phase. The receiver responds only after the selected
packet has resolved or the no-emission outcome is fixed.

An unsuccessful late send additionally charges the current owner a finite
$c_H\ge0$. This is an additive sunk charge: it does not change later menus,
admission, input kernels or payoff functions through a balance constraint.
Transmission metadata may refine the public history. At the next existing
public source boundary, however, the logical transition and fresh type kernel
are exactly those of the corresponding source boundary. Future canonical
play may ignore the extra metadata. This is a model premise, not a claim
about the unrestricted Vegas runtime.

The complete entering prefix $H$, including its extra metadata, is public to
all relevant players at the boundary. The next fresh prior is precisely
$\pi_h$, where $h=\operatorname{logical}(H)$; no additional hidden runtime
state changes that prior or the subsequent logical menus.

Reliability and drop charges may therefore depend on earlier public runtime
metadata, even when that metadata has no source counterpart. The theorem does
not allow new signals during a phase to change its fixed opportunity list or
give a player private information about its inclusion kernel.

## Outcome preservation theorem

Under these hypotheses, every selected source SE has a target SE with the same
initialized joint law of the logical terminal history, all source private
draws, player responses and source payoffs. Its initialized execution opens at
every protected phase turn and incurs no additional late charge. The target
can choose different replies and beliefs on source failure branches of
probability zero. The theorem does not embed the selected assessment literally.

The proof proceeds backward through the finite public control tree.

At a terminal boundary there is nothing to construct. At an ordinary public
decision, preserve the source action distribution and use the already lifted
continuations for every available action. Each continuation has the selected
source continuation's initialized payoff law up to any fixed additional
charges inherited from earlier target phases. Those charges are sunk constants
for the respective players at this boundary. They do not change any payoff
comparison. The public decision's comparisons therefore remain those of the
source SE, including its comparisons against actions it does not choose.

At a phase $h$, use the already lifted target continuation at every possible
following public source boundary. For every phase type pair, publication
result and receiver response, substitute its expected continuation payoff into
the local phase payoff. The receiver may account for the dependence of this
payoff on the response and on the private type pair eventually made public.
Other players have no owned decision before that following boundary.

These reduced sender payoffs, with the current forfeit removed, remain in
$[L_h,L_h+R_h]$ after removing inherited target charges, which are common
constants at the current public prefix. The current phase's charge $c_H$ is
accounted for explicitly in the late-failure payoff. The selected source
success responses are best responses
under $\pi_h(i\mid v,j)$: every source sender type opens, and every reached
$(v,j)$ has positive probability. The lifted future continuations reproduce
the relevant source payoffs. Apply the single-phase theorem, including its
value-dependent reliabilities and correlated-private-type extension. It
constructs the phase's off-path timing policy, receiver replies and a common
fully mixed local consistency sequence. It preserves the selected source
success responses and chooses protected opening.

A failed emitted packet can disclose more than the corresponding source
withholding branch before the receiver responds. That is handled by choosing
a new locally rational failure response. If the game continues, its response
and the source's existing public reset identify a legal following source
boundary. The induction supplies a continuation there too; it does not reuse
a continuation from a different receiver response. No initialized source
failure outcome needs to be preserved, because intrinsic forfeits make that
outcome unreachable in the selected source SE.

Future deviations do not invalidate this local reduction. After the next
public boundary, the constructed continuation is an SE; a player cannot gain
by replacing its whole subsequent behavior there. Conditional on each public
boundary, its optimal continuation payoff is therefore the prescribed one.
The phase comparison consequently covers deviations that change both the
current timing or response and the player's later strategy. The finite
perfect-recall one-deviation argument then gives sequential rationality of the
entire constructed profile.

## One consistency sequence for the whole game

There are finitely many legal public target prefixes, including the finite
transmission metadata. Choose a local fully mixed consistency sequence for
each phase lift. At ordinary public decisions, mix the prescribed action
distribution with a vanishing positive uniform lottery. Use the corresponding
local term at each public prefix, and pass to a common subsequence if needed
so that every local belief limit converges. Finiteness permits a single
diagonal choice; the resulting whole-game profiles are fully mixed.

The reason local consistency survives this concatenation is operational
factorization. If $H$ is an entering public target prefix and $z$ a current
phase history with current fresh types $(i,j)$, its likelihood is

$$
\Pr_n(H,z,i,j)
=\Pr_n(H)\,\pi_h(i,j)\,K_{h,n}(z\mid i,j),
\qquad h=\operatorname{logical}(H).
$$

The factor $\Pr_n(H)$ is common throughout each current information set and
cancels from Bayes conditioning. The fresh kernel is independent of all
earlier private history and of the extra transmission metadata. Thus every
within-phase posterior is exactly the corresponding local Bayes posterior
before taking its limit. At later public decisions there is no unresolved
private state to reconstruct. This proves whole-game consistency from actual
fully mixed likelihoods, rather than assuming posterior equality.

## A uniform-forfeit corollary for additive utilities

The whole-terminal-range condition above is sufficient, but conservative.
There is a stronger additive specialization that does not require increasing
the earlier forfeits to exceed the sum of later ones.

Suppose each player's source utility has the form

$$
U_p(z)=b_p(z)-\sum_{h\text{ failed in }z:\,\operatorname{owner}(h)=p}D_h,
\qquad b_p(z)\in[L_p,L_p+W_p]
$$

over every terminal logical history $z$. Suppose every entered opening is
available, and a skipped public guard imposes no failure charge. Retain the
public-subgame, fresh-input and target hypotheses above. It suffices that

$$
D_h>W_{\operatorname{owner}(h)}
$$

at every phase. A single constant forfeit per player can satisfy this bound,
even when that player owns several phases. The forfeits are still intrinsic
source utilities, not new compiler penalties.

To prove the corollary, induct backward simultaneously on source openings and
their target lifts. At the final phase, withholding loses its current forfeit
and success does not; the base payoff range gives the strict source opening
comparison immediately. At an earlier phase, every selected source
continuation at a following public boundary already opens at all its entered
phases by induction. It therefore incurs no later failure forfeit. Its
constructed target continuation also opens protected and incurs no later
additional charge. Remove past sunk charges and the current phase's forfeit
from the reduced payoff: its range is at most $W_p$, not the sum of the
possible future forfeits. The local single-phase theorem consequently applies
with $R_h=W_p$.

An alternative future strategy could deliberately incur later charges or
change later responses. That does not require replacing $W_p$ by a bound on
those arbitrary trajectories: later continuation SE optimality already rules
out a profitable whole future replacement at each following public boundary.
The current reduced comparison therefore uses the prescribed, optimal future
continuation values. This is the same reduction that justifies the main
backward-induction proof.

The distinction matters. The uniform additive hypothesis need not make
opening dominate every arbitrary future strategy at the current phase.
It makes opening optimal against the selected sequentially rational future
continuations, and then proves all phase openings together by induction.
A guard that automatically charges failure, an unavailable future opening,
or nonadditive balance effects can invalidate this argument.

## Why this does not settle general multi-phase preservation

Ordinary programs can retain a hidden binding through several decisions. A
failed reveal may disclose its value to the mempool without resolving that
binding in the source, and subsequent players may choose actions using this
extra information. Fresh later randomness does not remove knowledge already
held by players. The public-prefix likelihood is then not the only prefix
factor: old private histories have different weights inside a later
information set.

There is a second obstacle even without overlapping deadlines. Replacing the
single terminal receiver decision by a continuation game requires a whole
consistent continuation assessment. Choosing an SE under a limiting
no-emission law $w$, and separately using the explicit outer calibration
$p_i=\varepsilon^M(w_i/\pi_i+\varepsilon)$, is insufficient. That initial-law
sequence can differ from the continuation SE's own sequence and induce
different beliefs at its internally off-path information sets. A coupled
auxiliary extensive-game construction might resolve this, but the current
selector proof does not supply it.

Overlapping phases add another issue: an irreversible receiver choice can
occur after an early pending transmission and before a later transmission.
Complete observation at every decision still gives different information at
those two decision times. A theorem requiring the sole receiver choice after
all disclosure outcomes are fixed does not apply to that situation.

The useful boundary is therefore precise. Existing public subgames permit
composition by likelihood cancellation and backward continuation values.
Retained hidden bindings, strategic private input selection, intermediate
receiver decisions and unrestricted runtime action menus require further
information and deviation adapters. This note changes no asynchronous target,
checklist box or runtime assumption.
