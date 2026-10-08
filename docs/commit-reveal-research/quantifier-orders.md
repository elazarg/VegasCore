# Collateral chosen before or after the service

The checked settle-late comparison already gives a negative answer to one
abstract preservation question. It leaves a different positive question when
collateral may depend on a known builder. Neither statement alone settles the
full compiled runtime. This document keeps those scopes separate.

The primary project question chooses collateral before the selected builder,
using only public service properties. The fixed-builder calculation below is
a pedagogic contrast. A publicly uniform bound can sometimes turn that
calculation into a constants-before-builder result for a restricted class;
the bound itself then requires justification.
[Miner behavior and player knowledge](miner-assumptions.md) distinguishes this
uniformity from what players know about the service.

## The finite game behind the checked negative

Nature gives the sender a bit and an independent, uniformly distributed
private label from three possibilities. The bit has probability 9/20 of being
one. An opening discloses the bit, but not the label. After a successful opening,
the listener chooses Safe or guesses the label. Safe pays the listener 2/5;
a correct label guess pays one. The sender receives R/2 for Safe, and either
R or zero for a label guess, depending on its private label. After a failed
opening the listener guesses the bit, and the sender's reward also depends
on its label. All sender base rewards lie between zero and R.

The intended game requires the sender to open at its protected opportunity
and emit no extra signal. That opening is included surely. The listener still
has a uniform label posterior, so Safe is strictly optimal. Every intended SE
has that outcome, and the intended game has an SE.

The implementation comparison adds these choices and observations:

- The sender can instead wait and use either of two late sending opportunities.
- A sole late opening is included with probability q. With two openings, each
  is included with probability q/(1+q), and at most one is included.
- Late inclusion occurs only after the last sending opportunity. The sender
  therefore cannot retry after learning its first opening's inclusion fate.
- The listener observes between the two late turns. Each pending opening is
  shown independently with probability lambda at each listener activation;
  dropped openings remain pending and can be observed again at the answer.
- The sender can emit raw bit signals, including after a protected opening.
  The listener can emit one packet during its intermediate observation. The
  sender sees that packet; it does not displace an opening.
- The ledger exposes the included packet's serial, so additional packets can
  also communicate through that serial.
- The sender loses D if no opening is included, and pays c at most once if any
  of its packets is not included. Raw signals and duplicate openings create
  that capped charge. The listener's intermediate packet has a specified cost.

This is a finite comparison game with its own action and observation interface.
It is not a claim that all those choices exhaust the compiled runtime.

## What the checked theorem says

For every R>0, every D>R, every c>R/2, every lambda strictly between zero and
one, and every listener packet cost, there is an explicit threshold below one
such that **every q strictly between the threshold and one** has no implementation SE with the
intended outcome law. The intended game's existence and outcome assertions
are part of the same checked statement.

The threshold is

\[
\max\left\{
\frac{D+c+R-\min(c,D)}{D+c+R/2},
\frac{D+c+R/2}{D+c+R/2+\lambda R/2}
\right\}<1.
\]

See `Vegas.Paper.settle_late_not_preserved_for_every_margin` in
[Paper.lean](../../Paper.lean), and the proof in
[SettleLatePreservation.lean](../../Vegas/Examples/LateLeak/SettleLatePreservation.lean).
This is existing machine-checked evidence, not a new paper proof in this
research project.

The information issue concerns the sender's remaining private label. Even
though opening the bit is lawful, the chosen late turn and whether the listener
saw it can convey label information absent from the intended opening. The
proof derives restrictions on that information from SE consistency, forcing
an attractive late deviation in any purported preserving equilibrium.

**The scope matters.** Charges c at or below R/2, complete pending observation
lambda=1, and a theorem for an independently specified different builder are
outside this checked conclusion. Malformed and wrong-event packets, aliases
and the complete native action space are not covered. Adding actions can
restore equilibrium implementation, so a native embedding must control their
incentives and observations, not merely reproduce this game's paths.
[Comparison scope](../runtime-features-vs-late-leak.md#limits).
The [reviewed native construction](native-late-action-analysis.md) does this
for an explicit three-instruction source and the complete bounded raw menu,
with explicit fixed native charge bounds. It has a paper proof; its exact source,
scheduler, menu and belief identities remain to be formalized in Lean.

## Two orders of quantification

Both orders below choose the compiler and collateral before selecting the
source equilibrium. They differ in whether the service is already known.

| Order | Required preservation claim | Present status |
| --- | --- | --- |
| Collateral before service | Choose one finite collateral configuration that works for every builder in the declared class. | Checked negative in the settle-late family for D>R and c>R/2; reviewed full native paper negative with D>max(R,1), K_A>R/2 and K_B>1. Native formalization remains outstanding. |
| Service before collateral | For each known builder satisfying stated bounds, choose a finite collateral configuration that works for every selected source SE. | The fixed-q comparison below has a paper bound forcing the intended law in every target SE. General compiled-runtime preservation remains open. |

For fixed collateral, the builder can make 1-q small enough that expected
failure deductions disappear while an informational timing benefit remains.
For fixed q<1, increasing collateral can instead dominate the benefit. The
two statements are compatible. The checked negative does not prove that every
fixed builder defeats every deposit.

## A positive paper argument for the same fixed-q comparison

Fix R>0, q strictly between zero and one, lambda strictly between zero and one,
and any finite listener packet cost. Choose equal forfeit and audit amounts
D=c=K. The source remains the intended game described above, where neither
amount is ever deducted.

**Proposition, paper proof.** If K>R/(1-q), the implementation has an SE and
every implementation SE has the intended protected-opening, no-extra-signal,
Safe outcome law, including the original joint private-parameter distribution
and realized payoffs. Thus every intended source SE outcome is implemented,
and no other initialized target SE law occurs in this comparison.

Write F for failure to include any opening and A for the capped audit charge.
At every terminal history the sender's exact utility is

\[
b-KF-KA=(b-K(F\wedge A))-K(F\vee A),\qquad 0\le b\le R.
\]

Here indicators take values zero or one. This is an algebraic decomposition
of the existing two deductions. It introduces no new physical charge. The
residual base utility is at most R uniformly in K, and equals the source base
utility on all retained histories, where both indicators vanish.

The first additional action at a retained sender decision is either a raw
signal or silence at the protected turn, or a raw signal after its protected
opening. A signal incurs A certainly. Following protected silence, classify
each continuation:

1. If it emits a signal or duplicate opening, A is certain.
2. If it emits no opening, F is certain.
3. Otherwise it emits exactly one opening. That opening fails with probability
   1-q, in which case both F and A occur.

The same bound covers adaptive later choices. Whether the first opening was
observed and whether the listener sent its packet can affect the sender's
later action, but do not change a sole opening's inclusion law. Conditional
on each pre-inclusion history containing exactly one unsignaled opening, the
failure probability is 1-q; no-opening histories fail surely, and signals or
duplicates make A certain. Equivalently, the finitely many deterministic contingent
plans have the bound, and all behavioral mixtures inherit it.

Consequently the union event F or A has probability at least 1-q after every
first excluded sender action, under arbitrary subsequent play. This is **not**
a bound on the c-charge alone: emitting nothing forfeits D but incurs no c.
The retained listener decisions have exactly the old menus, so there is no
excluded listener action to deter there. New listener sites are completed
rationally, with their stated packet cost.

The bound proves the game-level conclusion directly. Every complete policy
after protected silence has expected utility at most R-(1-q)K. Opening at the
protected opportunity and then remaining quiet instead gives nonnegative
utility against every listener policy. At the sender's post-protected decision,
a raw signal gives at most R-K, while remaining quiet gives nonnegative utility.
Consequently, under

\[
K>\frac{R}{1-q}.
\]

both prohibited alternatives are strictly worse, regardless of the listener's
continuation. A raw signal at the protected turn also charges K certainly,
so has value at most R-K<0. Sequential rationality therefore forces every
sender type to open at the protected opportunity and remain quiet afterward.
Every bit has positive prior probability, and the listener's reached information
then carries no additional label signal. Bayes' rule leaves all three labels
equally likely. Safe pays 2/5, strictly above the payoff 1/3 of each label guess,
so the listener chooses Safe.

The game is finite with perfect recall, so it has a sequential equilibrium.
The preceding argument applies to every such equilibrium, including whichever
rational off-path completion it uses. Neither penalty is collected on its
initialized path, proving the joint law and payoff conclusion. The same
outcome conclusion holds for weak PBE requiring sequential rationality and
Bayes updating at reached information sets; no off-path consistency choice
can overturn the strict sender comparisons.

The bound is conservative. It gives an exact equilibrium and exact intended
law for each fixed q, without requiring any additional charge after the
initial capped charge has become sunk.
Using both deductions directly sharpens the sufficient bound to
K>R/min{1,2(1-q)}: a signal, duplicate or absent opening costs at least one
unit of K, while a sole unsignaled opening costs two units with probability
1-q. Conditioning before inclusion and averaging gives the minimum of those
two bounds. This still makes deferred utility negative and implies K>R,
which makes post-protected signals negative.

These bounds grow without bound as q approaches one. The checked negative,
rather than the growth of a sufficient bound alone, establishes that no common
finite collateral in its stated margin ranges covers all those builders.

**Status:** complete paper proof, not a new Lean theorem for this game. It covers
precisely this finite action interface and ideal monetary utility. Borrowing
costs, fees and native additional actions need their own treatment. The bound
is sufficient and is not asserted to be minimal. The full compiled runtime
has not been shown to reduce to this comparison in either direction.
Both deductions must be fundable: when they both trigger, the prescribed loss
is 2K. A single capped reserve of K cannot implement that settlement. The paper
proof does not charge an opportunity cost for the reserved funds.
The source here requires opening. A language game with lawful withholding and
its own failure payoffs needs a separate preservation argument; protected
silence with a later recovery opportunity is not an immediate source refusal.

## What a general builder-first theorem must establish

For a deviation comparison fixed independently of the chosen penalty, let g
be its base utility gain, including relevant fees, and r its additional expected
collection relative to a legitimate continuation. When r is nonnegative, one
finite penalty covers the whole comparison family exactly if

\[
r=0\Longrightarrow g\le0,
\qquad
\sup_{r>0}\frac{\max(g,0)}{r}<\infty.
\]

This is a local calculation, not by itself an SE-preservation theorem. The
family must cover conditional decisions and all later strategies; legitimate
comparators and a common consistent completion still need construction.
See [the enforcement analysis](service-and-enforcement.md#the-exact-conditional-penalty-calculation).

A lower bound on a single late packet's failure probability can supply r in
the fixed comparison above. In the native runtime, retries, replacements,
receipts, aliases and different future policies can alter that probability or
avoid additional collection. An honest-operation failure *upper* bound gives
an execution reliability estimate; a deviation's collection *lower* bound
gives deterrence. They answer different questions. A positive floor is
sufficient, but not necessary if potential gains vanish proportionally to
collection risk or fees already make the actions unprofitable.

The two independent native research tasks are therefore to realize the checked
negative with complete additional-action coverage, and to derive the fixed
builder's conditional gain/collection bounds and source-information
correspondence. Neither task should assume the other has been solved.
