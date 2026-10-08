# Concurrent immutable disclosure does not remove timing incentives

Analysis by Codex. This paper comparison uses only immutable truthful
publications, lawful withholding and transport timing. It has no receiver guess
or strategic choice of a committed value. It shows that an intrinsic failure
forfeit above the owner's base payoff width is insufficient for SE outcome
preservation under the asynchronous contract alone. Complete pending-message
observation does not change that conclusion.

The comparison fits the operational permissions of the actual
`AsyncContract`: a protected first call must receive inclusion, while a sole
late call outside its protected window can fail. Its complete native
`AsyncServiceSpec` and RAW information-game embedding is not proved here.
In particular this is not a negative theorem for the audited compiler with
arbitrarily large deposits. An explicit audit calculation repairs the example.

## Source game

There are three players. Each has one initially bound, immutable value, which
is already openable. The values can all be the Boolean true; no private type
uncertainty is needed. The source program is a `RevealOnly` sequence of their
three disclosures. Each source owner may open or withhold. Successful openings
publish the bound value; withholding records a failed reveal.

Player $p$ has base payoff

$$
u_p=W\,\mathbf 1\{\text{some other player's publication failed}\},
\qquad W>0.
$$

An own failed reveal subtracts an intrinsic $D$, with $W<D<2W$. Thus each
owner's base payoff range is exactly $W$, and $D$ exceeds that range.
The source SE opens all three values. At the final source reveal, opening
avoids $D$ and withholding cannot gain more than $W$. Backward induction gives
the same conclusion at the preceding reveals. The initialized source outcome
is all-success with payoff zero to everyone.

## A finite public asynchronous comparison

Compile the independent disclosures in concurrent-reveal mode, so all three
events can be ready initially. Give each event deadline duration two, reaction
bound zero and inclusion bound one. All readiness episodes begin at clock
zero.

The scheduler offers, in fixed publicly known order, one owner activation per
player at clock zero. Each owner either sends its canonical opening or waits.
The scheduler then advances to clock one and gives, again in fixed order, one
activation to each owner that has not sent. Its choices are the canonical
opening or silence. An owner that has already sent remains silent; it does not
retry. There is at most one packet per owner in this comparison.

Every player observes all earlier pending emissions before making its next
decision. An early emission is public evidence that an early opening was sent;
absence at an already completed protected opportunity is also understood from
the fixed public activation order. No packet is assumed permanently invisible.
There is no intermediate choice other than the owners' remaining publication
decisions.

The fixed values and these public histories make every comparison-game
decision information set a singleton. Fully mixed player trembles therefore
have the same singleton Bayes beliefs throughout. Backward optimality supplies
an SE with genuine consistency; no off-path posterior is stipulated.

The public controller uses the following inclusion kernel.

- If any opening was sent at clock zero, it accepts every submitted canonical
  opening at clock one. An owner that remains silent through its last
  opportunity expires and fails.
- If no opening was sent at clock zero, each submitted late opening is
  accepted with probability $1-\varepsilon$, independently across owners.
  Otherwise that event expires and fails. An owner that never sends also
  fails. Here $0<\varepsilon<2-D/W$.

All selections occur while the clock is one. The controller then advances to
clock two and expires every unresolved event. The horizon contains these
finite selections, clock changes and expiries.

The inclusion law depends on the public earlier packet traffic. This is
allowed by the current asynchronous contract. It is a deliberately simple
batch/recovery controller, not a claim that a named L1 implements this policy.

## Why this is compatible with the operational contract

Every owner is activated while its event is ready at clock zero, so the
reaction obligation is satisfied. A clock-zero send is protected:
$0+1<0+2$. When such a send occurs, the controller provides its accepting
receipt at clock one, before the clock can pass its bound. Foreign packet
traffic does not void the owner's sole-identifier protection.

A clock-one send is timely but unprotected: it is before deadline two, while
$1+1<0+2$ is false. At clock two, the strict receipt antecedent
$1+1<2$ is still false. Expiry at that clock completes the event; thereafter
the protected-inclusion implication has no unfinished event to cover. Thus
the late lottery does not violate sole-packet protection. All events finish
by the horizon.

The calls use the same valid readiness episode and immutable payload in both
turns. No duplicate, replacement or future-event credential is needed.
Before its first call, the clear risk menu permits a conformant canonical
opening even after `InclusionFitsDeadline` becomes false. An accepted late
opening can therefore be both a retained action and audit-clean. After it
sends, the owner can stay silent. The extra activation does not require a
second submission.

An actual all-RAW scheduler additionally needs definitions for malformed,
foreign, relayed and duplicate packets. One natural extension records those
inputs, provides the contract-required receipts for sole owner packets, and
selects canonical valid calls for the lottery; it can include other packets
after settlement without changing the source publication result. Verifying
this extension's all-history contract, native information fibers, and optimal
RAW normalization remains an adapter obligation. The finite comparison and
its no-preserving-SE result below do not silently discharge that obligation.

## The unique initialized sequential outcome is all-late

First consider a continuation where at least one early opening exists. At the
final late owner opportunity, its canonical call succeeds surely. Silence
loses $D$, with no possible base-payoff improvement above $W<D$. Thus it
opens. Backward through the remaining late opportunities, all missing owners
open and all publications succeed. Each player receives zero.

Next consider a continuation with no early opening. At the final late owner
opportunity, sending changes only its own failure probability, from one to
$\varepsilon$; its base payoff depends on other failures. Sending improves
its expected payoff by $(1-\varepsilon)D>0$. The same comparison propagates
backward: all missing owners send late. Independent failures then give each
player expected payoff

$$
V=W(2\varepsilon-\varepsilon^2)-\varepsilon D
 =\varepsilon\bigl(W(2-\varepsilon)-D\bigr)>0.
$$

At the last protected opportunity, if no earlier owner sent, opening early
triggers all-success and payoff zero. Waiting leads to the just-derived
all-late continuation and payoff $V>0$. It therefore waits. The preceding
protected owner knows this and likewise prefers waiting when the earlier
history contains no early opening. Backward induction reaches the first owner:
all three wait and then send late in every SE.

Consequently no SE of this finite comparison preserves the all-success source
law. The probability of at least one failed publication is
$1-(1-\varepsilon)^3>0$. This failure does not rely on concealed dropped
contents: all three packets remain publicly observable. The first controller
regime changes the other owners' inclusion law, which changes the sender's
base payoff even though its own value cannot change.

All-early remains a Nash profile if its off-path policies also keep opening
early. A unilateral delay cannot produce the no-early regime while those
other policies remain fixed. SE removes those particular off-path policies:
after earlier owners waited, later owners strictly prefer the all-late
continuation. The distinction is credible transport timing, rather than a
new strategic commitment or guess value.

For example, $W=1$, $D=3/2$ and $\varepsilon=1/10$ give $V=1/25$.

## Complete audit and the exact finite comparison threshold

Now use an authentic complete settled-input audit, with one escrow $E\ge0$
per owner. A sole accepted opening is permitted; a sole late opening that
expires has no accepting receipt and is forbidden. Complete collection
therefore charges $E$ precisely on its failed late emission. Never sending
has no submitted packet to audit, but still incurs its intrinsic own failed
reveal forfeit. This calculation concerns the first-only comparison; it is
not a claim that the charge is constant after arbitrary earlier RAW inputs.

If the no-early late continuation sends, its payoff is

$$
V_E=\varepsilon\bigl(W(2-\varepsilon)-D-E\bigr).
$$

At a late decision, sending rather than never sending improves payoff by

$$
\Delta_E=(1-\varepsilon)D-\varepsilon E.
$$

The sign is independent of the other owners' choices. Thus every late owner
sends when $\Delta_E>0$ and never sends when $\Delta_E<0$; either is locally
optimal at equality. If they all never send, each gets $W-D<0$.

Put $E_*=W(2-\varepsilon)-D>0$. Its value is strictly below the late-send
switch point $D(1-\varepsilon)/\varepsilon$, since
$D>W\varepsilon(2-\varepsilon)$. Hence:

- For $E<E_*$, the previous strict all-late cascade survives; there is no
  preserving SE.
- For $E=E_*$, an all-early preserving SE exists, and an all-late SE also
  exists. The latter gives payoff zero but has positive publication failure.
- For $E>E_*$, the final protected owner strictly prefers opening when no
  earlier opening exists. If later sending is optimal its all-late payoff is
  negative; if never sending is optimal its payoff is at most $W-D<0$.
  Earlier owners may wait or send, but some protected owner opens. All
  publications then succeed in every SE of this comparison.

For the numerical example, $E_*=2/5$. This is an explicit reason to distinguish
the bare asynchronous contract and intrinsic forfeits from the audited
large-deposit preservation problem.

## Heterogeneous or correlated failure risks

There is also a useful aggregate bound for this controller family. Replace
the independent common lottery by an arbitrary joint failure vector sampled
after the late decisions, with fixed marginals $f_p$ for valid late calls.
A missing call fails, without changing the vector's other coordinates.
Allow different widths $W_p$, forfeits $D_p>W_p$ and complete-audit escrows
$E_p$. An early opening still triggers the all-success continuation.

At a late decision, the send-versus-never difference is
$(1-f_p)D_p-f_pE_p$, independent of the other owners' choices. If that
difference is nonpositive, its optimal late continuation costs the owner
at least $D_p$, so its payoff is at most $W_p-D_p<0$. That owner cannot
choose waiting at its protected opportunity along a positive-probability
no-early SE branch. Hence any such branch must emit at every late opportunity.
For every owner on it, comparison with early opening requires

$$
0\le W_p\Pr(\text{some other failure})-(D_p+E_p)f_p
 \le W_p\sum_{r\ne p}f_r-(D_p+E_p)f_p.
$$

Branches where a later owner instead opens early pay zero, so their probability
does not change this inequality when the no-early branch has positive probability.

Summing would require

$$
\sum_r\left(D_r+E_r-\sum_{p\ne r}W_p\right)f_r\le0.
$$

If $D_r+E_r>\sum_{p\ne r}W_p$ for every $r$, a no-early equilibrium
continuation with positive failure is impossible. Zero-risk pivotal owners
do not evade this aggregate inequality: the owners whose events actually
fail still carry their corresponding liabilities. Thus heterogeneous risks
and correlation alone do not give an obstruction for every finite escrow in
this particular controller family.

This bound does not apply to an arbitrary scheduler. Its primitive repair
property is that one early call makes every later valid call succeed, and its
fresh-call menu gives the resulting zero-payoff continuation by backward
rationality. General controllers need a derived liability-to-externality
bound, or another argument. A component can influence other failures while
having zero incremental own liability; a uniform ratio cannot be inferred
from `AsyncContract` alone. Persistent one-time audit escrows also cannot be
treated as fresh penalties after an owner already became liable.

The actual-language lesson is limited but useful: immutable read-only values
remove a major information-choice difficulty, while public scheduling can
still couple publication incentives. Large authentic collection may repair
that coupling. Neither a general actual-runtime impossibility result nor an
audited `RevealOnly` SE preservation capstone is established by this note.
