# Auditable fees and public fee policies

Analysis by Codex. Auditable fee choices are useful evidence. They do not require
a blockchain to force every transaction to pay one amount. The useful candidate
is a publicly specified bidding rule, with an incentive argument for following
it. This note gives paper comparisons, not an adopted fee mechanism or a native
SE theorem.

## A fee rule is different from a fixed paid fee

Distinguish the sender's signed bid or cap, the effective price on inclusion,
and the total execution bill. For EIP-1559 transactions, the signature covers
the maximum fee and maximum priority fee. The included block's base fee affects
the effective price; actual gas consumption determines the bill. The EVM's
GASPRICE reports the effective price, rather than all signed bidding fields.
Thus fixing a bidding rule need not fix the numerical payment.
[EIP-1559 specification](https://eips.ethereum.org/EIPS/eip-1559).

A consequence of that specification is that two sufficiently high maximum
fee caps with the same priority bid can produce the same effective price.
Their distinct signed caps can still be visible. Checking only the paid amount
therefore need not control every fee-field signaling choice.
[Fee calculation](https://eips.ethereum.org/EIPS/eip-1559).

A candidate rule can specify a priority bid and funded cap as functions of
public information available when submitting. The resulting actual fee may
vary. A theorem must identify the evidence used to check the rule and establish
that this public information is genuinely available. A signed bid proves
authorization; an audit premise must additionally establish the submission or
execution relevant to its charge. The current settled audit is not silently
extended by describing fees as auditable.

There are three separate obligations:

- The rule and its visible metadata must preserve the source's information.
  A fee computed from a private receipt can disclose that receipt. Gas use or
  refunds depending on a hidden value can disclose it even with a canonical bid.
- Service analysis must account for the rule and every allowed alternative bid,
  including effects on other players' guarantees. Detecting a high bid does not
  prevent its prior inclusion or disclosure.
- The costs and collectible penalties must make the relevant alternatives
  unprofitable, with consistent equilibrium completion off the intended path.

## A conditional enforcement comparison

**Model for this result.** Use a finite perfect-recall expanded game with additive
monetary utility. A retained game follows a canonical public bidding rule and
has no audit charges. Its transitions and observations match the declared
source, including any fee costs assigned to that source. Every target terminal
base reward lies in [L,U]. Every retained terminal total fee bill is at most F;
all target fee bills are nonnegative. These bounds include deviations and
off-path histories as required by their respective interfaces.

At every clean retained decision history, every first noncanonical fee action
creates authentic persistent evidence. Under every subsequent joint policy it
causes a **fresh additional** charge K with probability at least alpha>0.
The charge covers successful included departures as well as excluded ones.
Players can fund the charge. Capital costs, nonlinear wealth utility, entry,
strategic miners and unmodeled communication are outside this comparison.

**Paper lemma.** A public bound

\[
K\ge\frac{U-L+F}{\alpha}
\]

makes every such first departure no better than the available retained
continuation. Strict inequality gives a strict comparison. The collateral is
chosen from these public bounds before selecting the builder and source SE.
The bounds hold across the declared builder class; they are not calibrated to
the selected producer's law. The hidden-history comparison also survives
averaging over any compatible posterior about a hidden builder type.

**Proof.** Whatever follows the departure, its expected net utility is at most
U-alpha K, since fee bills are nonnegative. A retained continuation pays at
least L-F. The displayed bound compares these two quantities. The comparison
holds at each compatible hidden history, hence under every belief there. Gains
from changed ordering, better inclusion or signaling are covered by the base
reward range rather than assumed absent. Past sunk fees can be omitted from
both conditional continuations under additive utility. QED.

This is an incentive lemma. An SE extension additionally requires a structurally
faithful retained game and a common consistency/completion argument, as in
[the existing first-departure route](service-and-enforcement.md). It does not
make leaked information disappear. It does not prove the collector obtains
the assumed evidence, or that the computed collateral is affordable.

A penalty imposed only when a packet fails is insufficient for this lemma:
a higher bid might obtain certain inclusion and make its additional collection
risk zero. An already exhausted capped penalty also provides no fresh charge.
Auditability supplies a potential basis for a fee-policy offence; it does not
by itself supply the required collection guarantee.

## Variable fees need not enter source syntax

Once the canonical policy's information and service obligations hold, its
actual costs can be treated at the utility boundary. If its expected total
fee is independent of every own continuation policy at every information set,
with the belief and opponents' continuation policies fixed, the fee cancels
the continuation comparison. A bound on fee variation instead
gives a regret bound, not automatic exact SE preservation. The
[cost note](costs-and-scope.md) proves both comparisons and explains the
conditions for an exact strict-margin result.

A flat funded service is another explicit contrast. Suppose the player pays
P before entry and receives the same rebate r at every retained terminal
outcome. A nonstrategic service covers all actual retained fees, bounded by
F<=P-r, and keeps or burns the remaining surplus. The player's net fee cost
is the constant P-r in additive utility. This gives exact cancellation after
funding, even though the service pays variable transaction fees. Refunding the
actual unused balance instead leaves the player's cost equal to actual fees,
so it need not cancel. Service funding, uninterrupted execution, participation,
capital timing and the service's incentives are additional premises; this is
not a claim about an available native backend.

The high-level language can therefore omit individual gas bids while its
theorem states a fee policy and utility convention. A public cap or interval
alone generally leaves several controlled bids. Those choices still belong
to the target's action space unless an extension argument deals with them.

## When fee cost alone removes an alternative

**Limited paper lemma.** In a finite additive-utility game, the sender makes
one fee choice and has no subsequent owned decision. All choices have identical
conditional inclusion probability q>0 and identical expected nonfee deductions.
Only an included call pays its selected actual fee f. The sender's base reward,
under every receiver response and terminal outcome, lies in an interval of
width W. The receiver may observe the fee and respond differently to it.

For any fixed full opponents' response policy, two choices satisfy

\[
V(f_h)-V(f_l)\le W-q(f_h-f_l).
\]

**Proof.** Both expected base rewards lie in that interval; their difference
is at most W. The identical expected nonfee deductions cancel, and the expected
fee difference is q(f_h-f_l). QED. Thus q(f_h-f_l)>W makes the higher fee
strictly dominated, even allowing arbitrary fee-induced signaling responses.
A public conditional lower bound q_min permits the same comparison with
q_min(f_h-f_l)>W before the builder is chosen.

This is a genuine reduction of a fee menu in this small interface, without
an audit fine. It requires the conditional bound at every relevant decision,
including off path. It excludes changed admission, retries and further sender
choices. The price f is the actual accepted payment; raising an unused signed
cap does not necessarily raise it. It is not a full bidding-menu preservation
or native-runtime theorem.

## A controlled fee can be a message even with identical inclusion

**Complete finite paper example.** Nature draws a fair bit b, known only to
Alice. Bob guesses it before Alice's final Open/Withhold decision. Both receive
one for correctness. Withholding deducts D>1 from Alice. In every source SE
Alice opens and correctness has probability one half.

Add a target choice before Bob's guess: Alice chooses Low, fee zero, or High,
fee kappa with 0<kappa<1. Both have identical certain inclusion, validity and
publication rights. The public bid identifies the choice. The fee is deducted
from Alice in additive utility and is sunk by her final opening decision.

There is a separating target SE: bit zero chooses Low; bit one chooses High;
Bob guesses zero after Low and one after High; Alice opens. Type zero prefers
utility 1 to -kappa. Type one prefers 1-kappa to zero. Bob's conditional guesses
are strict. Have each type tremble to the other bid with the same vanishing
probability, Bob tremble to the wrong guess, and Alice tremble to withholding.
Bayesian posteriors after the two bids converge to the claimed bit beliefs.
This is one fully mixed consistency witness. The new equilibrium has correctness
one, which no source SE has.

This disproves reflection for this interface. It does **not** disprove forward
preservation: pooling on Low can support source guessing policies with suitable
consistent off-path beliefs. The point is that a player-controlled fee is an
additional signaling action, even if its admission consequences are identical.
It is not exogenous auxiliary randomness to which the
[observation-channel theorem](observation-abstraction.md) automatically applies.

## Consequence for the honest-producer comparison

The [one-slot producer negative](honest-producer-models.md#candidate-two-one-opening-slot-and-maximum-fee-revenue)
uses a fixed bid as a restricted comparison assumption. Its fee normalization
incorporates the actual accepted-call cost; it does not establish that real
players have only one bidding action. With several bids below every competitor,
sole-call success can still equal 1-epsilon. That service calculation alone
does not extend the SE negative: bid signals, costs and retry selection change
the strategic game. Bids above competitors also invalidate that failure bound.

The useful next question is whether an auditable public fee policy, or a broader
source-equivalent fee menu, admits an extension theorem for the actual runtime.
A fixed paid fee need not be an assumption of that theorem. A general claim
must still say whether fee departures are charged, costs cancel or are bounded,
and priority and information effects have been covered. The producer comparison
and the fee-policy extension are different interfaces until those adapters are
proved.

The enforcement bound, utility conventions and signaling example have received
independent mathematical review. They remain paper results; no fee-policy
adapter or native collection theorem is supplied here.
