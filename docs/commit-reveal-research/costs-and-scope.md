# Costs and omissions in commit–reveal preservation

Analysis by Codex. This note gives finite-game paper results and explicit
modeling choices. It does not change the language, current runtime, or SE
checklist. None of the new results below is a Lean theorem.
The utility and bounded-wait arguments and the counterexamples have received
independent mathematical review; they remain paper proofs.

A high-level game need not describe packet processing. It does need the
economic choices and information that affect its players. Some implementation
details can be erased without changing incentives; other details can be
bounded, or require an explicit exclusion from the theorem's scope.

Throughout, an assessment consists of a behavioral strategy and beliefs.
SE means sequential rationality against every whole remaining policy, plus
one Kreps–Wilson consistency sequence. Games are finite and have perfect
recall. Logical outcome comparison includes the declared initial private
parameters, rather than just an unconditional public output distribution.

## Costs that can be erased exactly

**Positive affine utility changes, paper proposition.** On the same game tree,
with the same observations, menus and chance kernels, replace each player's
terminal utility by

\[
u_i'(z)=a_i u_i(z)+b_i,\qquad a_i>0.
\]

Here both constants are fixed for that player across all terminal histories.
Exactly the same assessments are SE, weak PBE and Nash equilibria. Their
logical laws are unchanged; their numerical utilities are transformed.

At every information set, every continuation payoff difference is multiplied
by the positive number \(a_i\). The additive constant cancels. Consistency
uses strategies and chance probabilities, so it is unchanged. This proves the
claim, including unreached information sets. A compulsory fixed fee can be
erased when it is an additive constant in utility units on this entire game;
exact numerical payoff preservation still requires recording that fee.

This proposition is about **utility**, not necessarily cash. Writing
\(u=b-KA-f\) treats money as additive utility, usually a quasilinear monetary
model. An arbitrary expected-utility model over wealth need not have that
form. Source utilities may themselves represent risk attitudes, but that
does not justify adding target cash deductions to them without an adapter.

**A fixed cash fee can reverse a unique equilibrium.** A single player chooses
Safe, giving terminal wealth 2, or Lottery, giving wealth 1 or 4 with equal
probability. Its utility is the square root of terminal wealth. Source utility
is \(\sqrt2\) for Safe and \(3/2\) for Lottery, so its unique source SE chooses
Lottery. Charge an unavoidable cash fee 1 after either action. Target utility
is 1 for Safe and \(\sqrt3/2\) for Lottery, so the unique target SE chooses
Safe. All wealth levels remain nonnegative. The interface and chance kernel
are unchanged, yet no target SE implements the selected source action law.
This is a complete one-decision counterexample, not just a failed comparator.

There is a sharper cancellation test than requiring a globally constant cost.
Fix an assessment, a player's information set \(I\), its belief \(\mu_I\), and
the opponents' continuation policies. Suppose an extra total cost \(C\) has
the same conditional expectation under **every** own continuation policy:

\[
\mathbb E[C\mid I,\pi_i,\sigma_{-i},\mu_I]=c_I.
\]

Then subtracting \(C\) changes none of that player's continuation comparisons
at \(I\). If this holds at every player's information set, a source SE
assessment remains an SE on the same tree after the costs are added. The
beliefs and their consistency sequence are unchanged. The test must include
whole continuation deviations, not merely the current action with a fixed
future policy.

A sufficient way to prove the test is to show, at each compatible hidden
history, that the cost's expected continuation value is independent of the
player's future policy. Averaging over any belief then preserves equality.
Past fees already irrevocably paid satisfy this condition as sunk costs under
additive utility, even when their values differ between hidden histories.
Future fees do not satisfy it merely because a tariff is called fixed: a
deviation may change the number of payments, opponents' responses, expiry,
or the refund time. This cancellation result assumes unchanged information
and opportunities; publishing a receipt can change the game separately from
charging its fee.

## Costs that can be bounded

**Same-tree payoff perturbation, paper lemma.** Keep the entire finite game
tree, chance kernels and information partition fixed. If

\[
\sup_z|u_i'(z)-u_i(z)|\le\eta_i,
\]

every source SE assessment is an exactly consistent target assessment with
whole-continuation regret at most \(2\eta_i\) at every information set.
Indeed, the prescribed payoff and each deviating payoff change by at most
\(\eta_i\); the original comparison was nonpositive. Initialized logical
law is exactly unchanged. No positive reach probability is needed for this
bound, because the belief is unchanged and the terminal bound is pointwise.
The conclusion is approximate rationality, not a nearby exact target SE.

For additive costs \(C_i\in[c_i^-,c_i^+]\), the sharper regret bound is
\(c_i^+-c_i^-\): the deviator's cost saving cannot exceed that interval's
width. A common unavoidable constant therefore gives zero incentive error.
Bounds on honest expected fees alone do not bound fees after deviations or
at unreached information sets.

Vanishing costs cannot generally preserve every selected exact equilibrium:
two source actions tied at payoff 1 cease to be tied when one costs
\(\varepsilon>0\). The pure costly source action has no exact target
implementation, although copying it has regret \(\varepsilon\) and zero
logical-law error. The full counterexample and stronger strict-margin results
are in [preservation-and-robustness.md](preservation-and-robustness.md).
Changing chance support or observations requires its separate consistency
argument; this elementary payoff lemma does not supply it.

## A compact discounted bounded-wait model

The following interface is deliberately small. It provides a quantitative
result about public waiting, not about arbitrary blockchain traffic.

Each player has additive discounted monetary utility, discount factor
\(0<\beta_i\le1\), and a fixed escrow \(K_i\ge0\). Fund the escrow at time
zero. At settlement, receive a bounded reward \(b_i\), with
\(|b_i|\le B_i\), and a refund \(K_i(1-A_i)\), where
\(A_i\in[0,1]\) is the confiscated fraction. There are no intermediate reward
payments, additional funding choices, or outside opportunities. Wealth and
credit permit the compulsory funding; participation is addressed separately
below. The nominal terminal utility is

\[
u_i^0=b_i-K_iA_i.
\]

Pad the source to settle at a fixed logical horizon \(L\), independent of
actions. Including funding and discounting, its utility is

\[
u_i^L=-K_i+\beta_i^L[b_i+K_i(1-A_i)]
      =\beta_i^L u_i^0-K_i(1-\beta_i^L).
\]

Thus this fixed-horizon source has exactly the nominal source equilibria by
positive affine invariance. A path-dependent source settlement time would not
give this conclusion.

Let the target be the public-wait expansion from
[public-scheduling-se-preservation.md](../public-scheduling-se-preservation.md):
waits are chance moves; the scheduler uses only recoverable source-public
history and its public auxiliary transcript; logical actions, primitive
source chance transitions and information are preserved. The retained
interface has no player-controlled retry, fee-priority, admission gamble,
or new signaling action. The implementation settles at \(L+W\), where every
legal history, including deviations, has \(0\le W\le H\).

Charge an additional terminal fee \(0\le f_i\le F_i\), and, if specified, a
financing bill \(\lambda_i K_i W\), with \(\lambda_i\ge0\). Both are measured
in time-zero utility units. The financing bill is an explicit additional
cash expense; omit it if discounting is the entire capital-cost model. Then

\[
u_i'=-K_i+\beta_i^{L+W}[b_i+K_i(1-A_i)]
       -f_i-\lambda_iK_iW.
\]

These bills are terminal payoff records and introduce no additional choices,
observations, or interim liquidity constraints. Exposing a new private fee
signal or requiring another funding decision would change this interface.

All constants and bounds are fixed before the builder and selected source
equilibrium. Define

\[
\eta_i=\beta_i^L(1-\beta_i^H)(B_i+K_i)
                  +F_i+\lambda_iK_iH.
\]

**Bounded-wait preservation, paper proposition.** Every source SE has a target
assessment with exact consistency, exactly the same logical terminal law,
whole-continuation regret at most \(2\eta_i\), and expected utility error at
most \(\eta_i\) relative to the discounted fixed-horizon source. This applies
uniformly to every public-wait scheduler satisfying the stated bound \(H\).

To prove it, first apply the public-wait preservation theorem with terminal
payoff \(u_i^L\). It supplies an exact preserving target assessment. At every
expanded terminal history,

\[
|u_i'-u_i^L|
\le \beta_i^L(1-\beta_i^H)(B_i+K_i)+F_i+\lambda_iK_iH.
\]

The first term follows from
\(|b_i+K_i(1-A_i)|\le B_i+K_i\) and
\(0\le1-\beta_i^W\le1-\beta_i^H\). Apply the payoff-perturbation lemma on
this expanded tree. Keeping its assessment keeps exact consistency and
logical law; averaging the pointwise bound proves utility fidelity. The
argument includes arbitrary adaptive correlations between waits and public
logical outcomes. It does not permit waits to disclose a hidden source fact.

There is an exact version with a substantive margin assumption. Suppose the
selected source SE is pure, and at every source information set its chosen
action exceeds every other pure action, followed by the prescribed source
policy, by at least \(\gamma_i>0\) in nominal utility. If

\[
2\eta_i<\beta_i^L\gamma_i,
\]

the lifted assessment remains an exact target SE with the same logical law.
The public-wait continuation and belief identities transport each one-action
margin as \(\beta_i^L\gamma_i\). Perturbing the two compared payoffs loses at
most \(2\eta_i\). All such local comparisons remain strict, and the finite
perfect-recall one-shot-deviation principle with consistent beliefs gives
whole-policy rationality. This claim covers every copied decision and all
legal source histories; initialized strictness alone is insufficient. Mixed
or tied equilibria need not have such a margin. The result supplies no exact
completion theorem for extra raw actions or newly added player sites.

The estimate explains why logical and physical horizon must be distinguished.
Padding to a fixed logical endpoint makes source discounting an affine
transformation. Random physical waits change the amount discounted and may
be action-dependent. A failure to settle by a fixed physical deadline is a
new terminal event; it cannot be erased as waiting. Large collateral also
enlarges \(\eta_i\). Increasing \(K_i\) does not automatically improve the
combined enforcement-and-capital-cost calculation. An expected-wait bound
only under honest initialized play cannot replace the pointwise \(H\) above.

## Omissions that require a different game or an explicit scope limit

| Omitted feature | What the small model must say |
| --- | --- |
| Entry, funding and affordability | Players are already participating and can finance the prescribed collateral, or entry/credit choices are included. A fee constant after entry need not be constant at an earlier entry decision. |
| Fee bidding and resource competition | Fee menus and load are bounded, and the service guarantee covers all allowed actions jointly. Otherwise changing a fee may change ordering, admission, or others' outcomes, rather than merely subtracting a cost. |
| Strategic miners or sequencers | Scheduling is exogenous Nature within a specified public class. A miner who chooses censorship, bribes, or order is an additional strategic player; noncollusion alone does not give a probability kernel or independence. |
| Capital and interim utility | Settlement and refund timing follow the explicit cash-flow model. Time-dependent outside opportunities and action-dependent early release require additional utilities and comparisons. |
| Outside communication and trades | Only specified channels and payoffs are available. A contract's packet audit does not punish an off-chain disclosure or a profitable external position without an explicit mechanism. |
| Computation and bounded rationality | Ordinary finite-game SE permits every observation-local continuation policy, without computation cost. Cryptographic or computational restrictions require a security parameter, adversary class, utility convention, and suitable equilibrium notion. |
| Rollback and incomplete execution | Finality and failure readouts are specified on the whole deviation tree. A logical readout coupling cannot erase leaked information from a subsequently reverted block. |

**Participation counterexample.** A source game gives one already committed
player a compulsory payoff 1, so its unique logical outcome is execution.
A target adds a voluntary entry move: Out pays zero; In executes the same
program but charges a fixed utility fee 2. The unique target SE chooses Out.
Conditional on entry, that fee cancels every continuation comparison, but no
target SE preserves execution. The additional participation choice is the
reason; the source conditional game did not promise an entry theorem.

**Delay counterexample.** One player chooses A for nominal reward 2 or B for
nominal reward \(3/2\). Source A is the unique SE. Target A is paid one period
later and B immediately, with discount factor \(1/2\). Target payoffs are
1 and \(3/2\), so B is the unique SE and selected-outcome preservation fails.
Menus and observations need not change for an omitted delay to change the
answer. This does not contradict the bounded-wait estimate: its small-error
or strict-margin condition is not satisfied.

Even under additive utility, a deviation can save capital cost as well as
avoid a deduction. For fixed comparison kernels, if collection risk increases
by \(r\), expected lock-time decreases by \(\Delta T\), and the other base
gain is \(g\), linear capital rent yields net gain
\(g-K(r-\lambda\Delta T)\). A positive collection bound alone is insufficient
when the saving cancels it. See the fuller conditional analysis in
[service-and-enforcement.md](service-and-enforcement.md).

## Constants, knowledge and approximation outputs

Let a public descriptor \(B\) specify payoff range, funded collateral budget,
load, allowed fee actions, physical horizon, collection guarantees and the
cost parameters actually used. Choose the compiler configuration \(C(B)\)
before selecting a builder from its declared class and before selecting a
source SE. A theorem
\(\forall S\in\mathcal S(B)\;\forall A\;\exists A'_S\)
may use different target strategies and beliefs for different fixed builders.
It is not automatically one implementable policy for players who know only
\(B\). The public-wait lift itself ignores the auxiliary transcript; audited
off-path completions need not have that stronger uniformity.

Unknown persistent builder behavior should be represented by a builder type
and a common prior, with the actual observations determining learning.
Conditional guarantees proved for every hidden history and every builder type
survive averaging under any posterior. An unconditional average service rate
need not survive conditioning on a rare signal. If players have only a set of
possible laws and no common prior, ordinary Bayesian SE has not yet been
specified. Noncollusion is not a replacement for this choice.

Report three approximation outputs separately: logical-law TV error,
whole-continuation regret in specified utility units at every information set,
and utility fidelity under an explicit coupling. In the bounded-wait result
they are respectively zero, at most \(2\eta_i\), and at most \(\eta_i\).
There is no bound on TV distance between exact numerical payoff laws: even
an arbitrarily small deterministic fee can move a point mass to a disjoint
point. The checked abstract public-scheduling construction and the separate
paper robustness results are discussed in
[preservation-and-robustness.md](preservation-and-robustness.md). A concrete
commit–reveal runtime still needs its action, information and settlement
adapters before any of these conditional applications becomes a compiler
theorem.
