# Immutable openings with several delivery decisions

Analysis by Codex. This note removes the one-late-callback restriction from a
paper SE-preservation result. After deferring an opening, its owner may make
many delivery decisions: send, wait, retransmit, or use another permitted
command for the same immutable opening. The owner can privately learn about
delivery conditions. Pending plaintext remains readable.

The main restriction is utility at failed publication. Failure terminates all
payoff-relevant play, and the controller's failure utility is independent of
the delivery route. Successful delivery advances the source game without
additional transport charges. The controller consequently wants to maximize
delivery probability, regardless of its other private game information.
That common objective permits a transport policy whose timing does not signal
retained private types.

This is a complete paper theorem for a proposed finite interface. It does not
establish preservation for VegasCore's full raw actions or its actual
mode-dependent audit. In particular, treating a retransmission as free after
success is a different accounting convention from charging an unaccepted
duplicate packet.

## Source game and physical interface

**Source game.** Fix a finite perfect-recall game with a public fixed serial
instruction sequence. Nature can initialize correlated private types and
bindings. At each binding decision, its owner chooses any admitted typed value
and binds it successfully. Every opening has one mandatory effective action:
publish the immutable bound value. Its owner knows that value and can produce
its authentic canonical packet. Source chance instructions draw public
outcomes from the declared source-public context. Remove unsupported chance
edges. Every terminal utility is in [0,R_i].

Private types and other unopened values may persist across many phases.
Players' later binding decisions and payoffs are unrestricted within this
finite source class. Arbitrary lawful withholding, rejected TRUE actions,
secret-dependent instruction schedules and failed source bindings are not
included.

**Protected source actions.** Bindings use one canonical opaque envelope at
their first protected opportunity. Their menus cover every legal source
value and admission is certain. The envelope, handle allocation and public
receipt do not depend on the private meaning. Its owner remembers its value.
No extra private preparation, alternative encoding, or late binding choice
is available in this interface.

At a mandatory opening, its owner can choose protected Open, which surely
publishes and advances the source instruction, or Defer. Defer enters the
delivery process described next. Every other physical response outside that
process is forced silence. All processing ends within the declared finite
physical horizon on every legal history.

**Delivery process.** While this opening remains unresolved, its owner alone
has non-singleton physical menus. It may have any finite sequence of owned
Send, Wait, Retry or other permitted delivery choices, with intervening chance
processing. Every transmission concerns the same immutable opening value and
canonical evidence. The menus may depend on the owner's complete operational
observations and recall. They cannot create a new binding value, expose another
unopened value, or communicate arbitrary retained private data in an additional
packet field. Other players may observe packets and receive private samples,
but they have no genuine strategic choice before this opening resolves.

The process is a finite partially observed control problem. Its underlying
service state need not be known to the owner. Delivery observations can be
private, correlated over time, and informative about that service state.
Success publishes the immutable value and enables the next source instruction.
Failure, including a deadline or deliberate abandonment, terminates every
further payoff-relevant game action. Success probabilities can be zero or one;
there is no lower success bound for a deferred process.

**Primitive information restriction.** Write p for the complete public source
prefix before this opening, and v for its immutable value. Operational state
is initialized independently of private source inputs and of future source
chance draws. Public service inputs, control menus and chance kernels depend
only on p, v when available, and operational records. Source binding meanings
enter no public packet before opening. Private passive samples enter no
service input. An owner has its original logical private information plus
its complete operational observation and action recall, denoted W.

Two executions with the same p and v but different retained private source
data therefore have identical operational dynamics under the same policies
based on p, v and W. This must hold across *different* private information
sets of the owner, not just histories in one information set. Earlier opening
values that affected prior processing are in p. Canonical identities, counts,
receipts and full histories are part of those operational records; equality
of only the latest application state is insufficient.

Logical chance has its source law conditional on every full physical record.
No service observation predicts a later logical draw beyond the source-public
information. Success retains the source observations and state transition
regardless of the route, wait or retry count. Ideal opacity and authenticity
are assumed; secret-dependent sizes, bills, credentials or decoder side
channels would require a new coupling argument.

**Utility and failure settlement.** Every history with no publication failure
has exactly its source utility, even if an earlier opening succeeded after
several retries. There are no additional successful-transport deductions.
If i's current delivery process fails, its entire terminal game utility is
the fixed amount -D_i, for a funded D_i>=0 selected before the service.
This amount is the same after every control policy, route, observation,
retry count and failure mode. Other players' abort utilities can be any fixed
bounded terminal functions: they make no further strategic choice.

These are absorbing utility outcomes, not a requirement that players forget
opening material or stop physically communicating. Fees, delay preferences,
financing, wealth-dependent menus, participation, outside trades, coalitions,
other communication rewards and strategic producers are excluded. If later
physical communication affects modeled utility, failure is not absorbing.
The source horizon alone does not establish these physical or cost assumptions.

## Paper preservation theorem

Fix the source/interface descriptor and failure utility amounts D_i>=0 before
choosing the service. For every service satisfying the complete interface and
every selected source SE, there exists a target SE with the same joint law of
initialized types, erased source terminal histories and realized source utility.

Its protected binding decisions copy the source policy and its opening roots
choose protected Open. At all off-path delivery sites, a policy based only on
p, v and operational recall maximizes conditional eventual delivery probability.
Such a policy can be completed consistently at every delivery information set,
including ones that have zero probability in the limit. No initialized failure
or deduction occurs.

The failure amounts are fixed before the builder, but the off-path optimal
delivery policy can depend on the service law. Full beliefs also depend on that
law. This is pointwise existence over a service class, not one prior-free
policy under unknown inclusion laws. A common policy follows under the
additional delivery-dominance condition below. The theorem is forward
preservation; it does not reflect every target equilibrium or prohibit timing
from supporting other equilibria.

The construction below proves the operational policies and their beliefs
together. It does not choose arbitrary POMDP posteriors independently in each
phase. No native raw or audit adapter, computational refinement, or capital
feasibility theorem is claimed.

## Why a delivery-only policy can ignore other private types

At a full control information set, let I be the owner's original source
information and let W be its operational recall. Until resolution there is no
new logical source move, so I remains the information for this mandatory
opening. Let V_i(I) be its expected source continuation utility under the
selected source policy, after successful publication and subsequent protected
transport. This is in [0,R_i].

The information restriction makes the conditional service-state law given
(I,W) the same as the law given the operational context (p,v,W). Thus for
any current action followed by a fixed operational continuation, if q is its
conditional probability of eventual success, its original expected utility is

\[
qV_i(I)-(1-q)D_i=q[V_i(I)+D_i]-D_i.             \tag{1}
\]

The nonnegative multiplier V_i(I)+D_i means that maximizing q is optimal
for every retained private type sharing p and v. When both terms are zero,
all delivery actions tie and a delivery-maximizing choice remains optimal.
Positive D_i makes the ranking strict whenever the success probabilities
differ, but exact preservation does not require that strictness or a positive
lower success bound.

This is why type-independent control is possible. It would not follow merely
from equality of service posteriors inside one owner's source information
set: choosing different delivery policies for different retained types could
signal those types to a later receiver. The operational process and objective
permit the same policy across those private information sets.

## Successful-prefix coupling with many physical choices

Choose one fully mixed source consistency sequence sigma_n tending to the
selected SE's strategy, with source Bayes beliefs mu_n tending to mu. At each
opening root, use Defer with the same probability epsilon_n>0 for every private
type and physical view, with epsilon_n tending to zero. At delivery sites use
a full-support policy rho_n that depends only on p, v and W. Its selection
is constructed in the next section; for this coupling argument fix any such
policy. Genuine source bindings use sigma_n and ignore physical auxiliaries.

Replay a fixed source prefix h, sampling the service, observations and control
lotteries while fixing only the past logical choices and chance outcomes in
h. Stop at the relevant source decision or control site. Paths that failed
earlier do not reach it. The resulting physical mass L_n(h,omega) is a
subprobability kernel and can depend on n. Actual reach probabilities factor as

\[
w'_n(h,\omega)=w_n(h)L_n(h,\omega).             \tag{2}
\]

Couple complete operational steps on equal inputs. Protected bindings emit
equal opaque envelopes and have equal receipts despite foreign hidden values.
For every preceding successful opening, its transmitted value is already in
the current source-public prefix. Its controls use the same p, that value,
and coupled operational recall, irrespective of its owner's other retained
private types. Hence their whole route, counts, retransmission identifiers,
receipts and passive samples have the same coupled law. Failed paths discard
the same mass. Logical chance factors belong to w_n and are not selected by
future physical outcomes.

This proves two needed statements by induction through the finite physical
tree. At a genuine source decision, every player's full remembered auxiliary
view has equal marginal L_n mass across its source information fiber. At a
control site, the joint law of the underlying operational record and W is
equal across all source histories sharing the current p and v. The owner's
other logical private information contributes no extra service-state signal.
All physical observations, including pending plaintext and absence, remain
in the coupling.

Bayes' rule in (2) cancels the common auxiliary mass at every genuine source
site and projects its target beliefs to mu_n. At a control site it also
factorizes the hidden source posterior and the conditional operational-state
law. The latter is the law obtained by observing p, v and W alone. Its
dependence on n is permitted; source projection still tends to mu.
Full beliefs, including singleton silent sites, are dealt with by one common
compact subsequence. No fixed normalized physical replay kernel is asserted.

## Constructing globally consistent delivery choices

For each n fix sigma_n and the positive root deferral probabilities. Form a
finite auxiliary game using the same source and physical tree as follows.
The initialized source variables, every source binding choice drawn from
sigma_n, source chance, root Open/Defer lottery, and service transitions are
Nature moves. Only the delivery-control choices remain strategic.

At each distinct operational control information set (p,v,W), introduce a
separate auxiliary agent. Its action menu is the actual controller's finite
menu. Its utility is 1 if this current opening eventually succeeds and 0
otherwise. If that information set is never reached, changing that agent's
action affects no outcome; it can receive the same indicator payoff there.
The agent sees no retained logical private data beyond p and v. The preceding
joint coupling proves that this omission removes no information relevant to
delivery at that node.

Full operational own-action recall ensures an agent's information set is an
antichain: no history in it precedes another history in it. An agent does not
choose twice on one play. Its payoff is therefore linear in its own action
lottery when all other agents' lotteries are held fixed. This removes an
absent-mindedness concern that would invalidate the simple agent construction.

Choose delta_n>0 tending to zero, smaller than the inverse of the largest
menu size. If there are no control sites, omit the auxiliary game and this
delta construction; the fixed delivery chance law already supplies its
continuation. Otherwise require every control action to have probability
at least delta_n.
These finite agent strategy sets are compact and convex. Payoffs are
continuous and linear in each agent's own strategy; the product best-response
correspondence has nonempty convex values and a fixed point. Choose such an
equilibrium rho_n. It is a full-support operational policy, common across
the original owner's retained private source types.

All legal auxiliary control information sets have positive reach: source
choices, root deferrals and control actions have full support, and supported
chance edges are positive. At a site with m actions, divide its agent's
equilibrium comparison by this positive pre-action reach probability. Since
the site is an antichain, that reach weight is independent of the agent's
current action. The result is a conditional comparison of eventual delivery
probabilities at that site's actual Bayes posterior.

For each pure alternative a, use the feasible lottery that gives probability
delta_n to every other action and 1-(m-1)delta_n to a. Its delivery probability
is within m delta_n of the pure alternative because all success probabilities
are in [0,1]. Agent optimality consequently gives

\[
q_n(a)-q_n(\rho_n)\le m\delta_n.               \tag{3}
\]

This bound is conditional and uniform. The information set's reach may tend
to zero; passing an undivided ex ante equilibrium inequality to the limit
would establish nothing there. The explicit division and (3) supply the
off-path comparison.

Use rho_n, sigma_n and the root lotteries as one fully mixed strategy in the
original target. Give every information set its actual global Bayes beliefs.
The projected operational-state posterior at an original control information
set (I,W) equals the auxiliary agent's posterior by the coupling above. Select
one common compact subsequence of all target strategies and full beliefs.
Its strategy limit rho_* still depends only on p, v and W. Its source binding
part is sigma and its root opening part is protected Open. Its beliefs are
globally consistent, with source projection mu.

Finite conditional continuation probabilities are continuous functions of
full beliefs and future behavioral policies. Thus (3) passes to the common
limit at every control site, even one with vanishing reach. It says that
rho_* is locally optimal for eventual delivery given the constructed
operational posterior and continuation. Within one unresolved opening the
controller has perfect recall and no other player chooses. The finite
one-shot principle therefore makes it optimal against every adaptive delivery
policy. This is a consistent solution of the full finite partially observed
problem; arbitrary separately chosen phase posteriors were not needed.

## Sequential rationality in the original game

At a control information set, compare any present action with rho_* and
continue using the limiting prescribed policy. After success every later
opening uses protected transport and source choices copy sigma. Conditional
on the full logical source history h, continuation utility is exactly its
source continuation S_i(h), independent of the physical success record.
Failure utility is exactly -D_i. The source and operational-state factorization
therefore gives (1). Inequality (3) in the limit, multiplied by
V_i(I)+D_i>=0, proves every original one-shot control comparison.

At a protected opening root, condition on any full hidden source/physical
history. Open has source continuation value S_i(h)>=0. Defer followed by
rho_* has value

\[
qS_i(h)-(1-q)D_i\le S_i(h).                    \tag{4}
\]

This is pointwise; q need not be known by the owner or constant across its
hidden physical histories. Protected Open is locally optimal. At a binding
site, every legal value has certain protected admission. Its erasure and
projected belief mu give the original source SE comparison. Other owned
sites have only silence, and abort leaves have no further choice.

All local comparisons hold in the single globally consistent assessment.
Finite perfect recall gives optimality against every whole adaptive target
policy, including one that uses retained private types when choosing waits
or retransmissions. Such dependence is permitted to deviations; it is the
constructed equilibrium and its consistency witnesses that use common
operational controls. Initialized play remains protected, so its source
transition law, terminal history law and source utility law are exact. QED.

## Mode-independent failure rewards can retain private types

The fixed utility -D_i is a useful simple case, not essential to the proof.
For the owner of a failed opening, allow F_i(h)<=0, a bounded function of
the current logical source prefix, immutable private types and bound value.
Require precisely this same utility after every failure route, policy,
observation, backend outcome and retry count. There is still no post-failure
strategic choice, and the success utility is unchanged.

The original control comparison becomes

\[
\bar q\,[V_i(I)-E_{\mu_i}F_i(h)]+E_{\mu_i}F_i(h).
\]

Its nonnegative multiplier again selects the same delivery-maximizing policy
for every retained type. Pointwise F_i(h)<=0<=S_i(h) gives the protected-root
comparison. All coupling and consistency arguments are unchanged. In
particular, a fixed failure gross reward r_i(h) in [0,R_i] and a uniformly
collected forfeit D_i>=R_i yield F_i(h)=r_i(h)-D_i<=0, with collateral fixed
before the service. Fundability remains an assumption.

The reward must not depend on the control route or later outside play. An
extra charge after failed Send but not after Never, a fee per retransmission,
or an observation-dependent abort reward violates this condition. Making
every failure payoff negative is insufficient to derive a common
delivery-maximizing policy when its magnitude changes with the route.

## A common policy under an additional delivery property

The general controller can depend on the actual service kernel. There is a
useful uniform corollary if a specified operational policy pi_0 maximizes
eventual delivery at every legal operational information set for every
service in the class. This is an extra operational dominance requirement,
not an assumption that standard miners necessarily satisfy it.

A sufficient pathwise formulation couples each permitted control policy to
pi_0 with the same service randomness, preserving the current information
and its law, so that whenever the alternative delivers, pi_0 also delivers.
Require this from every legal operational control site, including off-path
ones. Its conditional delivery comparisons are then weakly optimal for
every posterior over the coupled service states.

One elementary instance has a fixed opening treated as one delivery job.
Once submitted it remains eligible until publication or the terminal deadline.
Exogenous delivery opportunities are unaffected by submission time, waiting
or idempotent retransmission; identical copies do not change that job's
eligibility. Send it at the first available control response and then keep
it pending. On each coupled opportunity, a later-submitted job could be
eligible only when this earlier-submitted job is also eligible. First-send
therefore dominates every waiting/retransmission policy pathwise. No
independence between opportunity slots or positive success probability is
needed. This instance excludes cancellation, eviction, arrival-sensitive
producer response, and competition that changes future opportunities.

To supply consistency rather than only local dominance, use fully mixed
operational perturbations of pi_0 in the prefix construction. At the limit
the pointwise conditional dominance inequality proves every delivery
comparison under its induced full beliefs. The source-fiber coupling and
all other rationality arguments remain unchanged.

The complete prescribed policy can then be common across the service class:
copied source bindings, protected Open, pi_0 after Defer, and forced silence.
Beliefs can remain service dependent. The same policy works under a specified
common finite prior over source-independent service laws whose joint replay
and operational dominance retain these assumptions. This is a Bayesian
model with stated knowledge, not a prior-free ambiguity theorem. A service
correlated with hidden source data can instead select informative success
routes, as the counterexample in
[Late binding erasure](late-binding-erasure.md) demonstrates.

## Scope in the concrete runtime

Native opaque binding envelopes, fixed candidate values, public barriers,
full own recall and passive pending-packet observation support the physical
coupling cases. The
[native serial observation criterion](native-observation-criterion.md)
identifies checked ingredients and the missing native replay assembly.
Readable pending messages are included; their contents need only be
source-public by the next genuine decision, or followed by absorbing failure.

This new result weakens the number of delivery choices while strengthening
failure accounting. Neither its absorbing utility rule nor mode-independent
transport payoffs follow from the native runtime. Raw submissions can disclose
different candidates or add arbitrary packet fields, beyond the fixed-value
control menus. Actual response alphabets, observations and readiness need
their own finite operational adapter.

The
[settled native verdict](../../Vegas/Pending/ReactiveSettledVerdict.lean)
permits settled packets only when accepted with correct content. Of multiple
packets for one event, at most one is accepted; another can be forbidden
even though the correct opening succeeds. A dead canonical packet can also
be forbidden, whereas Never carries no such packet. An actual audit can
therefore make both success utility and failure utility depend on which
packets were emitted. Retries with new message identifiers are not proved
free private aliases. Transaction fees add another route-dependent cost.

A fail-stop protocol with one uniform missed-publication forfeit and no
additional charge for permitted identical retransmission is a variation in
which this theorem is useful. That would be a different utility/accountability
interface, not an authorized change to adopted semantics. Its protected
admission guarantees still need a declared backend contract; source finiteness
does not make liveness, scarce block capacity or settlement finality automatic.
This note proves neither that every realistic weakening destroys SE nor
that the actual charged-retry runtime preserves it.

## Result card

- **Source and physical game:** Finite public serial value-only protected
  bindings, mandatory immutable openings, retained private types, and an
  arbitrary bounded one-owner delivery-control process after Defer. Other
  players make no genuine choice before resolution.
- **Observations and service:** Readable pending plaintext and full private
  recall; operational dynamics depend only on public source past, fixed value
  and source-independent runtime records. The coupling is uniform across
  different retained types, not only within one source information set.
- **Positive and quantifiers:** Paper exact forward SE preservation for every
  admitted service and source SE, with fixed failure utility -D_i, D_i>=0,
  chosen before the service. Mode-independent nonpositive abort utility
  F_i(h) is also allowed. No late success probability floor is required.
- **Consistency evidence:** One full-support constrained auxiliary agent game
  per perturbation; positive-reach division gives uniform conditional delivery
  regret. A common global compact subsequence supplies every off-path belief
  and delivery policy, then original comparisons scale by a nonnegative
  source-value multiplier.
- **Knowledge boundary:** General off-path controllers can depend on the
  service; a declared pathwise delivery-dominating policy gives a common
  whole strategy, including under specified independent service priors.
- **Excluded effects:** General source withholding, late bindings, arbitrary
  messages, mode-dependent audit, fees, capital feasibility, outside utility,
  producer incentives, coalitions, capacity/finality implementation and
  post-abort strategic play. No full native adapter is claimed.
- **Review:** Root and independent mathematical reviews accepted the auxiliary
  agent construction, conditional regret, full consistency, type-independent
  posterior factorization, utility extension and common-policy corollary.
  Native assembly and machine checking are absent.
