# Late binding choices when failed attempts are erased from future play

Analysis by Codex. This note gives a paper extension of the
[serial immutable-opening theorem](serial-late-release.md). It allows a
binding value to be chosen at one late callback, rather than requiring that
every binding choice occur at a protected opportunity. The additional
condition concerns the game after a binding fails: a privately attempted
value must change no subsequent strategic possibility once that value is
erased. This is stronger than saying that the settlement contract ignores
an unaccepted value.

The failed attempt remains in its owner's actual memory. The proof constructs
an equilibrium that ignores this redundant private record. It does not ask a
player to forget a secret, make pending packets invisible, or revoke an
opening proof. General native raw play does not satisfy the stated erasure
condition merely because its terminal utility reads the source store.

An absorbing failure settlement is a simple concrete instance: after the
first publication failure, no further protocol action changes any modeled
utility. For that variation, opaque failed bindings have no continuation in
which their privately attempted values can matter. That gives a useful
positive without a private admission service, subject to the remaining
serial and opportunity restrictions spelled out below.

## Source game and physical interface

**Source game.** Fix a finite perfect-recall game with a public fixed serial
instruction sequence. Nature can initialize correlated private types and
bindings. A source binding decision chooses any legal typed value from its
finite menu and succeeds. A source opening has one mandatory effective
action: publish its immutable bound value. Public source chance draws keep
their declared conditional laws and are not resampled. Every supported
source chance edge is positive. Source utility satisfies 0 <= u_i <= R_i.
Retained secrets, later binding choices and arbitrary source equilibria are
allowed. Lawful withholding with arbitrary source utility is outside this
theorem.

**Binding opportunities.** At each source binding, its owner has the menu
ProtectedBind(a), for every legal source value a, and Defer. ProtectedBind(a)
privately registers a, emits its canonical opaque commitment envelope and
is surely accepted. Defer leads to exactly one later owned callback. At that
callback the owner can Emit(a), for every legal source value, or Never.
Emit(a) registers and transmits the canonical commitment. It either binds a
successfully or fails; Never fails surely. No value was selected by Defer.
Every admitted source value has its fresh-slot canonical native action.

Before resolution, no other genuine source choice occurs. All other owned
physical menus contain only silence. The pending commitment, its sender,
handle, timing and receipts remain physically available observations.
The transmitted envelope and the entire admission/failure experiment are
identical across a, conditional on the full state before Emit. An Emit does
not attach opening material or other value-dependent metadata. Its current
private registration is excluded from the service's inputs. On success,
the chosen value is added to its owner's source recall and future immutable
openings; acceptance itself reveals no value to another player.

**Opening opportunities.** At each mandatory immutable opening, retain the
serial interface: protected Open, or Defer followed by one Send/Never
callback. Send transmits the fixed value; its pending plaintext is readable.
No further source choice occurs before its success or failure resolves.
Unlike an opaque binding, an opening's service law may depend on that value.

**Service and observations.** All processing is finite bounded chance
processing. Its kernels inspect canonical public packets, receipts, clocks
and complete service-public history. They do not inspect unrevealed binding
meanings or private passive samples. Equal inputs have equal laws. Private
samples may be correlated and are remembered; every player retains its
complete own action and observation recall. Successful logical transitions
and subsequent source chance keep their source laws conditional on every
full physical record. Earlier physical randomness cannot predict a later
source chance draw. On every legal no-failure late callback, conditional
success is at least a public q_min > 0. No upper cap below one is required.

The first failed binding or opening has a public persistent marker identifying
its instruction. Before another strategic choice, all players recognize that
execution has entered the failure continuation. It never returns to an
information set containing a no-failure history. Its finite continuation
menus may otherwise be arbitrary, subject to the erasure condition below.
This is a specified restricted interface; additional callbacks, replacement
packets, extra preparations and raw premature proofs are not automatically
included.

**Costs and accountability.** No-failure utility equals source utility.
Failure gross utility is in [0,R_i]. Every nonnegative total deduction is at
most M_i=N_i D_i+K_i, with public N_i>=1 and K_i>=0 for players having a risky
binding or opening. A first failure caused by i collects at least D_i from
i regardless of subsequent policies. These are actual collectible funds
available before play. Collected amounts leave the modeled players, or the
gross bounds already account for redistribution.

There are no extra fees, financing or delay preferences, balance-dependent
menus, participation choices, outside trades, coalitions, other communication
channels or strategic producers. Cryptographic opacity and authenticity are
idealized; concrete bytes and metadata require a refinement. Capital
feasibility is not proved. Publication failure penalties are introduced only
on histories absent from this mandatory-success source game.

## Operational erasure after a failed binding

For a first failure caused by Emit(a), let e be the complete failure entry
record with the attempted value erased. Retain the earlier source history,
types, earlier bindings, service history, route, observation samples and
every player's prior recall. The emitting owner i retains the fact that it
attempted this binding and all information it had before choosing a. Only
this newly attempted value is omitted from e.

The actual entry is (e,a). The actual owner remembers a at every later own
information set. Others have received no a-dependent observation, since the
entire failed opaque experiment was value independent. The following is an
operational sufficient condition, not a property inferred from a payoff
formula.

**Common continuation condition.** There is one finite perfect-recall
continuation game with entries e. For each legal a, the actual continuation
above (e,a) has a coherent projection onto that game such that:

- Corresponding nodes have the same owner and every actual menu is in
  bijection with its projected menu. The bijection uses the acting player's
  information only. No actual alternative is removed.
- Chance kernels and transitions commute with the projection. The same
  projected action has the same projected transition law for every a.
- All other players' entire observations and recall are the projected ones.
  The emitter's actual information is its projected information together
  with its remembered a. Its original information before choosing a remains
  recoverable in that projected recall. Future own action names can be
  translated by the menu bijection, but recall is never discarded in the
  actual game.
- Every terminal player's gross utility and deduction equal those of the
  projected terminal history, for every continuation action sequence.

These projections agree on subsequent prefixes and information sets, so
they define a single common continuation game, not a separate unrelated
isomorphism for each value. Menus, proof capabilities, future observations
and utility are all covered. Never entries and fixed-value opening failures
use their ordinary entry records, without erasing an additional value. They
can join this same continuation game; their public instruction and retained
entry information are preserved.

A terminal settlement that ignores the attempted value meets this condition
when there is no further payoff-relevant play. For a nonterminal failure,
equal immediate rewards are insufficient. A failed preparation can leave
different evidence capabilities or recovery menus and thereby change the
best continuation payoff even if final utility reads accepted bindings only.

## Paper theorem

Fix the source/interface descriptor, R_i, N_i, K_i and q_min before selecting
the service or source equilibrium. Choose actual failure forfeits satisfying

\[
D_i>R_i,
\qquad
D_i[1-N_i(1-q_{\min})]
 > R_i+(1-q_{\min})K_i.                         \tag{1}
\]

For every service satisfying the full interface and common continuation
condition, every selected source SE has a target SE with exactly the same
joint law of initialized types, erased source terminal histories and source
utilities. At protected binding sites it copies the source value lottery,
at opening sites it chooses protected Open, and at off-path late binding
callbacks it copies the same source value lottery through Emit. Late opening
callbacks choose Send. There is no initialized deduction.

This is forward preservation, not reflection. Its no-failure policy and
late binding value selection are common to the whole service class. Beliefs
and projected failure equilibrium can depend on the service. No claim is
made that players need only a reliability bound to choose one complete
failure-tail policy under every unknown persistent service. A Bayesian
service model requires its joint replay channel to satisfy the same
information argument. This is a paper theorem, with no native raw adapter
or machine checking.

## Successful-prefix information and value comparisons

Use the source SE's fully mixed consistency sequence sigma_n. At a protected
binding menu, give ProtectedBind(a) probability
(1-epsilon_n) sigma_n(a|I), and Defer probability epsilon_n. At its late
callback give Emit(a) probability (1-epsilon_n) sigma_n(a|I), and Never
probability epsilon_n. At openings use the serial theorem's type-independent
Defer/Never trembles. Here epsilon_n>0 tends to zero and all copied value
lotteries ignore the auxiliary record. Every no-failure menu is fully mixed.

The successful-prefix replay again has the subprobability factorization

\[
w'_n(h,\omega)=w_n(h)L_n(h,\omega).             \tag{2}
\]

For a previous successful binding, both its protected and late envelopes
are opaque and admission is value independent. Thus two source histories
in a later foreign information fiber can differ in that binding value
without changing service inputs, public receipts, or that observer's recall.
The owner's past value agrees when comparing its own source fiber.
Type-independent transport trembles have the same coupled law. For previous
successful openings, the plaintext is already in the later source-public
history. The original serial coupling therefore extends by this one new
opaque-binding case.

In particular the joint marginal of the current actor's full view J and
complete service-public record P is equal on every source information
fiber. Bayes' rule cancels its common mass, giving the source posterior mu_n
at every genuine no-failure source site and late callback. This includes
off-path sites. A common compact subsequence handles full physical beliefs
and the singleton waiting sites, as in the serial proof.

The joint statement matters at a late binding. The success probability can
depend on P, even when P is not fully observed by its owner. For every value
a, opaque Emit(a) has the same public experiment from P, so write its
conditional probability as q(P). Given J=(I,z), the joint coupling makes
the conditional law of P the same for every source hidden history h in I.
Consequently, at each finite perturbation index,

\[
E_n[q(P)S_i(h,a)\mid J]
 =\bar q_n(J)\sum_{h\in I}\mu_{n,i}(h\mid I)S_i(h,a).
\]

Here S_i uses the limiting copied source continuation; the expectation is
over the index-n prefix posterior. The conditional service-record law,
and hence bar q_n(J), can depend on n because L_n does. Taking the common
full-belief subsequence gives bar q_n(J) converging to bar q(J) and yields

\[
E[q(P)S_i(h,a)\mid J]
 =\bar q(J)\sum_{h\in I}\mu_i(h\mid I)S_i(h,a),       \tag{3}
\]

where S_i(h,a) is the source continuation value after binding a and
bar q(J)>=q_min. The future copied source policy and conditional source
chance law make S_i(h,a) independent of physical P. Neither exact knowledge
of bar q by the player nor a pointwise information-local success function
is needed. Equality of only the actor's marginal view would not by itself
justify (3).

## Failure completion without a symmetric-equilibrium assumption

The failure entries form a cutset. The mixed no-failure profile induces its
actual normalized entry prior nu_n. For failed Emit entries, the value-
independent public experiment and source-copied selection give exactly

\[
\nu_n(e,a)=\bar\nu_n(e)\sigma_n(a\mid I_i(e)).        \tag{4}
\]

Here I_i(e) is the emitter's remembered source information before Emit;
any route probabilities, Never trembles and failure likelihoods are already
included in bar nu_n(e). Equation (4) follows from the actual prefix
probabilities. The erasure assumption is not used to replace the actual
entry prior by a convenient one. For other entry kinds there is no a mark.

Take an SE of the single projected continuation game at prior bar nu_n.
Lift its strategy to every actual continuation by the coherent menu
bijections, ignoring a. This is an SE of the actual continuation game with
prior nu_n, not just an equilibrium with a symmetric choice of actions.
Here is the needed private-record argument.

Take a fully mixed consistency witness for the projected SE and lift each
of its strategies in the same way. For a player other than the emitter,
no observation depends on a. Summing over a in (4) gives the projected
history probability because sum_a sigma_n(a|I_i(e))=1. For the emitter,
the original I_i(e) remains in its later projected own recall. At any
of its full information sets, the known mark a multiplies every compatible
projected history by the same positive factor sigma_n(a|I_i(e)); Bayes'
rule cancels that factor. All projected posteriors are therefore exactly
the projected game's Bayes posteriors, at every continuation information
set, not just at entry.

The common continuation condition gives every actual one-shot action choice,
followed by the lifted prescribed continuation, its projected continuation
law and utility. The projected SE's local comparisons therefore apply at
every actual information set, including ones with a known remembered a.
Full mark beliefs are obtained from (4); along the projected consistency
witness n is fixed, so its positive mark channel is fixed. The full
beliefs converge, or one can take a common compact subsequence. Finite
perfect recall and the one-shot principle then give sequential optimality
against adaptive whole policies that condition future choices on a.

This lift also makes the prescribed failure continuation payoff
F_i(e,a) exactly F_i(e), pointwise in each hidden projected entry e.
That equality is the ingredient needed to compare late values. Merely
choosing separate SEs in isomorphic failure games would not guarantee it.

For each n choose sufficiently close fully mixed strategy-and-belief
witnesses of the lifted actual continuation SE. Splice them into that same
global no-failure mixed prefix. Global Bayes beliefs in the marked failure
region are the virtual game's beliefs at the actual nu_n: the common total
entry mass cancels. Take one common compact subsequence of the global
strategies and beliefs and of the selected continuation SEs. Their
differences tend to zero. Finite continuation-value continuity passes all
local failure inequalities to the limit, and their strategies still ignore
the remembered attempted value after projection. This is the serial proof's
one-prior completion construction with an additional private-record lift.
No favorable off-path belief or assumed symmetric SE is introduced.

## Rationality of the expanded binding menus

At a late binding callback J, one prescribed Emit continuation succeeds
with nonnegative source utility and fails with utility at least -M_i.
It therefore yields at least -(1-q)(N_iD_i+K_i). Every Never continuation
yields at most R_i-D_i. Condition (1) makes submitting a source lottery
strictly better than Never, even against arbitrary later Never policies.
This is the same loss-cap comparison as for the late fixed-value Send.

Compare Emit(a) with Emit(b), keeping the constructed future strategy.
The common continuation gives identical failure payoff for both, including
deductions. Their payoff difference at J is therefore

\[
\bar q(J)\bigl[V_i(I,a)-V_i(I,b)\bigr],
\qquad
V_i(I,a)=\sum_{h\in I}\mu_i(h\mid I)S_i(h,a).          \tag{5}
\]

Every value in the support of the source sigma_i at I maximizes V_i(I,a)
by source sequential rationality. The copied source lottery is hence
optimal among all Emit value choices at that callback. The value-independent
failure term cannot create the type-dependent perturbation that drives the
[attempt-dependent binding counterexample](admission-information-boundary.md).

At the protected binding root, every ProtectedBind(a) comparison is exactly
the source comparison. The copied source lottery is optimal among these
values. Conditional on each hidden pre-decision history, Defer followed
by that copied lottery has its source continuation on success and payoff
at most R_i-D_i<0 on failure. The success experiment is identical across
the lottery's values. Since every source continuation is nonnegative,
the value of Defer is at most that of the prescribed protected lottery.
The root's retained source mixture is locally optimal.

Protected opening and late Send comparisons are those of the serial
theorem. Every other no-failure menu is singleton silence. Marked failure
comparisons were completed above. One globally consistent assessment
therefore satisfies every local inequality. Finite perfect recall gives
full sequential rationality against adaptive whole policies. Initialized
play uses protected actions, so erasure preserves the exact joint source
terminal law without deductions. QED.

## Why value-independent failure utility alone is insufficient

**Different interface, not a native counterexample.** Keep one immutable
opening, one late callback, terminal failure settlement and no extra fees.
Weaken the information condition by letting the service's success law depend
on a source-secret bit that neither acting player knows. This violates the
successful-prefix coupling assumption above. It shows why a scalar marginal
inclusion probability and erased failed attempts are insufficient on their
own; it does not show that the actual canonical public scheduler sees a
hidden binding meaning.

Nature gives an inactive player a fair bit theta. The sender's initialized
binding is a fixed constant v, independent of theta. The receiver must choose
Safe, Guess0 or Guess1 after the opening. Safe pays the receiver 1/2; a
correct guess pays 1 and an incorrect guess 0. The sender gets R/2 after
Safe and R after either guess, with R>0. The inactive player gets zero.
Opening is mandatory and certain in the source. A source SE has the receiver
choose Safe: its belief is fair, and every guess ties Safe. Fix this selected
source law.

In the target the sender chooses protected Open or Defer, followed by the
one Send/Never callback. Every player observes whether a successful opening
was protected or late. Protected success is certain. Late Send succeeds
with probability 1 when theta=0 and 1-epsilon when theta=1. The callback
and all pre-send observations are identical in both states; the sender
cannot condition its root or callback lottery on theta. Failure ends play
with sender utility -D, for any fixed finite D>=0. Never fails certainly.
No attempted value affects failure payoff, and no pending packet reveals
theta.

In every globally consistent assessment, the receiver's late-success belief
is

\[
\Pr(\theta=0\mid\text{late success})=\frac1{2-\epsilon}>\frac12.
\]

Indeed every fully mixed sequence contributes the same sender Defer and
Send factors in the two hidden states, so Bayes' rule cancels them and leaves
only the two success likelihoods. Thus Guess0 is strictly optimal there,
including when late success is off path. Send is strictly better than Never
at the late callback: its utility exceeds -D by
(1-epsilon/2)(R+D)>0. The root's Defer continuation consequently gives

\[
(1-\epsilon/2)R-(\epsilon/2)D>R/2
\quad\text{when}\quad 0<\epsilon<\frac{R}{R+D}.
\]

Any target assessment preserving the selected source law must put probability
one on protected Open. A positive Defer probability would produce a positive
failure probability in state theta=1; the source has none. At protected
success preservation also requires Safe, yielding sender utility R/2.
The strictly profitable Defer comparison refutes such an SE. Since D was
fixed first, epsilon can be chosen afterward below the displayed bound and
below 1-q_min for any predeclared q_min<1. The negative therefore survives
an arbitrarily high public lower success bound.

The failure continuation is terminal and its attempted-value erasure is
perfect; the failure is instead selection of a hidden source state by
successful delivery. A native embedding would need an actual public input
or correlated service state carrying theta. None is supplied.

**The same fixture preserves weak PBE.** Here weak PBE requires sequential
rationality everywhere and Bayes' rule only at positive-probability
information sets. Let the sender choose protected Open and prescribe Send
at the late callback. Let the receiver choose Safe after both protected and
late success, with a fair belief about theta at both. The protected belief
is the actual Bayesian posterior. Late success is off path, so weak PBE
allows its fair belief; both guesses then tie Safe.

At the sender's late callback use its fair belief and put
bar q=1-epsilon/2. Send, followed by Safe, has utility
bar q R/2-(1-bar q)D; Never has utility -D. Send is strictly better by
bar q(R/2+D)>0. At the protected root, Defer followed by Send yields at most
R/2, whereas protected Open yields R/2. Thus every local comparison holds,
Bayes' rule holds on path, and the selected source law is preserved.

This weak PBE fails sequential consistency: every fully mixed global witness
has the late-success posterior 1/(2-epsilon)>1/2, forcing Guess0 instead
of Safe. The fixture therefore separates weak PBE preservation from SE
preservation. It proves neither a general weak PBE transfer theorem nor
preservation for a stronger definition that constrains these off-path
beliefs, and it remains outside the native information model.

## A simple absorbing-failure variation

**Interface for this corollary.** Keep the protected/one-late binding and
opening menus, finite serial source, opaque commitment experiment, readable
pending openings, and source chance/utility restrictions above. At the first
failed publication, end all further payoff-relevant protocol play. Settle
from prior accepted source data and the public failure transcript. This
settlement, including its deduction law, ignores a failed binding's private
attempted value. Any later physical communication has no modeled utility
effect. Funded failure deductions are bounded by D_i+K_i for player i and
collect at least D_i when i causes that first failure.

The common continuation game is then terminal; attempted value erasure
is immediate, while the actual owner's memory and private catalogue can
remain intact. Condition (1) uses M_i=D_i+K_i, regardless of the number
of earlier source phases. Every public q_min>0 suffices with

\[
D_i>\frac{R_i+(1-q_{\min})K_i}{q_{\min}}.             \tag{6}
\]

Thus multiple late opaque value choices and multiple later immutable
openings admit exact forward SE preservation in this restricted fail-stop
interface. The whole selected source game can contain many strategic binding
choices and retained correlated secrets. The clean service need not hide
packets or order them before observation. Its main structural requirements
are serial choice frontiers, opaque bindings, protected early admission,
one late callback with a conditional success bound, and fixed-value opening.

In this absorbing variation the entire prescribed behavioral policy is common
to the service class: protected source value lotteries and Open, late Emit
with the same source lottery and Send, and forced silence elsewhere. There
is no strategic failure tail whose policy must be selected using the exact
builder law. Only the full assessment's beliefs may depend on that law.
The same policy also preserves SE under a specified common prior over
finitely many source-independent services, provided their joint replay
retains the stated source-fiber coupling and unchanged logical chance laws,
and conditional success is at least q_min. Collateral uses the common bound;
players need not know the exact inclusion kernel to implement this policy.
This is a Bayesian statement under declared service knowledge, not a
prior-free ambiguity result. An arbitrarily correlated prior is not covered;
the hidden-bit counterexample shows why service/source independence matters.

This is a realistic protocol design option at the game-interface level:
a contract can stop and settle after a missed publication. It is not an
assertion that the adopted source compiler does so, that all source programs
have this failure policy, or that a blockchain supplies protected windows
and q_min under arbitrary traffic. Other strategic contracts, outside trades,
post-abort communication rewards, recovery choices and renegotiation are
excluded. They would remove the absorbing-utility condition.

## What the actual native operations do and do not erase

The checked
[binding observation layer](../../Vegas/Pending/ReactiveBindingObservation.lean)
proves that changing a canonical binding's meaning leaves its public network
unchanged and preserves foreign activation inputs. This supports the
value-independent opaque experiment case. It does not say that the owner's
private state is unchanged after a failed admission.

[Submission registration](../../Vegas/Pending/EventSubmission.lean) prepares
an owned candidate before packet emission and fixes its meaning. The checked
[candidate realization layer](../../Vegas/Pending/ReactiveCandidateRealization.lean)
states its stronger catalogue-to-source-store representation at completed
canonical binding prefixes; it expressly does not assert that property
between submission and inclusion. A failed admission can leave a private
candidate that is not an accepted source binding.

[Opening evidence](../../Vegas/Pending/OpeningEvidence.lean) certifies a
candidate's immutable value even when that candidate never won a binding.
Its owned-evidence operation checks the private catalogue, not acceptance
of that candidate. A raw response can therefore expose the candidate's
authentic opening material later. Inclusion rejection does not undo the
packet's public contents. The explicit
[response-menu construction](../../Interaction/ReactiveResponseMenu.lean)
restricts native actions without asserting strategic equivalence to raw
play; the full response application permits such submissions.

This gives a direct obstruction to the common continuation condition in
general raw tails. Compare an otherwise equal failed-binding state with
candidate H fixed to a against one with H fixed to b, a!=b, and no prior
certificate for H. In the first state its owner can request an authentic
certificate for (H,a); in the second state it cannot. Replacing the request
by one for (H,b) changes the packet that another player sees. Freezing H
prevents re-preparing it to a. Thus there is no observation-preserving
continuation correspondence of the stated kind whenever those raw responses
and an observing later choice remain available. This is failure of a
sufficient adapter hypothesis, not a native SE impossibility theorem.

The actual
[source readout and utility](../../Vegas/Game/RevealServicePayoffs.lean)
decode the typed terminal source store, retaining initial private cells.
They do not directly read an unaccepted candidate's privately attempted
value. This rules out treating an arbitrary attempt-dependent payoff as
already embedded in that readout. It does not establish full erasure:
candidate evidence, future menus, observed packets and recovery paths can
still affect later strategic outcomes and hence the eventual typed store.

Finally the
[settled verdict](../../Vegas/Pending/ReactiveSettledVerdict.lean)
judges accepted content rather than emission time. A failed canonical packet
can be forbidden at settlement. Its charges must be accounted for in K_i;
the checked audit extension cannot simply declare every such retained
history audit-clean. No native full-menu erasure or collection adapter is
proved here.

## Result card

- **Source and target:** Finite serial value-only successful bindings,
  mandatory immutable openings, retained private types and choices; protected
  binding or one late Emit(value)/Never, plus one late fixed-value opening.
- **Information and service:** Opaque value-independent binding experiment,
  readable pending plaintext, complete recall and conditional success
  q>=q_min. Joint public-service/actor replay invariance supplies the late
  value-comparison factor. No known exact miner probability is required.
- **Additional boundary:** Failed attempted binding values have a coherent
  common continuation projection preserving all menus, transitions,
  observations and utilities. Their actual private recall is retained.
- **Positive:** Paper exact forward SE preservation under (1), with one
  globally consistent assessment. Absorbing failure settlement reduces the
  requirement to (6) for every q_min>0, regardless of the source phase count.
- **Quantifiers and exclusions:** Public bounds first, funded collateral next,
  then every admissible service and source SE. Fees, capital feasibility,
  producer incentives, outside utility, coalitions, extra callbacks, other
  transmissions and general source withholding are excluded.
- **Native scope:** Opaque binding and readout facts support parts of the
  interface. Persistent candidate evidence obstructs general raw continuation
  erasure. This is not a native SE counterexample or a checked native theorem.
- **Review:** Independent mathematical review accepted the coherent quotient,
  actual entry factorization, private-record consistency lift, global
  completion, late value comparisons and scoped hidden-state counterexample.
  Native assembly and machine checking are absent.
