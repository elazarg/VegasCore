# Service and collateral requirements for commit–reveal preservation

Analysis by Codex. This is a math-only research note. Its candidate interfaces
and new proofs are not claims about the implemented runtime. Checked results
are identified separately. No semantics or preservation checklist changes are
proposed here.

The useful separation is between a service that represents the source game,
and enforcement of departures from that service. Collateral can deter an
observable departure. It cannot make an informative lawful packet opaque,
create capacity for another participant, recover collateral already spent,
or supply a consistent belief system by itself.

## The games and utility scope

The source is a finite extensive-form game with perfect recall, finite action
menus, and a finite joint prior. Private state may be correlated and remains
available across phases. A logical commitment fixes a value; an opening reveals
that value at the specified logical point. Source withholding, failure, and
abort alternatives remain genuine actions when the source provides them.

The target is another finite perfect-recall game describing physical sends,
pending observations, fees, admission, receipts, finality, and settlement. Its
logical readout erases those implementation records. Public pending messages
are visible according to an explicit observation rule; they are not erased
because the intended client ignores them. A message may disclose information
before it is accepted. A collector may observe different traffic from another
player, but those observations must be specified.

Utilities include the application payoff, transaction fees, delay or capital
costs that the model represents, and actual collectible deductions. Additional
trading profits, bribes, validator revenue, or damage to another application
must either be included and bounded or excluded explicitly. A theorem for
application utility alone does not constrain unmodeled outside incentives.

The compiler, fee convention, scheduler, escrow rule, and finite deposit vector
are fixed before selecting a source SE. Ordinary SE here means sequential
rationality against entire remaining policies and one global Kreps–Wilson
consistency sequence. Local incentive inequalities alone do not establish
this consistency or the existence of a preserving assessment.

The source and target utility comparison also needs a fee convention. Charging
different fees for two source actions with tied payoffs can remove a selected
exact source equilibrium. Fees may instead already be included in the source
payoff, or an unavoidable common entry fee may be charged in both comparisons.
The latter preserves incentives but shifts numerical payoffs. Negligible
action-dependent fees justify approximate incentive claims, not automatic exact
preservation. See
[preservation-and-robustness.md](preservation-and-robustness.md).

## Candidate service interface

The following is a collection of separate candidate guarantees. It is not a
claim that their names describe one currently deployed blockchain.

| Part | Plain-English operational requirement |
| --- | --- |
| Immutable meaning | The contract can associate each accepted commitment with one logical value. A successful opening cannot change that value. Acceptance and failure have unambiguous typed readouts. |
| Phase gate | The logical choices that must precede a revelation are irrevocably fixed before its content can influence a later strategic choice. A gate on contract execution does not itself gate pending-message observation. |
| Timely opportunity | At each represented source decision, the owner can use an information-local canonical action with a stated admission, inclusion, and finality guarantee. Its fee and collateral requirements are feasible within the declared budget. |
| Joint service guarantee | The guarantee covers the relevant actions of other users and the allowed resource load. One player's successful valid send cannot silently invalidate the guarantee for another simultaneous canonical send. |
| Receipt and finality | A receipt says exactly which logical transition is fixed. If rollback remains possible, its probability and effect on earlier observations, deadlines, and settlement are part of the game. |
| Information fidelity | On all represented source histories, including histories reached by lawful deviations, target observations give exactly the source information plus declared extra signals that have a separate preservation argument. |
| Timing fidelity | The scheduler's supported timing and ordering rules, and the player's ability to influence them with fees or other actions, are explicit. Their information and payoff consequences are accounted for. |
| Accountable departures | Every action classified as a departure has specified evidence, a collector, an incremental collectible amount, and a bound covering arbitrary later policies. Legal source alternatives are not classified as misconduct merely because they differ from one selected equilibrium. |

“Same logical value” is weaker than source equivalence. A valid packet alias
can still disclose a private type, change another user's inclusion, or alter
an economically relevant fee. To call an action source-equivalent, supply a
source continuation with the same relevant joint logical law and information
constraints, or a proved domination comparison. Own-payload equality is not
such an adapter.

Conversely, a source withholding action that is lawful need not be costless.
Its declared source failure payoff may include a forfeiture. The compiler may
preserve that payoff; it may not silently add a new punishment and claim to
preserve every equilibrium of the unchanged source game.

There is a useful exact service model with public stochastic waiting: waits
are chance moves, eventual source choices retain the original menus and
payoffs, and the public scheduler depends only on recoverable source-public
history. Its source-to-service SE argument is in
[public-scheduling-se-preservation.md](../public-scheduling-se-preservation.md).
That paper model does not include arbitrary strategic timing, failed admission,
or additional private-state signals. A real backend requires an adapter to it.

## The exact conditional penalty calculation

Fix a legal decision history or an information set with a fixed belief. Fix
two whole continuations: a candidate deviation and a lawful comparator. Hold
their physical contingent policies, chance kernels, and audit rules fixed.
Let

\[
 g=\mathbb E[b_i\mid\mathrm{deviation}]
      -\mathbb E[b_i\mid\mathrm{comparator}],\qquad
 r=\mathbb E[a_i\mid\mathrm{deviation}]
      -\mathbb E[a_i\mid\mathrm{comparator}],
\]

where base payoff \(b_i\) includes fees and modeled outside benefits, and
\(a_i\in[0,1]\) is the probability of actually collecting a fixed escrow
\(K_i\). A submitted accusation is not yet collection. The net gain is exactly

\[
 g-K_i r.
\]

Therefore \(r>0\) and \(K_i\ge g/r\) deter that comparison; \(r=0\) requires
\(g\le0\). If \(r<0\), increasing the deposit rewards the deviation relative
to the comparator. With nonnegative deposits, such a comparison imposes an
upper bound \(K_i\le g/r\); if \(g>0\), it is impossible to deter it this way.
These statements are elementary identities, not equilibrium theorems.

For a family of comparisons fixed independently of the chosen deposit, with
\(r(d)\ge0\), a common finite nonnegative deposit exists exactly when

\[
 r(d)=0\Rightarrow g(d)\le0,
 \qquad
 \sup_{d:r(d)>0}\frac{\max\{g(d),0\}}{r(d)}<\infty.
\]

An empty positive-risk family needs no ratio bound. Necessity divides the
deterrence inequality by positive risk; sufficiency chooses a nonnegative
deposit at least the common upper bound. This sharper boundary does not require
a positive uniform risk floor: gains may shrink with risk.

The independence qualification matters. If an opponent's equilibrium response
is recomputed when \(K\) changes, then the resulting gain and risk can depend
on \(K\). Evaluating a ratio at one selected equilibrium and then changing
the deposit is circular. A reusable sufficient argument instead bounds all
hidden histories and all contingent future plans in a fixed finite physical
game. The strategy set is then fixed even though optimal strategies change.

Locked-capital costs can also depend on the deposit. With fixed monetary
utility, suppose capital costs \(\lambda K\) per unit of lock time, and the
deviation saves expected time \(\Delta T\) relative to the comparator.
Write \(s=\lambda\Delta T\ge0\) and let \(g_0\) be its other base gain.
Its net gain is then \(g_0-K(r-s)\). Positive collection risk \(r\) alone
does not deter a positive \(g_0\) if \(s\ge r\). Holding escrow until the
same fixed settlement time removes this particular saving; otherwise a
usable bound must control the effective margin \(r-s\), or the complete
deposit-dependent cost comparison. Time preferences and opportunity costs
are part of the monetary utility model, not free consequences of slashing.

For a finite vector of fresh deductions the identity is
\(g-\sum_j K_j r_j\). If others' confiscated funds are paid to the deviator,
those rewards also depend on the deposit vector. For example, requirements
\(K_1\ge G+K_2\) and \(K_2\ge G+K_1\), with \(G>0\), have no solution.
“Increase every deposit” is not a proof when bounty redistribution changes
the gain. Burning a deduction, or transferring it outside the modeled ordinary
players, avoids this particular dependence; strategic collectors still need
their own incentive model.

## A positive result derived from finite mechanics

**Interface for this result.** Fix finite source and target games with perfect
recall. The source embeds as a structural restriction of target actions:
retained transitions, information histories, and legal source choices match.
Every retained complete history is uncharged, and its base utility matches
the source utility under the chosen fee convention. Let the source payoff
be at least \(L_i\), and every raw base payoff be at most \(U_i\).
These base utilities and bounds are fixed independently of the selected
deposit, or are supplied uniformly over its allowed range.

For every retained hidden decision history \(h\), every excluded current
action \(e\), and every complete deterministic observation-local joint future
plan \(p\), run the actual finite chance tree and audit. Assume its probability
of collecting the departing owner's escrow is strictly positive. This is a
primitive test over the physical mechanics: it does not assume beliefs,
equilibrium play, desired continuation payoffs, or compliance after departure.
The audit is fixed before deposits and sound on every retained history.

**Paper derivation of a uniform bound.** There are finitely many triples
\((h,e,p)\). If no excluded triples exist, enforcement is vacuous. Otherwise
take their smallest positive collection probability, \(\rho_i>0\). A behavioral
continuation can be realized by sampling its local action draws in advance;
perfect recall prevents revisiting one decision information set. The execution
and audit law is the mixture over those pure contingent plans. Every such
mixture therefore collects with probability at least \(\rho_i\). This includes
correlated joint mixtures; independence is unnecessary for the lower bound.
It also covers every belief over compatible retained histories, since the
bound was proved pointwise before averaging over a belief.

One fixed finite vector

\[
 K_i=\max\{0,(U_i-L_i)/\rho_i\}
\]

then deters every excluded first action against arbitrary later behavior.
Its expected net payoff is at most \(U_i-\rho_iK_i\le L_i\). A retained
continuation gives at least \(L_i\). The configuration does not depend on
which source SE is later selected.

**Game-level conclusion and its separate ingredient.** Under this structural
restriction, the consistent-completion theorem extends each source SE to a
target SE, optimizing the new target sites and preserving the embedded
initialized logical law. Since retained play is audit-clean, the realized
settlement law is also preserved under the matching payoff convention. This
last step is not supplied by the scalar penalty inequality. It requires the
finite restriction and completion hypotheses.

The general terminal-audit extension and finite-deposit conclusion are already
checked in [TerminalAudit](../../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean),
as described in [general-se-preservation.md](../general-se-preservation.md).
The finite-plan mixture lower bound is checked in
[PositiveCollection](../../GameTheoryExtensions/Analysis/PositiveCollection.lean).
Supplying the source-to-service restriction, the actual pure-plan collection
tests, and behavioral execution realization for a particular backend remains
an operational obligation. Those checked results are not a general theorem
for every blockchain scheduler.

A concrete assembled candidate is to first lift the abstract source SE into
the public-delay service model, then embed that service as the retained part
of the raw protocol. The clock-free source need not itself be a literal action
restriction of the clocked target. Suppose every first excluded action creates
an authenticated or publicly certified fault witness, later actions cannot
erase that witness, and the settlement service collects from it with probability
at least \(\alpha_i>0\), pointwise under every future plan. Signed forbidden
traffic and a certified deadline fault are possible witness kinds; an
unobserved silence is not automatically evidence. If retained histories never
create such witnesses, then \(\rho_i\ge\alpha_i\), and one fixed finite deposit
strictly above \(\max\{0,(U_i-L_i)/\alpha_i\}\) suffices by the same extension.
This is a conditional paper application of the checked completion theorem.
Authentication, persistent evidence availability, actual collection, source
information fidelity, and the structural service embedding still need backend
proofs. Public readability by one recipient does not prove those properties.

This proof needs fresh risk only at the first departure from clean retained
play. At a later dirty site the escrow may already be lost. The completion
theorem optimizes that dirty continuation; it does not demand further
compliance there. A profitable dirty-suffix disclosure, by itself, does not
refute this forward-preservation result.

## An explicit physical route to the risk bound

**Candidate interface.** After a detected timing departure, let `bad` mean
that recovery has not yet removed the auditable fault. The initial
post-departure state is bad. There are at most
\(N\) physical opportunities before settlement. At each opportunity, conditional
on every full prior physical history that is still bad and on every allowed
action, fee, and routing choice, the probability of remaining bad is at least
\(0<\varepsilon\le1\). Waiting may count as an opportunity and preserves badness.
At settlement, a bad record collects with probability at least \(0<\alpha\le1\).
These are statements about transition and audit kernels, before any assessment
is selected.

**Lemma, paper proof.** Collection probability is at least
\(\rho=\alpha\varepsilon^N\). The conditional expectation of the next badness
indicator is at least \(\varepsilon\) times the current one. Iterating this
inequality gives probability at least \(\varepsilon^N\) of badness surviving
all opportunities. Average the terminal audit lower bound over that event.
The argument accommodates adaptive choices and correlated delays. Padding a
shorter execution with badness-preserving waits proves the same bound for an
adaptive stopping time bounded by \(N\).

The predicate must fit the actual fault. If a late but certain canonical
inclusion removes every charge, then that action has zero risk and this
badness-survival premise is false. If a recipient can read an excluded packet
but no collector can obtain evidence of it, recipient observation alone does
not give \(\alpha>0\).

The checked survival and native round adapters are linked from
[module-architecture.md](../module-architecture.md). The candidate interface
above still needs to be proved from a backend's primitive kernels.

## Sunk, fresh, and capped collateral

A one-time audit charge has a boolean settlement variable. Conditional on a
prefix where collection is already certain, every future continuation has
\(a_i=1\). Its additional charge risk is zero. The relevant gain is therefore
\(g\), regardless of how large the original escrow was.

Possible alternatives have different obligations:

| Collateral design | What must be proved |
| --- | --- |
| One clean-prefix escrow | Every excluded first departure has positive actual collection under every future plan; clean source histories collect nothing. Dirty continuation may be arbitrary. |
| Separate phase escrows | Phase \(j\)'s charge is not consumed by earlier faults. The phase's remaining decisions have their own source-equivalent service and pointwise collection bound. Other phase escrows cannot be withdrawn or spent to avoid it. |
| Additive penalties funded upfront | Reserve enough collectible funds for all charged fault units. Each new unit really increases the deduction, with no cap reached before the comparisons being enforced. |
| Replenishment | Specify who can refuse to replenish, what happens on refusal, and whether that abort is a legitimate source choice. “The player tops up” is not an incentive proof. |
| A fixed total cap | Comparisons after the cap is exhausted have zero additional deduction. Their profitable departures need another deterrent or a completion argument that tolerates them. |

If a physical game allows at most \(Q\) charged units and each needs at most
\(M\) collateral, an upfront reserve \(QM\) is finite and can avoid exhaustion
before the last unit. A finite number of logical phases does not give \(Q\)
when each phase allows unbounded packets or retries. Conversely, preventing
every dirty-suffix departure is stronger than the clean-first-departure SE
extension requires; fresh collateral at every raw action is not a necessary
condition for that theorem.

Per-reveal source forfeitures and one-time traffic escrows must also be
distinguished. An additive source forfeiture for another failed reveal can
remain incremental after an earlier traffic escrow is spent. It can make
truthful completion preferable when available. It does not automatically
price an extra early information leak that leaves the final reveal successful.

### A finite nonpreservation game with unavoidable spent collateral

**Candidate model, complete paper proof.** Nature draws an immutable private
bit \(w\), fair and known to Alice, and an independent public flag \(z\).
Let \(\Pr(z=\mathrm{spent})=\eta>0\). Bob later makes an irreversible choice
\(S,G_0,G_1\), before the legitimate final opening of \(w\).
His base payoff is \(3/4\) for \(S\), one for a correct guess, and zero for
an incorrect guess. Alice's base payoff is zero for \(S\), one for a correct
guess, and zero for an incorrect guess. At the final opening she can publish
\(w\) or fail; failure deducts a separate source forfeiture \(H>1\).
The flag gives no information about the bit.

In the source, there is no early message action. Every SE has Bob choosing
\(S\), since either guess has expected payoff \(1/2<3/4\). The final opening
is strictly preferable to failure. Fully mixed independent type trembles and
Bob trembles establish consistency. The source logical law is therefore safe
choice followed by truthful publication, at both flag values.

In the target, before Bob's choice Alice can send an opaque canonical packet
or a certified premature proof of her bit. The proof costs \(f\), where
\(0\le f<1\). Its signature and binding evidence make the bit certain to Bob;
pending contents and the absence of a proof are publicly observable. Both
actions leave the same final logical commitment and allow the ordinary final
opening. A one-time escrow of any finite size \(K\ge0\) is already certainly
charged on the spent branch. Sending another proof cannot increase that charge.
On the fresh branch the audit may charge proofs; its rule there is immaterial
to the negative result. The separate final failure forfeiture remains \(H\).

On the spent branch, a proof yields Alice base payoff \(1-f>0\) and Bob must
guess correctly. Conditional sunk \(-K\) cancels from Alice's comparisons.
If a preserving profile kept Bob safe after an opaque packet, Alice would
strictly gain by proving her bit. Consequently no target SE, or even weak
PBE, preserves the source logical law, for any finite original escrow.

There is a stronger characterization. If a type uses the opaque packet with
positive probability, its payoff there must be at least \(1-f>0\), so Bob must
assign positive probability to guessing that type after the opaque packet.
Bob cannot optimally mix both guesses: their tie requires posterior \(1/2\),
where safe is strictly better than either. Thus at most one type uses the
opaque packet on path. Bayes' rule then makes that type certain and Bob guesses
it correctly. Certified proofs also receive correct guesses. Every target SE
therefore has correct guesses with probability one on the spent branch, and
its logical-law TV distance from the source is at least \(\eta\).
The final opening remains strict because its failure deduction is separate.

This example includes an unavoidable spent branch. It does **not** say that a
dirty suffix reached only by a deterrable initial offense destroys preservation.
It deliberately violates clean retained-history matching or fresh collection
on that unavoidable branch. The same unavoidable sunk transfer can be included
in both games without changing these conditional comparisons; otherwise the
claim compares logical outcomes, not equality of numerical settlement payoffs.
The ordinary uncharged early-disclosure obstruction is discussed separately in
[information-and-release.md](information-and-release.md).

## Concurrent reveals and scheduler leverage

Independence of logical reveal values does not imply independence of physical
capacity. A scalar guarantee that one's own packet is included with high
probability omits the damage a fee or load choice can cause to other reveals.
One's own failure forfeiture does not punish another player's failure.

**Finite counterexample, complete paper proof.** Two players have immutable
commitments and the source requires their openings before settlement. Bob's
base payoff is always zero. Alice's base payoff is two if Bob's opening fails,
zero otherwise. Each owner loses \(H>2\) for its own failed opening. Source
openings are reliable, so every source SE opens both commitments and pays zero.

In the target Alice may use a normal or a resource-heavy valid opening. A
normal opening costs zero and leaves capacity for Bob. The heavy opening
costs \(f\in(0,2)\), succeeds for Alice, and occupies the remaining resource
budget so Bob misses his fixed deadline. Alice's accepted logical value is
identical in both modes, and no audit charges the heavy mode. Bob sees the
mode and may try his canonical opening or withhold. After normal service he
strictly prefers trying, obtaining zero instead of \(-H\). After heavy service
he fails either way and gets \(-H\). Alice therefore strictly prefers heavy,
obtaining \(2-f>0\), over normal followed by Bob's rational successful opening.
Alice's withholding consumes no capacity, so Bob receives normal service;
her own withholding gives \(-H\). Every target SE uses heavy service and Bob
fails. No SE preserves the source law, for any larger own-failure forfeiture.

This is a fully public finite capacity toy, not an existing-runtime or chain
deployment claim. It shows the missing guarantee: successful aliases must
preserve other users' service, or harmful resource consumption must incur an
incremental collectible penalty. Fresh collateral with no chargeable offense
does not fix it. Nor does blaming Bob for a deadline miss prove that Bob could
have avoided a competitor's load.

Useful candidate repairs include reserved per-owner capacity, bounded admission
that accounts for the worst simultaneous canonical load, and phase deadlines
that cannot be exhausted by another allowed action. These change the service
interface; their own costs and strategic admission decisions remain modeled.
An adaptive scheduler may condition on legitimately public values, but hidden
value-dependent scheduling signals or priority purchases require separate
information and deviation adapters.

## Deadlines, finality, and physical bounds

There are three different claims to distinguish:

1. A canonical publication succeeds surely before a logical decision closes.
2. It succeeds before a fixed physical deadline with probability at least
   \(1-\delta\).
3. Its acceptance becomes final eventually, perhaps almost surely, without a
   fixed physical settlement time.

Only the first gives exact reliability by itself. If every target policy has
failure probability at least \(\delta>0\), and the selected source law has no
failure, the target logical-law TV error is at least \(\delta\), regardless of
collateral. This follows by comparing the failure event. The native outage
result in [probabilistic-runtime-preservation.md](../probabilistic-runtime-preservation.md)
supplies checked actual-runtime examples of this law-level obstruction.

An inclusion receipt is not necessarily finality. If later rollback changes
the logical commitment after another player has already acted on its contents,
waiting only at settlement does not restore the earlier information structure.
An exact candidate interface must either make the relevant receipt irrevocable
within its declared fault model or model rollback as a source chance/failure
event. A probabilistic guarantee supports an approximate law claim; it does
not make positive-probability failures disappear.

For context, the official Ethereum gas description distinguishes the priority
fee used to encourage inclusion from the cost of execution. It is not a
worst-case inclusion theorem. The primary-source Bitcoin/Prism analysis states
explicit probability bounds for growth, quality, and common prefix under a
bounded propagation-delay assumption. Neither statement should be silently
replaced by certain inclusion by every fixed deadline.
[Ethereum gas documentation](https://ethereum.org/developers/docs/gas/),
[Continuous-Time Analysis of the Bitcoin and Prism Backbone Protocols](https://arxiv.org/abs/2001.05644).

A logical horizon counts source decisions. A physical horizon counts actual
opportunities to send, replace, route, bid, observe, and recover. Finitely many
source phases do not imply finitely many physical plans. A finite-plan proof
must specify finite physical menus and a bound on their use. A uniform risk
floor can also come from a different primitive argument, such as positive
probability of no usable block before a fixed deadline; a hard attempt bound
is sufficient, not necessary. Unbounded retries alone do not prove that this
probability can be driven to zero.

Fees also matter to impossibility statements. For a fixed comparison with
inclusion probability \(q\), write

\[
 g(q)=qS+(1-q)F-P-k(q),
\]

where \(P\) is the comparator payoff, \(S,F\) are success/failure base values,
and \(k\) is the incremental expected fee. If additional collection is
\(\alpha(1-q)\), a finite deposit works exactly when positive gains divided
by this risk have a finite common bound. Near-one inclusion is not itself an
impossibility: expensive priority may eliminate the positive gain. Conversely,
if some fixed-mechanics comparisons have gains bounded away from zero while
their additional collection tends to zero, no common finite deposit works.
This calculation assumes the values and kernels used in each comparison are
fixed; establishing them from equilibrium continuations is another theorem.

Almost-sure eventual completion without a fixed deadline can avoid a finite-time
failure floor. It changes the game: withholding can stall other decisions,
capital remains locked, and execution is no longer the finite game used in
the extension theorem. Existence and consistency then need an appropriate
infinite-game argument or a justified finite abstraction.

## Catalog cards

| Result or candidate | Conclusion | Status and limit |
| --- | --- | --- |
| Conditional gain/charge identity | Net gain is \(g-Kr\); sunk charges cancel. | Complete elementary proof for fixed comparisons. No consistency claim. |
| Sharp finite-collateral boundary | Zero-risk positive gains or an unbounded positive gain/risk ratio prevent a common finite penalty. | Complete proof; comparisons and utilities fixed independently of deposits. |
| Finite primitive collection tests | Positive collection for every hidden-history/action/pure-plan triple gives one positive uniform floor. | Paper instantiation argument; minimum/mixture component checked. Backend tests and realization still required. |
| Clean structural restriction plus audit | One fixed finite deposit vector extends every source SE, preserving clean initialized law and matching settlement. | General extension checked; a new backend still needs faithful restriction and collection adapters. |
| Adaptive bounded recovery | Pointwise badness survival \(\varepsilon\), at most \(N\) opportunities, and terminal collection \(\alpha\) give \(\alpha\varepsilon^N\). | Complete paper proof; related survival APIs checked. Kernel premises must cover fees and all future plans. |
| Unavoidable spent escrow | A certified early leak is profitable on a spent branch; every preserving SE is excluded, with TV error at least branch probability. | Complete finite-game paper counterexample. Does not refute deterrence of a first clean departure. |
| Concurrent capacity sabotage | A valid own opening can profitably force another reveal to fail; raising own-failure forfeitures does not help. | Complete finite-game paper counterexample. Requires joint service protection or accountable resource departures. |
| Fixed-deadline probabilistic publication | A policy-independent positive failure floor precludes an all-success exact logical law. | Elementary event proof; actual native outage obstruction checked. Not absence of target SE. |
| Fresh or additive collateral | Additional faults can have genuine additional cost. | Candidate repair; finite reserves, refusal, caps, and evidence must be specified. Does not repair information-changing lawful aliases. |

The [reviewed native two-late construction](native-late-action-analysis.md)
refutes uniform SE preservation over the declared timely contract builders
with fixed collateral above its stated thresholds, at paper level. It controls
the full bounded raw menu and actual capped settlement. General positive
results need a further public service or settlement property; native PBE
preservation remains a separate question. This is a concrete compiler/runtime
boundary, not a universal public-mempool impossibility or a general positive
theorem inferred from a local collateral comparison.
