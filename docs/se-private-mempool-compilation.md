# Private-mempool SE preservation: compiler and incentive choices

Rollback is a compiler recovery policy. It is not imposed by the ledger or the
existence of private mempools. Replacing recovery with an absorbing failure
outcome can remove the need to reason about survivor equilibria, remembered
voided values and retry archives. This does not create public knowledge:
failure becomes public only when the ledger records it.

The strongest positive design direction is to separate source choices from
source-blind execution mechanics, with successful execution paying the source
utility and failure paying a fixed floor. The mathematical product theorem
below explains why those two incentive problems can separate. Its conditions
are structural properties of a compiler, not a hypothesis that every player
sees the pending queue.

These are hand proofs and proposed compiler specifications. They do not change
the implementation, the existing theorem contract or the preservation checklist.
The [mathematical foundations](se-private-mempool-mathematics.md) prove the
observation, consistency, completion and finite-refutation results used here.

The [intended-game and quit-handler analysis](se-quit-handler-preservation.md)
separates intended-game SE from SE of a game already exposing Quit. It also
proves a source-level extension using only a first-quitter utility cap, with
arbitrary bounded survivor continuations. This can avoid an all-player abort
floor, but general handlers replace the common-interest operational proof with
handler-aware incentive and attribution obligations.

| Design | Benefit | Obligation or cost |
|---|---|---|
| Retain rollback | Survivors can continue. | Private-memory simulation and source-compatible continuation incentives. |
| Absorbing global abort with floors | Removes retries; hidden irreversible failure can have zero continuation gain. | Payoff floors, loss of survivor liveness, and actual compiler/source separation. |
| Abort with ordinary refunds | Simpler payout rule. | Fails SE preservation when a loser prefers the refund. |
| Canonical logical commitment slots | Removes handle-choice signaling and retry slot allocation. | An enforceable signed-packet rule and a separate cryptographic realization. |
| Automatic release / recoverable commitments | Removes selective withholding after binding. | New release, validity, availability and cryptographic assumptions. |

## Independent operational game: a complete product theorem

Let S be a finite perfect-recall source game with utilities u_i. Let O be a
finite perfect-recall operational game whose terminal output is a success bit
B, and whose utility for every player is B. All primitive source and operational
chance variables are independent; source private inputs may be arbitrarily
correlated with each other. Suppose some legal operational profile succeeds
with probability one.

First consider a literal independent product. Source and operation actions have
independent menus and transition laws. They run on fixed padded finite calendars;
the calendar must preserve the original source information, rather than reveal
a hidden branch through its timing. Their histories can be interleaved in a
fixed manner, but a choice in one component does not change the other component's
state, chance law, available actions, or decision opportunities. At each combined
information set (J,K), the possible component histories are the actual Cartesian
product J times K at that stage. Each player's current information is exactly
that pair. These restrictions ensure a product of reach weights; independent
initial seeds alone would not ensure it in an arbitrary interleaving.
The desired terminal readout depends only on the source terminal state and its
initial state. The combined utility is

    U_i = F_i + B (u_i-F_i),       F_i<=u_i(z) for every source terminal z.

The combined player may condition its deviations on both components. The
candidate source policy ignores K, and the candidate operation policy ignores
J. This restriction is on the constructed equilibrium, not on deviations.

**Theorem.** Every source SE extends to a combined SE with success probability
one and the same initialized source outcome/payoff law.

### Obtaining an operational SE that succeeds surely

At operational information set K, impose a strictly positive action floor
f_n(K,b), with total floor eta_n(K)<1 and maximum total floor tending to zero.
Choose a global maximizer kappa_n of the probability of success over the finite
product of these compact constrained behavioral simplexes. A maximizer exists.
Because a success-one operational profile exists, its small floor perturbation
has success probability tending to one; thus the maximizing profiles do too.

Treat each operational information set as its own agent, all with payoff B.
Global optimality implies an exact constrained best response for each agent.
Under the fully mixed profile every chance-supported information set has
positive reach. Changing its own action does not change that reach or its
Bayes belief, because perfect recall makes the set an antichain. Divide the
exact unconditional best-response inequality by this positive reach.
The residual action distribution is supported on actions maximizing conditional
success. Hence every pure local operational success gain is at most eta_n(K),
independently of how small the reach probability is. A common subsequential
Bayes limit is an operational SE with success one.

This is stronger than selecting an arbitrary operational Nash equilibrium or
an ex ante local optimum. The exact globally optimal constrained profile is
what supplies conditional control at all off-path operational sites.

### The common product consistency sequence

Let s_n be a fully mixed source sequence converging with its Bayes beliefs to
the selected source SE. Pair it with kappa_n, and take a common subsequence if
needed. The product profiles are fully mixed at the combined information sets.
Independent primitive laws and component policies give exactly

    mu_product,n(h_S,h_O | J,K)
       = mu_source,n(h_S|J) mu_operation,n(h_O|K).

This equality is asserted at every index, including sites that become off path
in the limit. It is not inferred merely from independence of the limiting
strategies.

Let p_n(K) be conditional success under the operation profile, and let
w_i,n(J)=E_source,n[u_i-F_i|J], including the prescribed future source play.
Put W_i=max_z u_i(z)-F_i. Then 0<=p_n(K)<=1 and 0<=w_i,n(J)<=W_i.
For a source local alternative a,

    G_product,n((J,K),a) = p_n(K) G_source,n(J,a).

For an operational local alternative b,

    G_product,n((J,K),b) = w_i,n(J) G_operation,n(K,b).

The first factorization uses the fact that the operational continuation ignores
the source action. The second uses the fact that the source continuation ignores
the operational action. If a single native move chooses a pair (a,b), its gain
is at most

    p_n(K,b) G_source,n(J,a)
      + w_i,n(J) G_operation,n(K,b).

In the literal product this is an equality with the evident baseline source
and operational expectations. Thus source local gain errors tending to zero,
and operational errors bounded by eta_n, give all combined local gain errors
tending to zero. Mixed alternatives follow by linearity. A common subsequential
Bayes limit is an SE. Operation success tends to one, so the limiting initialized
source law and payoffs are exactly preserved. QED.

An operational deviation may use all currently observed source information;
the proof applies separately at each pair (J,K). Multistep adaptive deviations
are covered by sequential rationality obtained from the one-shot principle.
No uniform rescue assumption at late operational sites is used.

### Exogenous state-dependent abort payoffs

The fixed number F_i can be weakened to F_i(theta), a function of initial Nature
that no semantic or operational action can change. Require
F_i(theta)<=u_i(z) for every source terminal compatible with theta. Under any
source local alternative, the conditional expectation of F_i(theta) is unchanged;
it cancels from the source gain. Operational gains are still multiplied by the
nonnegative expectation of u_i-F_i(theta). The same proof therefore applies,
with W_i=max_(theta,z)(u_i(z)-F_i(theta)) over compatible pairs.

At a doomed physical history theta is fixed, so all future choices have the same
base payoff even if the player does not know theta. Partial-opening conditioning
below also remains valid because theta belongs to the semantic state. This does
not permit action-, timing- or culprit-dependent abort rewards. Computing a
private-type-dependent payout in an actual contract is a separate obligation.

### Wait-or-send menus

The native menu need not literally be a Cartesian product. Suppose it is Wait
or Send(a), with a ranging over source actions. Let the operational component
choose Wait or Send with law kappa_n(K), and on Send draw a from s_n(J).
Thus P(Wait)=kappa_n(Wait|K) and
P(Send(a))=kappa_n(Send|K)s_n(a|J), a fully mixed native distribution.
Until sending, no new source observation arrives; a later prescribed send uses
the same source law s_n(J). Operational timing does not alter its conditional
source payoff factor. Write w for that baseline factor, w_a for fixing a now,
p for baseline operational success, and p_send or p_wait for the corresponding
local operational alternative. Then exactly

    G(Send(a)) = p_send (w_a-w) + w (p_send-p),
    G(Wait) = w (p_wait-p).

With source gain error at most eta_n and operational success gain error at most
zeta_n, these are bounded above by eta_n+W_i zeta_n and
W_i zeta_n respectively. The first identity also covers a valid alias or
route choice by replacing Send with its appropriate operational label. The
calculation fails if waiting reveals source information before the action is
fixed, or if success probabilities depend on the chosen source value.

## Allowing privately received semantic openings during mechanical work

The literal rectangular product can be weakened in a way matching a reveal
phase. Write X for the semantic state and its potential source continuation
randomness, and Z for the operational randomness. At an operational decision,
suppose the player's actual information has the form

    (K, V_K(X)),

where K is its source-blind operational view, determined by the operation
component, and V_K says which semantic data have been disclosed through that
view. For fixed K, V_K is a function of X alone. For example, K records which
opening packets were received, while V_K contains their values. The original
private input can be included in V_K. X and Z are independent before these
observations under the product policies.

Conditioning on (K,V_K(X)=v) leaves the operational posterior equal to its
posterior given K: after fixing K, the second condition concerns X alone.
The conditional source payoff factor changes, but remains nonnegative because
u_i-F_i is pointwise nonnegative. The operational success gain is therefore
still multiplied by a nonnegative scalar, so operational completion remains
sequentially rational even after privately observing favorable or unfavorable
openings.

The index must be the **observed** operational view K. It cannot secretly use
an operational state y that K hides. For example, let an independent source bit
X be known to a player, let an operational bit Y be hidden, and reveal X xor Y.
That player can now infer Y. This is not a projection V_K(X) when K does not
already identify Y. An operational policy that ignores the new signal can cease
to be optimal in a guessing subgame. Packet identities and receipt ordering
must therefore supply enough actually observed metadata to determine which
source projection is being disclosed.

At a source decision, a stronger requirement is needed: every semantic value
available in the native information must already belong to the original source
information J. A public reveal barrier supplies this only if all current-round
semantic choices have been irrevocably fixed before any opening can be received,
and the next semantic choice waits until the relevant public reveal is complete.
Merely saying that packet delivery is independent does not supply the barrier.

For several stages, the source and operational components can be coupled by
pre-sampling independent source behavioral randomization and chance tables and
an independent operational table. The operational profile ignores semantic
contents, and source policies ignore operational metadata beyond their original
source observation. A fixed padded stage layout ensures that the operation
component, its success bit, and its feasible actions do not depend on hidden
source choices. Under those structural conditions, induction over stages gives
the same likelihood and continuation factorizations used in the product proof.

This is an ideal staged-compiler sufficient condition, not a claim about the
present raw runtime. Important concrete obligations include:

* Packet counts, sizes, slots, routes, and valid alias choices must not expose
  hidden source values before their source reveal. Padding can make phase
  topology independent of source branches, including branches that terminate
  early. This has real communication and execution cost.
* Operational action labels such as wait, send the frozen commitment, or open
  the frozen commitment must have source-independent effects after semantic
  contents are erased. Correct cryptographic payloads may be generated from
  the frozen value, but their delivery/service behavior must not depend on it.
* The operation component must have a success-one profile under the fixed
  reserved-service law. Positive-probability unavoidable network failure would
  leave positive abort mass and prevent exact preservation of a source law
  having no abort outcome.
* Optional waits and aliases may be allowed as operational actions; the
  common-interest completion chooses their off-path behavior. Every such
  action must preserve the component separation. Type-dependent signaling
  capabilities are not automatically operationally irrelevant.
* Every out-of-menu raw packet must be classified. It must either be a genuine
  operational action in this source-independent game, make global failure
  irreversible, or satisfy a separately proved first-forbidden-packet incentive
  bound. Honest-path opacity alone leaves this classification open.

### A language-level batched source semantics

A clean target for this construction is a finite sequence of public-barrier
phases. Within one phase, each player chooses one private action vector, using
its original information at the start of the phase. The vector can contain all
of that player's source choices before the next public reveal. The compiler
uses one canonical commitment per player and phase, then performs the mechanical
opening protocol. All current vectors are fixed before any is opened, and the
next vector is selected only after the public barrier.

This makes source semantic concurrency explicit. Physical ordering of the
individual commitment callbacks is operational metadata, with no need to
declare an arbitrary physical submission order to be the semantic source order.
It does not impose a new public observation of pending packets or make omission
of a private callback an on-ledger offence.

There is a restricted source theorem that justifies this grouping. Assume each
phase has a fixed event order and finite layout, and each player's information
at successive events consists exactly of its phase-start information J_i and
its own earlier phase actions. Legal menus depend only on those data. Every
listed event occurs in order on every legal phase execution: there is no hidden
early exit or survival selection before a player's first event. Batch recall
retains prior own vectors and original barrier information.

**Batching theorem.** Every source SE induces a simultaneous-vector SE with the
same initialized terminal law under these conditions. No converse is asserted.

Let s_n be a fully mixed common source consistency witness. Define

    lambda_i,n(v|J_i) = product over i's phase events of
                        s_i,n(v_event | J_i, own earlier entries of v).

Every legal vector has positive probability. A player with no event has the
singleton empty vector. Pre-sample the other players' vectors and expose their
entries in the original event order. Because no player receives new external
information within the phase, this produces exactly the source law. Repeat at
each later public barrier.

A pure batch vector deviation is a legal source continuation deviation from
that player's first phase information set: choose its specified entries, then
resume the source continuation after the barrier. Pre-sampling gives equality
of conditional gains at every index n. To check the conditioning, preceding
unobserved foreign moves and chance branches have total mass one given J_i
and disclose nothing. Projecting the original first-site belief to phase entry
therefore gives exactly the batch entry belief; the sampled foreign vector
prefixes reconstruct the remaining conditional law at the original first site.

Source sequential rationality and finite continuity bound the finitely many
continuation gains by errors tending to zero. Take a common subsequential Bayes
limit of the full-support vector profiles. The gain bounds make it an SE, and
equality of initialized laws at each index gives the desired limiting law.
This uses independent behavioral randomization conditional on source information,
not independence of players' private inputs.

Actual Vegas phases still need to satisfy these hypotheses. Intermediate private
signals, hidden exits, source-relevant partial publication, or menus depending
on information outside J_i and own earlier actions need a different adapter.
A bare vector cannot commit a player before information the original game lets
that player use.

## A useful extension with funded audit enforcement

Suppose count-clean successful behavior has the staged product structure, while
extra raw packets can leave that structure. A funded audit can handle the first
forbidden packet when its sender's conditional charged payoff is bounded above
by F_i against every continuation, and a count-clean continuation has payoff at
least F_i. Pointwise coverage and a deposit satisfying q_i D_i>=Ubar_i-F_i,
where Ubar_i bounds every native base payoff, are one way to obtain this bound.
The inequality must cover the actual signed traffic,
not only packets that eventually reach the ledger.

Then use the finite common-sequence construction already derived: prescribe
source/operational component profiles at information sets meeting regular
count-clean histories; add smaller positive raw-error trembles; and choose all
remaining native actions by simultaneous constrained-agent completion. The
minimum regular witness reach determines the raw-error scale. Conditional
posterior error is bounded by H delta_n/a_n, uniformly over the free completion.
On regular histories, source/operation factorization controls successful
alternatives; global abort controls irreversible failures; and the audit
controls the first forbidden packet. The following closure and baseline
conditions are necessary for that inference.

After every regular supported local alternative, the reference must visit only
copied sites until a terminal boundary, including any privately doomed prefixes.
Couple actual and reference play until the first raw-error flag. Its probability
is at most H delta_n; after it the free continuation can be arbitrary. Let M_i
bound the entire NET payoff spread, including the fixed deposit. Each continuation
value changes by at most M_i H delta_n, and a local gain by at most
2 M_i H delta_n. Thus source and operational local errors eta_n and zeta_n give

    e_n <= eta_n + W_i zeta_n + 2 M_i H delta_n

under the reference posterior. Actual-posterior transport adds at most
2 M_i H delta_n/a_n as in the mathematical foundations.

Audit soundness is also needed: clean traffic incurs no charge. The reference
baseline is then at least F_i, and the actual baseline is at least
F_i-M_i H delta_n under the reference posterior. A universally forbidden or
irreversibly failing alternative has net value at most F_i, so its gain is
at most M_i H delta_n, before posterior error. It would be incorrect to compare
its value with a clean baseline and simply claim nonpositive gain against the
fully mixed actual profile, whose future errors can incur charges.

If abort ends the application but later audit-relevant emissions remain possible,
that is not a terminal boundary for this estimate. Either continue prescribing
clean doomed play with the same raw-noise control, or use free-site local
optimality and the downstream-regret theorem to bound loss relative to a clean
continuation by H_i eta_n. Merely knowing that the BASE payoff is fixed does not
make NET continuation gains zero when additional charges are possible.

This extension still needs its raw-menu and observation producers. In particular,
an accepted unusable binding is now genuinely irreversible doom, but a privately
sent off-ledger disclosure is not automatically a global abort. A compiler
cannot make that fact true just by changing its on-ledger retry rule.

## Why global abort alone is insufficient

Consider a single simultaneous source round. Nature gives a fair bit theta to
sender S. S's required source action is its forced truthful declaration of theta;
receiver R simultaneously guesses the bit without observing it. Both utilities
are one for a correct guess and zero otherwise. There is a source SE where R
always guesses zero, with the selected initialized joint law assigning that
guess independently of theta.

Suppose the compiler permits S to send a valid truthful opening privately before
R's commitment is fixed. This opening does not trigger abort. Suppose also that
at the resulting receiver information set no earlier hidden failure is possible:
S's validated declaration is the only preceding operation, and R has not acted.
After receipt, a valid guess completes the protocol successfully with no further
discretionary move by S and no other failure branch.
After receiving theta=1, R strictly prefers guessing one. On theta=1, S therefore
strictly gains by this early valid disclosure whenever it is received with
positive probability. Every compiled profile preserving the selected law has
the same profitable deviation. A global abort floor of zero or below does not
help, because the deviation never fails or aborts.

This counterexample establishes the need for a barrier or a separate incentive
bound on early disclosures. It does not refute a compiler that actually enforces
the stated all-choices-fixed-before-openings rule. It also shows why opacity only
along the prescribed honest path is weaker than what the theorem needs.

## Compiler redesign: global absorbing abort

Rollback is a recovery design choice. [CommitPhaseRecovery.lean](../Vegas/Source/CommitPhaseRecovery.lean) explicitly
retries surviving owners after a missed commitment, retains their private
histories, and bounds retries by the number of newly excluded owners.
the [phase application](../Vegas/Pending/PhaseApplication.lean) implements that choice. Guard well-formedness does not
mathematically require retrying: it ensures intended source actions can satisfy
the guards, whereas rollback describes what happens after a runtime failure.

A simpler candidate compiler can terminate the whole game on the first public
failure instead of continuing with excluded owners. Record that abort in the
actual ledger state; do not pretend a privately pending failure is already public.
Do not manufacture a complete source terminal on abort: expose an abort outcome,
which has probability zero in the selected preserved law. On honest paths the
existing timely service must ensure that every required action completes before
its deadline, so this change has no effect on the selected source joint law.

Suppose global abort gives every player \(i\) payoff \(F_i\), with
\(F_i\le u_i(z)\) for every source terminal and \(F_i\le0\). These are the same
numerical floor conditions already imposed on the individual exclusion payoff;
the semantic change is applying them to everybody on a global abort. Every abort
branch is then pointwise dominated by every successful source payoff, rather than
entering an arbitrary survivor continuation. The delay comparison in the delay theorem below
can treat abort as a genuine absorbing dominated outcome. There are no retry
archives, retired plaintext effects, or future survivor choices to reconstruct.
The clean private-view likelihood and legal source-deviation adapters are still
needed; global abort does not prove those automatically.

Without retry, the compiler can additionally assign a single static handle to
each owned commitment event, require evidence-free commitments, and make any
different handle a signed audit violation. This is a real compiler/enforcement
choice: it is checkable from the signed packet and public program, independently
of receipt or private callback time. It removes uncharged handle-choice signaling
and reduces the fresh-slot reserve to the program's fixed commitment slots.
Atomic private registration still binds the hidden value before transmission.
By contrast, requiring a packet to have been sent at the first private activation
is not comparably justified by signed content alone; waiting remains a legal
deviation requiring the delay argument. These canonical-handle rules are a
proposed new implementation, not the current permissive raw-menu contract.
Here a canonical handle is a canonical logical slot in the existing ideal
opaque-commitment interface. It does not assert that concrete hash-commitment
bytes can be made identical across different hidden values; the cryptographic
backend's hiding and binding realization remains a separate interface obligation.

### Refund-abort is sharply insufficient

Consider the matching-bit source example with clean payouts 126 to the winner
and 74 to the loser. Both players have staked 100. In the intended source game,
uniform independent commitments followed by mandatory disclosure form an SE.
Suppose a proposed global-abort runtime refunds the 100 stake on any failure.
In this particular variant, the last player can submit its opening only after
observing the earlier public opening. It therefore has an actual decision
opportunity after learning its payoff and before irrevocably sending its own
opening, rather than merely having its already-broadcast packet included later.
At each positive-probability information set where its committed bit will lose,
disclosure yields 74, while withholding until abort yields 100. The deviation improves
payoff by 26. Every profile preserving the selected complete terminal law must
reach these losing disclosure histories and disclose there; none can therefore
be sequentially rational. This is an exact refutation of that refund-abort
variant, not of a version retaining a pointwise abort floor.

### What makes a global floor financially realizable

An abstract utility floor is not automatically an executable transfer. In a
quasilinear model, let the player's unpenalized abort payoff (including retained
assets and external benefits) be at most \(G_i\), and every clean source payoff
be at least \(L_i\). Burning collateral

\[
 b_i\ge\max(0,G_i-L_i)
\]

on abort makes its actual abort utility at most \(L_i\), hence no greater than
any clean source payoff. The collateral must be collectible, and burning it must
not reward another participant. The abort utility need not literally be constant
for the immediate-abort and hazard arguments, which use pointwise domination.
This financial bound alone does not instantiate the common-success product
theorem or zero-gain hidden doom: those require their stated action-invariant
abort payoff structure. An operation succeeding with probability .9 but failing
at payoff -100 can be worse than one succeeding with probability .8 and failing
at zero, even when every success pays one. Maximizing success is then insufficient.
In a payout-only game, holding the pot in escrow and burning the prescribed
abort amount is a concrete implementation of the same condition. In a game with
unbounded external benefits or nonmonetary utilities, no finite collateral amount
follows from the current finite-payoff argument.

There is also an exact budget constraint. In a constant-sum payout game with pot
\(C\), write \(m_i=\min_z u_i(z)\). If each abort payout satisfies \(F_i\le m_i\),
then the amount removed from participant payouts must satisfy
\[
 C-\sum_iF_i\ge C-\sum_i m_i.
\]
Strict budget balance is impossible whenever \(\sum_i m_i<C\). In the 126/74
example, global floors require burning at least \(200-74-74=52\); refunding 74 to
each player attains the weak floor, while refunding 100 to each does not. Thus
the simple global-floor theorem requires permission for a burn or another
payoff sink in this example. It cannot promise both all-player floors and full
redistribution of the pot to the participants.

The maintained paper already separates computed payouts from executed transfers,
assumes collectible deposits and quasilinear utility, burns penalties, and excludes
capital-locking/reporting costs from the model. A global-abort redesign should
state its own payout rule in those same terms rather than infer it from arbitrary
abstract utilities.

The principal practical cost is that an offender can terminate the game and
destroy innocent players' escrow. Exact unilateral SE preservation permits this
because the offender cannot improve its modeled utility, but it supplies neither
collusion resistance nor recovery for honest survivors. Reserved inclusion and
activation bounds also remain substantive: if honest messages can fail with
positive probability, global abort generally occurs with positive probability
and changes the exact selected initialized law. Compiler rules can define an
abort response and ledger barriers; they cannot establish an unavailable network
delivery guarantee.

Exact preservation also depends on the utility model. Padding, extra packets,
collateral locking and waiting can change real costs even if successful nominal
payouts agree. If the model counts those costs, their contribution must be
included in the preserved payoff law. Existence of one preserving SE does not
rule out other equilibria that abort, guarantee recovery against malicious
players, or supply coalition resistance. A player already receiving its floor
may be indifferent to causing failure.

## Immediate absorbing abort is an exactly solvable extension

Start with any finite perfect-recall source game. At each information set
\(I\) of player \(i\), add an action `abort` that terminates immediately.
Its payoff to \(i\) may depend on \(I\), but is at most every one of \(i\)'s
source terminal payoffs. The other players' abort payoffs may be arbitrary
fixed bounded numbers. The original action menus, information, chance laws,
and continuation tree are otherwise unchanged.

**Claim.** Every source SE extends to an SE of this game that never aborts and
has exactly the same initialized joint terminal law.

Let \((s_n,\mu_n)\) be a legal fully mixed consistency sequence for the chosen
source SE. For any \(\delta_n>0\) tending to zero, define the target sequence

\[
 t_n(\mathrm{abort}\mid I)=\delta_n,
 \qquad t_n(a\mid I)=(1-\delta_n)s_n(a\mid I)
\]

for original actions \(a\). This is legal and fully mixed. If a source history
\(h\) contains \(k(h)\leq H\) earlier strategic decisions, its target/source
reach ratio is exactly \((1-\delta_n)^{k(h)}\). Thus every such ratio lies in
\([(1-\delta_n)^H,1]\), uniformly even at source-off-path information sets.
After normalization, target/source Bayes belief ratios lie in
\([(1-\delta_n)^H,(1-\delta_n)^{-H}]\), which tend uniformly to one. The
target Bayes beliefs therefore converge to the original source beliefs on
the original histories; no absolute lower bound on their reach is needed.

The limiting strategy never aborts. For every original local action, its
limiting continuation gain is exactly the source gain, hence nonpositive.
For `abort`, its payoff is no larger than every payoff in the support of the
prescribed source continuation, hence no larger than that continuation's
conditional expectation under any belief. Its local gain is nonpositive as
well. The same fully mixed target sequence supplies consistency at all sites;
perfect recall supplies sequential rationality. Since abort has limiting
probability zero, the entire source initialized joint law is unchanged.

The acting player's pointwise lower-payoff requirement is sufficient here;
an all-player abort floor is not logically necessary for this ideal immediate
extension. All-player floors become useful for a compiler with **hidden doom**,
where other players may still act before inevitable termination is observed.
If every doomed history pays a fixed vector independently of all future
actions and independently of which failure is detected first, all those
players' continuation gains are exactly zero. A culprit-dependent refund or
penalty vector does not have this automatic property.

Ordinary refund aborts need not satisfy the theorem's floor hypothesis. For
example, if a player's two possible successful settlement payouts are 126
and 74 but abort refunds 100, learning that settlement will pay 74 makes abort
strictly profitable by 26. Replacing a losing source payoff by a refund is
not neutral; the refund is above that source payoff. The exact existence of
the informative abort opportunity must still be established in any proposed
protocol.

## Delay with a type-dependent stopping hazard

A useful sufficient inequality does not require the event of successful
completion to be independent of the hidden source state. Fix a source
information set \(J\). Let \(X\) include every hidden state and source
continuation random seed needed to define a common counterfactual payoff
vector \((v(X,a))_{a\in A_J}\). Let \(Z\) be a potential operational
observation/randomization tape independent of \(X\) conditionally on \(J\).
For a particular legal waiting policy, suppose there exists a latent selected
action \(A=\alpha(J,Z)\). The word latent matters: if execution stops before
an action is selected, this is the action that the same policy would select
on the potential tape with that stopping event suppressed. Require that the
actual source action agrees with \(A\) whenever completion succeeds.

Let success \(S\) be any event, possibly depending on \(X,Z,A\). Suppose the
actual native payoff \(U\) satisfies

\[
 U=v(X,A)\quad\text{on }S,
 \qquad U\leq v(X,A)\quad\text{on }S^c.
\]

Then

\[
 \mathbb E[U\mid J]
 \leq\mathbb E[v(X,\alpha(J,Z))\mid J]
 =\sum_{a\in A_J}\Pr(A=a\mid J)\mathbb E[v(X,a)\mid J]
 \leq\max_a\mathbb E[v(X,a)\mid J].
\]

The first inequality is pointwise; the equality uses the independence of the
whole payoff vector from the latent selection. No independence of \(S\) is
used. If the prescribed source policy is \(\eta\)-optimal and its native
implementation loses at most \(e\) in expected payoff, the waiting policy's
native gain is at most \(\eta+e\). An additional nonnegative pointwise coupling
error with conditional expectation at most \(b\) adds \(b\) to this bound.

One operational producer is a process whose hidden source state affects
execution only by an absorbing stopping hazard. Until stopping, the policy
sees successive prefixes of the independent potential tape \(Z\). Run the
policy counterfactually on the whole tape with the stopping hazard disabled;
that defines \(A\). On any actual path that completes before stopping, its
choice is the same. Even survival can change the player's beliefs about
\(X\); this does not defeat the inequality, because completing paths agree
with an independent potential action and stopped paths receive a pointwise
dominated payoff. Hidden-state-dependent nonabsorbing messages, response
changes, or arrival timing generally do not admit this construction.

If the hazard-suppressed run never selects an action within the finite
horizon, assign any fixed legal fallback to \(A\). The comparison still
requires the actual noncompletion payoff to be bounded by the payoff of that
fallback; a source payoff floor below every legal action is sufficient.

Several weaker premises would be insufficient:

* A failure payoff below the **average** source value does not suffice. Let
  \(X\) be fair, with one source action having payoff \(v(0)=1\),
  \(v(1)=-1\). Success occurs only at \(X=0\), and failure pays zero. The
  failure payoff is at most the source expectation zero, but the native
  payoff is \(1/2\). The pointwise domination fails at \(X=1\).
* If \(v(x,a)\) is merely an expected continuation value, selection on future
  source randomness can invalidate the successful-payoff equality. Either
  include that randomness in \(X\), with the needed independence, or prove a
  conditional continuation comparison after selection.
* Independence of an initial random seed is insufficient if the potential
  transcript also depends on hidden-state-dependent packet contents, counts,
  or timing. The mathematical foundations document's no-receipt example gives such dependence.
* A public rollback need not pay the focal player an exclusion floor. If it
  leads to a free continuation, that branch needs its own continuation
  comparison or an argument that the focal old action has been erased and
  all relevant continuation laws agree. Its probability need not be small.
* The common payoff vector must use the actual opponents' continuation
  behavior or a proved source comparator for it. A waiting policy can change
  opponents' observations and future choices; equality of final marginal
  source state laws does not by itself control this response.

To apply this bound to all native waiting deviations, the potential-action
construction and the payoff comparison must hold for each legal policy. It is
not enough to prove them for an honest fixed waiting schedule.

## Why several tempting actual-runtime attacks fail

### A forced own exclusion cannot strictly improve payoff

Write \(F_i\) for the fixed exclusion payoff. The retained payoff assumptions
give \(F_i\le0\) and \(F_i\le u_i(z)\) for every complete source terminal \(z\).
Exclusion is permanent. Thus a continuation that makes player \(i\) excluded
surely has base payoff exactly \(F_i\), irrespective of subsequent retries,
new information, other policies, or the realized source terminal. A nonnegative
audit charge only lowers it. Any count-clean continuation whose base payoff is
a source terminal payoff, default zero, or the exclusion floor has expectation
at least \(F_i\), under every posterior.

It follows that “cause my own omission, see a favorable retry, then collect its
source payoff” is not a profitable attack: the final payoff is still \(F_i\).
This does not prove that every deviation with some exclusion risk is harmless.
For prescribed value \(V_i\), nonexcluded improvement bound \(B_i\), and own
exclusion probability \(p\), one only gets
\((1-p)B_i-p(V_i-F_i)\) before audit costs. If \(V_i=F_i\), the second term gives
no strict deterrence.

Relevant source: `Vegas/Game/PhaseExclusionPayoff.lean`, especially permanent
exclusion and terminal-payoff statements; the [concurrent contract](../Vegas/Game/ConcurrentRawSequentialPreservation.lean)
includes the floor assumptions in its bounded-payoff assumptions.

### The first count-forbidden packet is globally dominated

Let \([L_i,U_i]\) contain all base payoffs, including default zero and the
exclusion floor. Let \(q_i\) be observation rate times conditional delivery rate,
and \(D_i\ge0\) the deposit. The retained funding premise is
\(q_iD_i\ge U_i-L_i\). For an actual newly emitted forbidden signed packet, its
verdict cannot change under a later continuation. The audit coverage is pointwise
in complete signed traffic, and therefore gives, conditionally at any current
information set and against every continuation,

\[
 \mathbb E[\text{net payoff}_i]
 \le U_i-D_i\Pr[\text{charge}_i]
 \le U_i-q_iD_i\le L_i.
\]

A continuation that keeps the player's own traffic count-clean incurs no own
charge and has base payoff at least \(L_i\). Therefore the first forbidden packet
cannot give a strict improvement. Independence of the audit and game evolution
is not needed. This argument is about the first such packet: after the player
already sent one, the audit uses a Boolean charge and another packet need not
incur an additional deposit. Those later information sets need free rational
completion.

The signed count verdict rejects malformed packets, premature masked-token calls,
duplicate packets for a physical event, reused commitment handles, and incorrect
opening certificates. Private selective delivery of an early forbidden opening
does not remove its audit consequence. Source: `PhaseCountVerdict.lean`,
`ReactiveCountVerdict.lean`, `PhaseCountCollection.lean`, and
`Interaction/ReactiveAuditContinuation.lean`.

### An unusable commitment is not immediately an exclusion

This distinction matters. [ExclusionApplication.lean](../Vegas/Pending/ExclusionApplication.lean) explicitly leaves the owner
unexcluded after acceptance of an unusable binding. Exclusion follows an owned
expiry or a failed public opening. the [event submission step](../Vegas/Pending/EventApplication.lean) freezes the
candidate before transmission, so a sender cannot send a fresh handle, inspect
new traffic, and then prepare its value. A replacement for the same physical
event is count-forbidden. Once unusable binding debt has entered the saved
semantic checkpoint, [PhaseProposalSavedDebt.lean](../Vegas/Game/PhaseProposalSavedDebt.lean) propagates it through arbitrary
future policies and retries and proves the terminal exclusion payoff.

However, an unusable binding in the current commitment phase can be voided if
another owner misses and forces rollback before the phase is saved. Thus
“unusable submission implies own floor under every continuation” is false.
With promptly responding canonical opponents, this escape requires another
mechanical error, and can plausibly be bounded by that error probability. The
claim must be conditional at the actual information set, not an unconditional
small-probability argument.

In particular, treating *all waits* as regular produces a difficulty: a last
useful activation can be missed before the public expiry is recorded. At a later
information set a retry may already be inevitable, despite the public excluded
set still being empty. An unusable current binding may then be safely voided.
This is a counterexample to the proposed floor proof step, not to SE preservation.
A canonical prompt-response skeleton avoids calling every such history regular;
legal waiting deviations still require a separate timing/no-new-information
argument.

### Selective retry knowledge is principally an off-path completion problem

Rollback retires the attempt namespace; retired packets cannot regain application
validity. The retry follows a publicly recorded exclusion. Its survivors may
remember different private disclosures and may rationally play a different
continuation from the source. The capstone preserves the initialized joint law,
not the entire off-path assessment. Therefore an off-path survivor who profits
from private retry information does not by itself contradict the theorem.

A valid counterexample must show why all preserving SEs fail: for example, an
uncharged nonexcluding unilateral deviation that gains from the extra information,
unavoidable loss of source information, or incompatible consistency constraints
at information sets whose behavior is forced by the selected initialized law.

Off-path completion cannot simply be done as independent subgames after public
exclusion. A player can privately know that it made an invalid preparation or
sent a forbidden packet before any public exclusion, while other players remain
at information sets compatible with regular play. Joint constrained equilibrium
completion, together with rarity bounds at copied information sets, addresses
the correct mathematical shape. A proof must also handle uncharged aliases and
waiting, whose dominance does not follow from the audit inequality.

## A rollback comparison with legal private simulation

Fix a native information set \(I\), its belief, the opponents' policies, and
the fixed scheduler/chance law. Let \(b\) be an unusable or otherwise bad local
action and \(g\) a proper local action. The relevant dominance statement is
directional: for **every** legal continuation \(\tau_b\) after \(b\), construct
one legal continuation \(\tau_g\) after \(g\). It is not enough that each
actual hidden history admits some individually favorable continuation.

A sufficient operational construction has the following parts.

1. Until a stopping time \(T\), couple the two executions from the same
   initial hidden history at \(I\). The coupled histories give every other
   player the same complete private observation history and give the
   scheduler the same environment observation history. The focal player has
   a causal private simulator: from its good-side observed history and its
   own simulator memory/independent coins, it reconstructs the bad-side
   observation history and applies \(\tau_b\) there. Its translated good-side
   action is legal. The simulator never reads the global hidden state.
2. The transition kernels admit a coupling preserving this relation at each
   step. Since all other agents see the same histories, their fixed policies
   can use identical action draws. Identical scheduler observations similarly
   preserve the fixed scheduler policy. Fixed private-reception kernels must
   either receive identical physical inputs or have an explicitly verified
   coupling with the required observation relation.
3. At \(T\), either the current phase rolls back, or the bad process enters
   irreversible own failure, or the comparison terminates without either.
   The good-side simulator can recognize the branch from its own simulated
   observations. At rollback, the residual states satisfy a continuation
   simulation of the same kind, preserving the focal payoff. This simulation
   may keep the bad old action in private memory; no player is required to
   forget what it did. At own failure or a terminal nonrollback branch, the
   bad payoff is bounded by \(F\), and a single legal good continuation
   available on that branch attains payoff at least \(F\) under the coupling.
   The bound and the continuation must be uniform across the hidden histories
   compatible with the good-side information. Branches on which neither
   stopping condition occurs before the horizon must also satisfy an equality
   or domination comparison; they cannot be silently discarded.

These conditions can be checked locally using a relation on augmented
physical states and simulator memories: each translated focal action has a
correct-marginal transition coupling, all supported successors remain in the
relation or enter one of the stated terminal cases, and the simulator's update
is measurable in its own available data. Finite induction then constructs
the coupled complete executions and an implementable good policy. This is
stronger than merely postulating a terminal coupling, because it enforces
legality of the policy and reactions of the other agents step by step.
Private simulator memory can be expressed as a mixed strategy over private
contingent plans; in a finite perfect-recall game, its own-information
behavioral realization is an equivalent legal continuation.

On the rollback event \(R\), the coupling gives equal focal payoffs. On
\(R^c\), it gives \(U_g\geq F\geq U_b\). Consequently

\[
 \mathbb E[U_g-U_b\mid I]
 =\mathbb E[1_R(U_g-U_b)\mid I]
  +\mathbb E[1_{R^c}(U_g-U_b)\mid I]
 \geq0.
\]

There is no small-rollback-probability premise. Rollback may occur almost
surely. Initial private types may be arbitrarily correlated because the
argument begins with the actual conditional belief and couples from the same
hidden history. It is equality of the relevant observation histories, not
independence of initial types, that keeps the fixed opposing policies aligned.

The equality branch may be replaced by a conditional expected error of at
most \(e_R\), and the other branch by a domination error of at most \(e_F\).
The conclusion becomes
\(\mathbb E[U_b-U_g\mid I]\leq e_R+e_F\), with the errors already weighted by
their branch probabilities. Dividing by a rare branch probability is neither
necessary nor justified.

### What this proves about equilibrium, and what it does not

Let \(\sigma\) be the candidate prescribed continuation. Applying the theorem
with \(\tau_b=\sigma\) shows

\[
 V(b,\sigma\mid I)\leq V(g,\tau_g\mid I).
\]

It does **not** by itself show
\(V(b,\sigma\mid I)\leq V(\sigma\mid I)\). The constructed \(\tau_g\) may
use future behavior different from the prescribed \(\sigma\), especially on
the rollback branch. A conclusion that the bad one-shot action has
nonpositive gain therefore needs one of the following additional bridges:

* The good continuation supplied by the simulator is the prescribed one, or
  has conditional value at most that of the prescribed one under an already
  established local rationality theorem for the relevant downstream sites.
* The **whole** legal good continuation, including its behavior after
  rollback, transports to a legal source deviation, with a gain comparison
  against the same baseline. Source sequential rationality then bounds that
  continuation's gain. Transporting only its first proper action is not
  enough.
* The candidate completion is constructed to be invariant under the shadow
  relation, and a separate continuation theorem establishes that this
  restriction preserves all free-site optimality. Merely observing that old
  choices have been removed from the public state does not establish this
  invariance: they remain in the player's perfect recall.

Thus bad-action weak dominance by an available alternative is useful but is
not a substitute for copied-site sequential rationality. In particular, an
arbitrary free-site equilibrium completion can condition on remembered old
choices. If a shadow argument compares two different such continuations, the
gain must still be connected to the prescribed baseline.

### A rigorous downstream-regret bridge

At a fixed **fully mixed** native profile \(\sigma_n\) with its Bayes beliefs,
perfect recall supplies one useful bridge. Fix the current information set
\(I\) and the proper action \(g\). Suppose every later own information set
reachable after \(I,g\) has one-shot regret at most \(\eta_n\) against
\(\sigma_n\). For any legal continuation \(\tau\) of this player, while all
other players retain \(\sigma_n\),

\[
 V(g,\tau\mid I)-V(g,\sigma_n\mid I)\leq H_i\eta_n,
\]

where \(H_i\) bounds the player's number of later decisions. The tiny reach
of a later information set causes no additional denominator.

To prove this, note first that the player's information set \(K\) fixes its
own earlier information/action sequence. Under a unilateral behavioral
continuation change, the ratio of reach probabilities of each history in
\(K\) is the same product of changed own action factors. Hence the posterior
within \(K\), whenever reached under the deviation, is the Bayes posterior
under \(\sigma_n\). Conditioning on \(I,g\) does not change this conclusion
because every later \(K\) in question recalls that same earlier information
and action. A private-memory implementation has an equivalent behavioral
realization by perfect recall.

Now telescope the prescribed continuation value along a play generated by
\(\tau\). Chance moves and other players' fixed moves have zero expected
increment. At each own decision \(K\), the expected increment is the
\(\sigma_n\) one-shot advantage of the action chosen by \(\tau\), averaged
under that same Bayes posterior. It is at most \(\eta_n\). At most \(H_i\)
such increments occur, proving the bound.

Combining this with the shadow comparison gives

\[
 V(b,\sigma_n\mid I)-V(\sigma_n\mid I)
 \leq G_{\sigma_n}(I,g)+H_i\eta_n
\]

(plus any shadow-comparison error). Thus a source-comparable proper-action
bound and already bounded future own regrets suffice; exact equality with
the prescribed shadow continuation is unnecessary. One can attempt backward
induction on the player's own decision count, which increases along its
perfect-recall precedence relation. Since the tree is finite, any fixed
finite amplification of errors tending to zero still tends to zero. This
does not supply the proper-action comparison or the shadow coupling itself,
but it removes a potential circular demand that the free completion ignore
all old private memories.

## Existing ingredients for retaining rollback

The [private policy shadow](../Vegas/Pending/ReactiveBindingShadow.lean)
reconstructs original own observations and responses from repaired private
state and runs a supplied policy on that reconstructed recall.
[PhaseBindingShadow.lean](../Vegas/Pending/PhaseBindingShadow.lean) connects the
reconstruction with phase restoration and completion.
[PhaseBindingRepairObservation.lean](../Vegas/Pending/PhaseBindingRepairObservation.lean)
establishes public-view and foreign-player-view preservation for an own-binding
repair. These are useful ingredients for the directed simulation above,
including under arbitrary observation rules.

The operational transition, response-menu, certificate and terminal-payoff
conditions must still be connected. An extra repaired certificate must not force
an observable difference. Restricting first to count-clean policies helps:
freshness and latest-binding checks can make an old voided handle unusable for
future permitted emissions. A deviation can first be normalized at its first
forbidden packet using the audit bound, instead of comparing arbitrary future
audit charges after the two histories diverge.

The existing native repair can choose a typed value; that is not automatically
a guard-satisfying source-legal action. A source-policy comparison additionally
needs a legal intended value obtainable from the owner's actual source
information. Public-view equality, a typed value and an unconstrained terminal
coupling are each weaker than the required policy simulation.

There is a possible backward-induction bridge. Under a single fully mixed
perfect-recall profile, changing an earlier own policy does not change the
conditional posterior at a later own information set that records the same
earlier actions. If every later own site has local regret at most eta, a
continuation deviation can improve payoff by at most H_i eta. Combining this
with the directed simulation bounds the bad action by the proper action plus
H_i eta. The proper-action comparison must already be available independently;
otherwise this is circular.

## Other reasonable compiler changes

An immediate public abort can be modeled as an explicit language outcome,
outside the successful source record. Its probability is zero in the preserving
equilibrium; no invented successful terminal value is needed on aborted runs.
By contrast, replacing a missing source value with a default value preserves
the source game only if that value is source-legal at every applicable private
type and the new strategic default option is controlled. Guard well-formedness
does not automatically give a publicly computable universal default.

An ideal recoverable commitment can make valid committed values available after
a public barrier without the owner's cooperation. This removes selective
withholding, but needs public validity checking and an actual release mechanism.
Threshold decryption introduces availability/trust assumptions; time-lock
release introduces timing/computation assumptions. An early private plaintext
must not become available before dependent choices are fixed. These are proposed
model interfaces, not consequences of a ledger.

For an exact finite-SE theorem, the commitment/release interface is ideal.
A computational cryptographic implementation requires a corresponding
computational equilibrium or simulation statement, not an assertion that
computational hiding supplies exact equality of finite posterior laws.

Public barriers and canonical logical slots are compiler choices. A guarantee
that an honest required message reaches the ledger before a deadline is a
service assumption. Treating a missed private callback as a publicly provable
offense requires evidence the proposed model does not supply. Any safe-cutoff
proposal must specify whether it is an observable inclusion deadline or an
independently authenticated emission deadline.

## What remains to instantiate in Vegas

For an absorbing-abort compiler, first fix the actual abort payout rule and
public failure transitions. Then establish the source equivalence of the
phase/batch layout, the operational projection and its source blindness,
the information available at each semantic decision, and classification of
every raw local alternative. A first forbidden packet can use the funded audit
bound; a nonexcluding uncharged action must appear in the operational game or
have its own value comparison.

For a rollback compiler, the directed private-shadow comparison is a credible
alternative to assuming foreign retries rare. The baseline continuation bridge
remains essential. These are different compiler designs and should not be
mixed into one proof by silently changing the failure semantics.

The private-mempool observation model can remain ledger-only, private receipt
sampling or suitably stateful gossip. The probability law and its accessible
metadata must satisfy the stated compiler theorem; the proof never promotes
unseen packets to common knowledge. Arbitrary adaptive builders, concurrent
reveals before all dependent choices are fixed, and missing timely service are
separate extensions.

The generic product and restricted batching theorems are potential GameTheory
library additions, using the existing consistency/completion infrastructure.
The source-to-phase interpretation, canonical slots, failure transitions,
raw-message classification and payout realization belong in Vegas. No Multitubes
rewrite or dependency is required for this route; any use there would be a
separate theory/example decision.
