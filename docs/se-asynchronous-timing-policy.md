# Optimal asynchronous timing and source incentives

This note asks when source-preserving behavior can use an optimal timing policy
instead of an unconditional prompt-send prescription. The answer is positive
for an exact separable completion process, and is not implied by bounded
inclusion alone. The lemmas are finite mathematical modules, not an asynchronous
preservation capstone or newly checked Lean declarations.

The publication and private-information interfaces are in
[the asynchronous publication contract](se-asynchronous-publication-contract.md).
The indexed reference-information argument and its service boundary are in
[the asynchronous reference analysis](se-asynchronous-reference-information.md).

## The success-or-exit fact

Fix a well-formed opening of a player's accepted commitment in an actual
installed resolve phase. Once that resolve event has completed, either:

* its owner is unexcluded, in which case its successful opening and certified
  value have already been included in the public ledger; or
* its owner is permanently excluded, and its base terminal utility is F_i
  under every later continuation.

An owned event cannot disappear unfinished when a phase closes. Completion of
an unexcluded owned event has an actual authenticated packet; the existing
surface is `Vegas.EventGraphRuntime.phase_completed_owned_message` in
[PhaseCompletionStampHistory](../Vegas/Pending/PhaseCompletionStampHistory.lean).
For a resolve event, failed publication or expiry excludes its owner. The
permanent payoff conclusion is
`Vegas.phase_excluded_terminal_payoff` in
[PhaseExclusionPayoff](../Vegas/Game/PhaseExclusionPayoff.lean).

Thus, at a subsequent binding phase, an unexcluded owner's earlier resolved
value is public. This is weaker than publication of every submitted proposal:
a failed owner's correct opening may remain private, be replaced, or arrive
after its game effect is obsolete. Same-value replacement that succeeds still
publishes that same certified value.

The fact concerns the failed sender's utility. It does not put a survivor's
utility at that floor, and does not identify survivors' beliefs about the
failed sender's hidden values. It also does not make a transmission made
before exclusion a uniformly losing deviation: it may still succeed. That
case needs a success/continuation comparison, not the post-exclusion shortcut.

The `none` branch of a qualified comparison law is only bookkeeping; it is
not such a failure-payoff theorem. Nor does a scalar comparison at each full
source site J permit merging sites that differ in a missing failed-owner
proposal. Their prescribed actions can differ, and averaging those actions
loses their correlation with the hidden proposal. The exact distinction and
a finite information counterexample are in
[the archive analysis](se-asynchronous-reference-information.md#9-successful-delivery-does-not-automatically-replace-the-proposal-archive).

## An exact scalar timing theorem

Fix a source information set J. Let X describe the hidden source history and
all counterfactual source continuation randomness relevant to this local
comparison, with conditional law mu_J. For each legal source action a, let
u(X,a) be its source continuation payoff. Let F(X) be the fallback payoff,
fixed by the source state rather than by the selected timing policy, and assume

    F(X) <= u(X,a)                  for every supported X and legal a.      (1)

The constant exclusion payoff F_i is the main application. The more general
fixed-state fallback permits the same calculation.

An operational policy tau chooses when to send, wait or retry using its actual
operational observations. Assume the following concrete separation.

1. Conditional on J, the operational randomness Z is independent of X. Its
   observations, menus and transition kernels do not inspect the hidden
   semantic action/value or the unobserved payoff vector.
2. The legal operational policies are the same for every semantic action a.
   A policy may observe and react to Z, but cannot gain an additional source
   signal unavailable at J before choosing a.
3. Success S(tau,Z) is independent of a. On success, the selected source
   continuation is exactly u(X,a). On failure, the payoff is exactly F(X).
   Timing does not select another source opponent policy or another handler.

These conditions imply

    V_J(a,tau)
      = E[F(X)|J] + q_J(tau) E[u(X,a)-F(X)|J],
    q_J(tau) = Pr[S(tau,Z)=1 | J].                                (2)

Proof: write the payoff as F+S(u-F). Conditional independence factors the
second expectation. No division is used. In particular, zero success
probability is allowed.

Let q_J^* be the largest achievable success probability. Finiteness gives an
optimal operational policy tau_J^*. By (1), a policy maximizing q is optimal
for every fixed a. If a^* is source-optimal at J, then

    V_J(a,tau) <= E[F|J] + q_J^* E[u(X,a^*)-F(X)|J]
                 = V_J(a^*,tau_J^*)                              (3)

for every a and tau. Source ties remain ties. If the source surplus is zero,
the actor is indifferent over timing and may still use the common max-q
policy. If q_J^*=0, all semantic actions are indifferent in the completion
process, but that observation alone does not preserve the source outcome law.

The optimal timing can depend on the actual operational observation. It need
not be a fixed send time or prompt send. Its independence from a is the useful
conclusion. When different private source types induce the same operational
model, choose the same max-q policy for all of them; no type-dependent timing
signal is required.

### Choosing the semantic action after observing operational noise

The theorem also covers a joint policy that delays selection of a and chooses
A(Z), provided its operational transitions do not depend on that semantic
choice. Conditional on the operational realization,

    E_X[u(X,A(Z))-F(X) | J,Z]
        <= max_a E_X[u(X,a)-F(X)|J].

Multiply by the nonnegative success indicator and average. The joint policy's
success probability is at most q_J^*, so (3) still bounds its value. This
rules out a hidden advantage from choosing an action after observing merely
source-independent network noise. It does not cover a new observation of X.

## Dynamic timing requires separation at every continuation

An independence statement at the phase's initial state is insufficient if
later operational observations reveal hidden source information or later
menus depend on the chosen value. Require the preceding separation at each
operational information history o at which the player can still act. Retain
the complete local observation/action history, so there is no absentmindedness.

One concrete producer is a finite partially observed completion process whose
state, observation and transition kernels depend on the public source position
and operational history, but not on the source hidden realization X or the
semantic action a. Its private random seed is independent of X. The action
menus are fixed by operational history. The player can use all legal adaptive
operational policies; the domain is not narrowed after seeing a hidden state.
This is a one-controller decision process, or a local comparison with the
other participants' operational policies already fixed. Simultaneously choosing
separate best replies for several owners is not a proof of a joint operational
equilibrium.

The Bellman value is the maximal remaining success probability:

    q^*(o) = max_b E[q^*(next operational history) | o,b],

with terminal values 1 at success and 0 at failure. Choose a maximizing action
at every o. This one policy is optimal after every operational history, not
only initially. The same policy remains optimal when success is multiplied
by any nonnegative source surplus that the operational observations do not
update.

There is a precise rectangularity requirement here. At each information set,
the available continuation policies and their kernels must be shared across
the hidden source histories being averaged. Optimizing separately in each
hidden history would produce an illegal policy with information the player
does not have.

### A whole fully mixed sequence

Let beta_n be one fully mixed source sequence whose Bayesian assessments
converge to the chosen source SE. Finiteness gives

    R_n = max(0, all source pure one-step gains under beta_n) -> 0.

Use the same source action law in the operational extension. At every
operational information set, mix a Bellman-maximizing action with a full-support
law, with total perturbation eta_n>0. Suppose at most D operational decisions
remain. Coupling with the maximizing policy until the first perturbation gives

    0 <= q^*(o)-q_n(o) <= D eta_n                              (4)

uniformly in the starting information history. No lower bound on its reach
probability appears in this conditional continuation estimate.

Let B bound every nonnegative success surplus u-F. For a joint current
alternative with semantic action a and operational action b, write q_b for
its success probability followed by the perturbed reference continuation,
q_n for the prescribed one, and g_a=E[u(X,a)-F(X)|J]. If g_n is the source
profile's mixed surplus, then

    q_b g_a - q_n g_n
      = q_b(g_a-g_n) + (q_b-q_n)g_n
      <= q_b R_n + D eta_n B
      <= R_n + D eta_n B.                                    (5)

For a semantic-only deviation, the timing factor is the same on both sides
and the exact bound is q_n R_n. For an operational-only deviation, the first
term is zero. Mixed current alternatives follow by averaging. These statements
require the source posterior at the actual joint information set to be the
correct source posterior, as supplied by the separation or an explicit
likelihood factorization; they do not follow from an unconditional product law.

The same finite sequence is used at all sites. Compactness supplies one
subsequence of its strategies and Bayesian beliefs. The uniform bound (5)
vanishes, proving local rationality of the limit under perfect recall.
This is the consistency argument; prescribing optimal limit behavior alone
would not determine off-path beliefs.

For several such stages, require the same conditional separation and legal
policy correspondence at every stage. If every fresh stage has q^*=1,
and the number of remaining stages and decisions is bounded, future
operational perturbations contribute another uniform O(eta_n) continuation
error. The probability of any operational failure on the preserved execution
also tends to zero. Thus the initialized source terminal/payoff law is
preserved in the limit. If some fresh stage has q^*<1 on a positive-probability
source path, its failure outcome generally prevents exact law preservation.

This gives a genuine sufficient class: source-blind completion processes with
the same semantic continuation on success, an own-payoff floor on failure,
and attainable certain success at each fresh source stage. It is narrower
than concurrent recovery where a foreign failure can restart the phase or
select a different survivor continuation.

## Exact limits of the scalar reduction

### Marginal success probability is not enough

Without independence, the exact formula is

    V_J(a,tau) = E[F|J] + E[S_tau (u_a-F)|J].                    (6)

For every bounded payoff function f(X), the identity

    E[S_tau f(X)|J] = q_tau E[f(X)|J]

holds if and only if E[S_tau|X,J]=q_tau almost surely. Necessity follows by
testing indicators of each supported X; sufficiency follows by conditioning
on X. For a fixed game it is enough to have this identity on its actual span
of continuation payoff differences. An all-functions independence requirement
can therefore be stronger than necessary, but a marginal success number alone
proves neither version.

For example, let X be a fair bit, F=0, and let the source actions have payoffs

    u_a(0)=u_a(1)=2,       u_b(0)=3, u_b(1)=0.

The unique source optimum is a, of value 2 rather than 3/2. Suppose completion
succeeds exactly when X=0, independently of the selected action. Both actions
have marginal success probability 1/2, but their implemented values are 1 and
3/2. The ordering reverses. This example violates the required source/service
separation; it is a counterexample to inferring (2) from equal marginal success,
not a claim that every opaque, source-independent service has this behavior.

### Action-dependent success changes source comparisons

Even with no hidden state, source payoff a=2 can lose to payoff b=1 when their
maximal completion probabilities are q_a^*=1/4 and q_b^*=1, with F=0.
The completed values are 1/2 and 1. For all possible nonnegative payoff
assignments, preserving every source optimum requires the same maximal
success coefficient across semantic actions. If two coefficients differ,
choose payoffs with a sufficiently small strict advantage for the action
having the smaller coefficient to reverse the order.

Opaque commitment packets help establish action independence, but do not
prove it by themselves. Opening size, gas requirements, fee choices,
value-dependent validation, builder priorities or reaction to extra metadata
can reintroduce action dependence. These must be controlled by the actual
envelope and service specification.

### A foreign failure is not the focal player's floor

Let the source values for a focal player be a=2 and b=1. A foreign player's
failure occurs with probability 1/2 independently of the focal action. On
the ordinary branch those are the payoffs; on the foreign-failure handler
branch let the focal payoffs be a=0 and b=4. The focal expected values are
1 and 5/2. Replacing the handler branch by its own exclusion floor would give
the wrong comparison: the focal player was not excluded.

The example can be interpreted as a later subgame with those continuation
values; no strange utility function is required. It shows why maximizing a
single success probability does not solve a setting with survivor-dependent
quit handlers or rollback continuations. It does not prove that the whole
expanded game lacks a source-preserving SE; it refutes this particular
continuation reduction.

### Timing can select a continuation even if rollback erases the value

Suppose a foreign failure is already unavoidable. Both focal SEND and WAIT
lead to rollback, which erases its current proposed value. If SEND produces a
public retry record selecting a continuation of value 0 and WAIT produces one
selecting a continuation of value 1, WAIT gains despite identical semantic
rollback states. A common continuation must be justified across the distinct
public and private records. Arbitrarily completing new information sites does
not establish that comparison.

An optimal timing policy could select the better branch in this example, but
that does not show the resulting source action kernel, other players' incentives
or a common consistency sequence are preserved. Those are separate obligations.

## Insertion monotonicity and retrying the same entry

A useful service condition is weaker than a public calendar or full queue
flushing. Fix the other admitted entries and one service random realization.
For a canonical entry x, let T(x,A) be its recording time when copies are
offered at a nonempty finite set A of admissible retry times. An earlier
insertion time a must also be admissible and no earlier than the entry's
public readiness. Assume

    a <= min(A)  implies  T(x,A union {a}) <= T(x,A).              (7)

Earlier insertion of the same entry cannot delay its recording. Repeated
copies do not reenter the unique-entry inclusion queue. The condition concerns
the same immutable protocol entry: changing its payload, invalidating an
earlier signature, replacing a nonce with another action or lowering a fee
is not the comparison in (7).
For an initially unsubmitted entry, A empty means no completion and the
fallback payoff; adding an admissible attempt is weakly better under the
same floor and continuation assumptions. No minimum of an empty set is used.

Let d be a fixed deadline and S_A=1[T(x,A)<=d]. Then (7) gives S_A<=S_(A union
{a}) pointwise. If successful execution has the same counterfactual source
payoff u(X,a_source) in the two runs, and failure pays F(X)<=u(X,a_source),

    [S_early-S_late] [u(X,a_source)-F(X)] >= 0.                 (8)

Earlier insertion weakly improves payoff even when service success is
correlated with X. This is stronger than comparing mean success probabilities:
the pointwise domination removes the independence requirement for this fixed
semantic-action comparison.

To compare adaptive retry policies, start early and then execute the same
later retry policy in a shadow record that ignores the additional early copy.
The shadow must be causally computable from the sender's actual information.
It cannot consult a hidden service outcome from the counterfactual run.
If the service and observations admit this coupling, the early policy weakly
dominates the delayed one by (8). This is an explicit policy-simulation premise,
not an instruction to forget the actual earlier send.

The condition on other traffic is also substantive. With arbitrary reactive
opponents, an earlier public or private receipt can change their submissions.
For the preservation proof, either their prescribed continuation ignores the
extra timing information in the required causal sense, or the coupled service
theorem must include those reactions. Holding an arbitrary opponent's entire
future action word fixed does not prove a behavioral-policy comparison.

If a proper first admission after readiness is guaranteed within Delta and
the next local opportunity occurs within Gamma, an owned deadline exceeding
Gamma+Delta with the appropriate endpoint convention makes initial prompt
completion certain. Combined with the continuation coupling and floor,
this supplies q^*=1 at fresh stages. No complete queue flush is needed.
At late off-path information sets, however, the remaining deadline can be
shorter and an optimal timing policy still requires the actual service law.

### Bounded inclusion does not imply insertion monotonicity

Let the deadline be 10 and the inclusion bound Delta=3. A service can record
a transaction first offered at time 8 at time 11, but record the same
transaction first offered at time 9 at time 9. Both satisfy the delay bound.
Sending at 8 fails while waiting until 9 succeeds. The service violates (7),
so bounded inclusion alone cannot prove prompt dominance. This is the exact
timing counterexample also analyzed in the reference-information note.

Persistent admission of one canonical transaction and idempotent retries are
credible ingredients for proving (7), but are not its proof. Queue priority,
replacement, state-dependent validity, nonce dependencies, fees and reactions
to earlier disclosure can matter. A concrete service must establish the
pathwise or controlled-kernel relation it uses. The relation need not be a
calendar and need not imply that all pending entries are processed together.

## What the module establishes

Actual-information optimal timing preserves source action comparisons when
the success process is source/action independent, successful continuation is
the source continuation, and failure has the acting player's genuine floor.
The dynamic version requires these properties at every relevant continuation
information set and yields the uniform bound (5) for one common fully mixed
sequence. Certain attainable success at fresh stages is needed for exact
initialized outcome preservation.

Success-or-exit proves that active owners' resolved values are public, but
does not identify survivors' posteriors about failed owners or replace their
handler payoffs by the failed owner's floor. Insertion monotonicity can justify
prompt sending without scalar independence for a fixed coupled continuation;
it must include legal shadow policies and the required opponent response law.

These are usable sufficient modules and explicit counterexamples to shortcuts.
They do not yet supply a preservation theorem for general asynchronous
concurrent rollback with arbitrary private reception, replacements and
survivor continuations.
