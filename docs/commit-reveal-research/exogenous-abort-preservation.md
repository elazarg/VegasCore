# Exogenous abort and delivery-conditioned SE preservation

Analysis by Codex. A blockchain-like service can fail before the source game
finishes. Finite-horizon reliability can bound that event without making it
impossible. This note studies a weaker preservation target that records the
failure honestly: exact sequential rationality, with the source law recovered
conditional on delivery. It is not exact unconditional preservation of source
terminal histories, a change to VegasCore's semantics, or a theorem about the
full native raw action space.

The useful contrast is that a small probability of a genuinely exogenous
outage need not cause even a small rationality error. Under the explicit
failure-payoff convention below, every copied comparison is multiplied by
the same nonnegative survival probability and receives the same additive
offset. Outcome failure and incentive error are different quantities.

## Source and proposed service interface

**Source game.** Fix a finite extensive-form game with perfect recall and a
fixed public horizon of H stages. The public stage specifies its owner, or
that it is a logical chance stage. All terminals occur after these H stages.
Legal action menus, logical transitions, original observations and terminal
utility numbers are those of the source. Source chance edges have positive
probability in the legal tree; impossible edges are removed. Private initial
types and retained secrets can be arbitrarily correlated across players.
Binding values, lawful withholding and subsequent source failure choices are
allowed if present in this source game. A source failure outcome is distinct
from the physical abort introduced below.

Fixed horizon means that a logical action or type does not change the number
or identity of the remaining service stages. A program with earlier logical
terminals can be padded to H, but whether physical abort after such an earlier
result should erase its utility must be specified as part of that interface.
Padding is not a justification for changing settlement silently.

**Service process.** Between source stages, before them, or after them, insert
a fixed finite sequence of service checkpoints and finite forced processing.
The checkpoint index and its logical position are public. The service has a
finite state, possibly including a persistent hidden type. Its initial state
is independent of the source initial types. Every transition is a kernel of
its preceding service state and the public checkpoint/stage index only. It
does not read source actions, binding meanings, logical public chance
realizations, original observations or source utilities. It does not receive
feedback from a source policy or from the size/content of its chosen packet.

A checkpoint can continue or abort. Abort is absorbing: there is no later
strategic choice. Service states and checkpoints can be correlated over time.
No independence between successive outage events is assumed. On continuing,
the next source transition has its original law conditional on every complete
physical past. In particular, service records cannot predict a future logical
chance draw. Source draws are neither conditioned retrospectively on delivery
nor redrawn until a favorable one is obtained.

**Choices and observations.** Each genuine target decision offers precisely
the original source menu. There are no extra strategic timing, retry,
replacement, bidding, preparation or broadcasting choices. Forced physical
response sites have one silence action. At a genuine decision, the complete
remembered target input is its original source information I together with
a service record z. Observation randomness is implemented by finite joint
random seeds drawn from service-state/stage kernels independent of the source.
Shared seeds can correlate different recipients' samples. The complete record
z is a deterministic function of that actual seed/state prefix, the public
stage and original I; the same function applies to every hidden source history
in I. Any other packet field remembered there is already fixed by I. Source
and own-action recall are retained. Service evolution does not read a
source-dependent decoding of a private observation.

Public service records suffice. The theorem also allows correlated private
service samples, even samples predictive of future outage, if their complete
remembered channel is source-independent in this sense. The service does
not learn a source secret from those samples or change its law in response
to players' source choices. Additional information about source secrets is
not justified by calling it a receipt.

This is a whole-observation condition, separate from exogeneity of outage
probabilities. A pending opaque commitment can satisfy it. A plaintext opening
can be readable during forced waits if its value is already source-public
at the next genuine decision, or the wait ends in absorbing abort. No theorem
requires pending packets to be physically invisible. An implementation still
has to establish this frontier and its metadata behavior, as in the
[native serial observation analysis](native-observation-criterion.md).

**Utility on completion and abort.** When all checkpoints continue, target
terminal utility is exactly u_i of its erased source terminal history. On
abort at checkpoint k with service record r, utility is a_i(k,r), a fixed
number independent of source types, preceding source choices, source chance
outcomes, unfinished source results and continuation policies. These are
utility numbers, not merely equal cash refunds before applying a nonlinear
wealth utility. They can differ between players and checkpoint records.
Here r is the raw source-independent service/seed record, not a receipt
decoded using a source-dependent I. Finite service states ensure bounded
abort utilities.

Actual abort settlement must realize that convention. Saying that escrow is
refunded does not prove that a permanent chain halt permits its refund, that
lost fees were equal across choices, or that capital/time costs vanish. Such
effects can violate the assumption. There are no action-dependent fees,
forfeits, financing costs, delay preferences, wealth-dependent menus, producer
incentives, participation choices, coalitions or outside trades in this
interface. Ideal hiding/authenticity, available resources and finite physical
completion are primitive assumptions, not conclusions of an SE theorem.

## A preservation target that includes physical failure

Let Q_sigma be the source's joint law of its initialized private parameters
and complete logical terminal history under the selected SE. The target has
a distinct physical-abort terminal branch. Let Complete mean that it survives
all service checkpoints, and put p=Pr(Complete).

**Paper theorem.** For every selected source SE (sigma,mu) and every service
in the stated class, copying sigma at every genuine source decision yields a
target SE with globally consistent beliefs that project to mu. If p>0, its
joint law conditional on Complete is exactly Q_sigma. The unconditional
target readout is

\[
pQ_\sigma+(1-p)A_\sigma,                         \tag{1}
\]

where A_sigma is the actual abort-branch law, including the initialized
parameters if the readout retains them. The source private parameters are
not resampled or replaced to obtain this equality. Source utility is retained
exactly on completion. Expected utility has the form

\[
\mathbb E U_i^{\rm target}
 =p\,\mathbb E_\sigma u_i+c_i,
\qquad
c_i=\mathbb E\bigl[1_{\rm Abort}a_i(k,r)\bigr],  \tag{2}
\]

where p and c_i depend only on the service and its fixed stage layout.

This target is **exact sequential rationality with delivery-conditioned
source law**. It is forward implementation. It is not exact unconditional
logical-law preservation, approximate SE, equality of realized utility laws
on abort, or reflection of all target equilibria. If p=0, the copied assessment
can still be a target SE, but the conditional-delivery law is undefined.
Conditional positivity at every decision is unnecessary for forward
preservation; it makes the corresponding payoff comparisons positively
scaled rather than potentially tied.

The source and service interface are fixed before the selected source SE.
One copied behavioral policy works across the entire declared service class.
Full beliefs depend on the service law; the later section distinguishes this
pointwise claim from a Bayesian unknown-service model. No compiler parameters
are selected after observing the chosen equilibrium.

The proof is finite-game mathematics. No full native implementation adapter
or machine-checked theorem is claimed here.

## Primitive prefix factorization and global consistency

Take the source SE's one fully mixed consistency sequence sigma_n, with
Bayesian source beliefs mu_n converging to mu. Copy sigma_n at every target
source menu and use silence at all singleton physical sites. This is a fully
mixed target profile: every available player action has positive probability.

Let h be a source history at a genuine decision at stage s. Let omega contain
the complete preceding service state history and the jointly source-independent
random seeds used for observations, including hidden service type. It does
not store decoded receipts as independent factors: those can depend on the
recipient's original I. The pair (h,omega) determines those actual receipts
and the target history. Replay only the actual service/seed kernels up to this
stage, retaining paths that have not aborted.
Its law Q_s(omega) is a subprobability law, independent of h. It does not fix
future service events or condition a draw on future success.

Induction on the finite execution gives

\[
w'_n(h,\omega)=w_n(h)Q_s(\omega).                \tag{3}
\]

Source action and logical chance factors supply w_n(h). The original source
kernel remains unchanged given omega, and the copied source action component
ignores omega. Service factors supply Q_s. This is a product of actual
transition probabilities, not a marginal-independence assertion based only
on initialized honest play.

For a source information set I at s, write z=F_{s,I}(omega) for the complete
remembered service view, incorporating any observation randomness into omega.
Its dependence on I can record when this actor receives samples; it is the
same function for all h in I. Define

\[
q_I(z)=\sum_{\omega:F_{s,I}(\omega)=z}Q_s(\omega).
\]

At every legal target source decision J=(I,z), q_I(z)>0. Bayes' rule gives
the full target belief

\[
\Pr_n(h,\omega\mid I,z)
 =\mu_{n,i}(h\mid I)
   \frac{Q_s(\omega)1[F_{s,I}(\omega)=z]}{q_I(z)}. \tag{4}
\]

Thus the source projection is exactly mu_n, and the posterior service history
is independent of hidden source history given J. The second factor is fixed
across n, so these full beliefs converge at every genuine source site, even
when its source reach probability tends to zero. There is no division by a
limiting zero probability.

Other owned physical sites have singleton menus. Take one common compact
subsequence of their finite belief simplexes if needed. It preserves all
limits in (4) and supplies a single consistent target assessment at every
site. Singleton rationality is automatic. Full own-response and source recall
make the expanded finite game perfect recall.

The stronger product in (4) matters. Equal current observations alone would
not imply that a hidden service state remains independent of the source:
service learning and success selection can reveal a correlated source fact.
Here primitive independent initialization and source-independent service
kernels derive the product on every legal source history.

## Why every local rationality comparison is exact

Fix a genuine decision J=(I,z). Change its current source-action lottery to
delta and keep the copied source continuation thereafter. For a complete
source history h and service prefix omega compatible with J, define

- S_i(h;delta): source continuation utility from h using delta once and sigma
  thereafter;
- p(omega): probability that the remaining actual service process completes;
- c_i(omega): expected abort utility from that remaining process, with zero
  contribution on completion.

Service evolution and abort payoffs do not depend on delta or h. Under this
one-shot change, subsequent source actions ignore service records, and source
chance kernels are unchanged conditional on every physical history. Finite
transition multiplication consequently gives

\[
V_i^{\rm target}(h,\omega;\delta)
 =p(\omega)S_i(h;\delta)+c_i(\omega).           \tag{5}
\]

This is a derivation from the independent kernels. No future source coin is
sampled early, and no future physical result is made available to the player.
The identity follows by summing completed physical branches and aborted
branches of the actual continuation tree.

Average (5) using the product belief (4). Let p_J and c_{i,J} be the posterior
averages of p(omega) and c_i(omega). Then

\[
V_i^{\rm target}(J;\delta)
 =p_J V_i^{\rm source}(I;\delta)+c_{i,J}.       \tag{6}
\]

These coefficients can depend on the actor's public or ancillary private
service record, but not on delta or the hidden source history. Always
0<=p_J<=1. The gain relative to the copied source lottery is therefore

\[
p_J\bigl[V_i^{\rm source}(I;\delta)
        -V_i^{\rm source}(I;\sigma(I))\bigr]\le0. \tag{7}
\]

Source sequential rationality supplies the inequality under mu. If p_J=0,
every action has the same continuation utility c_{i,J}; copying is still
rational. All genuine decisions satisfy (7), all singleton sites are
trivial, and the assessment is consistent. The finite perfect-recall
one-shot-deviation principle now gives sequential optimality against every
whole target continuation policy, including policies adapting to future
service observations. This proves exact target SE.

Equation (6) has only been proved for a present action lottery followed by
copied continuation. An arbitrary later adaptive policy can choose source
actions based on a service signal predictive of completion. Its eventual
source utility can then correlate with Complete. It need not have a universal
affine comparison against its unconditional erased source policy. The proof
uses local comparisons plus perfect recall, rather than making that false
claim about every adaptive policy.

### Harmless extension: abort utility from immutable initial parameters

Type-independent abort utility is sufficient, but need not be imposed for
this result. Permit a_i(x,k,r), where x is an immutable initial source
parameter, provided abort utility remains independent of every source choice
and subsequent source random draw. Keep the same independent service process
and observation rules. This is a separate stated utility variant, not a
license to make failure payoff depend on the last attempted value.

At a complete source history h, x is fixed. The remaining expected abort
contribution becomes c_i(h,omega), but it is still independent of the current
lottery delta and future policies. The posterior service history remains
independent of h. Averaging gives

\[
V_i^{\rm target}(J;\delta)
 =p_J V_i^{\rm source}(I;\delta)
  +\sum_{h\in I}\mu_i(h\mid I)
       \sum_\omega\rho_J(\omega)c_i(h,\omega).
\]

The final term is the same for all delta, so every comparison and the entire
consistency argument remain valid. Delivered-law and reliability conclusions
are unchanged. The global offset in (2) now depends on the fixed initial
source distribution as well as the service, but not on the selected source
profile.

For example, a refund's utility may depend on immutable private initial
wealth. This variant can account for it if no source-dependent fee, financing
or portfolio change alters the abort wealth. Equal cash refunds alone do not
establish those conditions. Independent mathematical review accepted this
extension. The counterexample for prior source choices below still applies:
their values are strategic, rather than immutable initial parameters.

## Exact delivered law and unconditional error

At a complete source terminal h, the same multiplication gives source weight
w_sigma(h) times the law Q_H^complete(omega) of a successful service path.
The latter does not depend on h, even on its public chance realizations.
Summing over omega yields

\[
\Pr(h,\mathrm{Complete})=p\,w_\sigma(h).
\]

This equality includes the initialized private parameters in h. Dividing by
p>0 proves the conditional law in the theorem; summing utilities proves (2).
Absorbing abort never generates the unfinished logical draws. Their source
terminal law appears only in the successful-branch calculation.

Compare source and target on the common space consisting of complete source
terminals and a distinct abort branch. The target is (1), so total variation
is exactly 1-p: their supports disagree precisely on the abort branch and
the source component loses the same total mass. For any declared coarser
readout, such as a fixed fallback value on abort, total variation is at most
1-p by pushforward contraction. Neither statement equates a partial source
execution with a completed game.

Let the service have m possible checkpoint positions. Suppose a public bound
q_k in [0,1] applies to conditional continuation at checkpoint k after every
compatible complete service past that has survived to k. Then

\[
p\ge\prod_{k=1}^m q_k,
\qquad
1-p\le1-\prod_{k=1}^m q_k
       \le\sum_{k=1}^m(1-q_k).                 \tag{8}
\]

Indeed, the next survival probability is the previous one times the expected
conditional continuation probability given survival; that expectation is at
least q_k. Induct through the fixed checkpoint list. The final inequality
follows by expanding or inducting on products in [0,1]. No independence
between checkpoints is needed. With q_k>=1-epsilon_k, the whole-game failure
bound is sum epsilon_k. A fixed logical horizon bounds m only if the service
also supplies a fixed finite processing/checkpoint bound per stage.

Bounds must hold for permitted load and all legal source choices. A bound
only for one intended fee or packet size does not establish exogeneity or
the required uniform conditional property. Initial good-average availability
does not supply every conditional q_k after learning a persistent service type.

## Complete boundaries for weakening the assumptions

These examples show failures of this particular target when a key primitive
changes. They do not assert that every compiler admitting that feature fails.

**Source-choice-dependent survival.** One player chooses A or B. Source
utilities are u(A)=1 and u(B)=3/4, so A is its unique source SE. The target
retains that menu and has abort utility zero. After A it completes with
probability 1/10; after B it completes surely. Target expected utilities are
1/10 and 3/4. B is uniquely rational. No target SE copies A or has the all-A
source law conditional on completion. Each completed branch still executes
the original action correctly; the outage law changes incentives.

**Hidden-source-dependent survival before a choice.** Nature draws a fair
hidden bit theta. Source choices are Safe, paying 3/5, and Bet, paying one
when theta=1 and zero otherwise. Safe is uniquely rational in the source.
Before the target choice, a checkpoint continues surely when theta=1 and
with probability 1/10 when theta=0; abort utility is zero. Conditional on
reaching the choice, the posterior is Pr(theta=1)=10/11. There is no further
abort, so Bet is uniquely rational there. No preserving target SE exists
for the selected source policy. Even with a singleton menu, the delivered
joint type law would already differ from the source prior. A hidden service
type correlated with theta can produce the same comparison without a service
directly reading a private bit; independent initialization rules out both.

**An outage law reading a later public source coin.** One player first chooses
A or B, then a fair public source bit theta is drawn. Payoffs are
u(A,0)=1, u(A,1)=1/5, u(B,0)=0 and u(B,1)=1. Source A has expected utility
3/5 and is uniquely optimal against B's 1/2. A later service checkpoint
continues with probability 1/5 at theta=0 and surely at theta=1; abort
utility is zero. Target A has expected utility 1/5 and B has 1/2, so B is
uniquely optimal. The checkpoint need not predict the bit before it is drawn.
Reading it afterward is enough to reweight source continuation payoffs and
tilt the delivered coin law. Source-public dependence can therefore matter
even when it leaks no additional secret.

**Source-dependent abort utility with independent outage.** One player chooses
A or B with source utilities one and zero. The target completes with
probability 1/2 independent of the choice. On abort, A pays zero and B pays
three. Expected target utilities are 1/2 and 3/2. B is uniquely rational,
so the source all-A SE is not implemented. Success reliability, unchanged
source menus and exact delivered execution do not cancel a failure payoff
that rewards a prior attempted action.

These are finite one-player perfect-recall games, so the claimed unique
optimal strategies are SE and PBE as well as Nash conclusions. Their strict
comparisons rule out a preserving equilibrium, rather than merely showing
one copied assessment is bad.

Premature source-secret observations form another independent boundary:
even perfectly exogenous survival cannot preserve a source guessing decision
when its answer is revealed before the choice. The complete separating
decision argument is in
[the information criterion](universal-preservation-criterion.md).
Outage exogeneity must be combined with the declared observation interface.

## Knowledge, concrete meaning and remaining adapters

For a fully specified service, the target SE above is a pointwise assessment.
Its copied behavioral source policy is the same for every service meeting
the assumptions. A player need not calculate its precise survival chance
to follow that policy: every admissible posterior gives a nonnegative common
multiplier and a source-independent offset. The theorem nevertheless supplies
different complete beliefs for different service laws.

An independent persistent hidden service type can be included in Nature with
a specified common prior. Every type must obey the same source-independent
kernel and observation rules. Updating that type from public or private
service signals changes p_J and c_{i,J}, but the product factorization and
local rationality proof remain valid in the resulting Bayesian game. Common
conditional reliability bounds survive posterior averaging. Correlation of
service type with source-private input, strategic service decisions, collusion,
or ambiguous priors without a specified belief model are outside this result.

As a blockchain interpretation, this is an abstract abortable execution layer
whose outages and recovery records are unrelated to the program's choices,
and whose failure settlement assigns the declared choice-independent utility.
It can describe application failure against independent background outages.
It does not claim that ordinary mempool inclusion is source-independent:
transaction fees, lengths, load, replacement, validity and producer selection
often depend on the chosen transaction. Noncollusion does not eliminate those
dependencies. Fixed program length helps aggregate genuine stage guarantees;
it does not create them.

For native serial commit-reveal execution, protected canonical binding and
opening operations can help prove the observation frontier. Their packets
remain real messages. The native model also has lawful failure utilities,
collateral settlement, accepted and dead late packets, candidate preparation
and repeated physical response choices. These are not automatically the
exogenous absorbing-abort layer analyzed here. A native application must
prove the stage/process factorization, full observation identity, actual
abort settlement convention and complete menu restriction. Existing checked
public-scheduling preservation does not supply this probabilistic-abort
adapter by simply adding a failure probability.

If exact unconditional readout is required, genuine physical abort is already
a mismatch even in this benign model. If delivery-conditioned correctness
and an explicit failure bound suffice, one can retain exact sequential
rationality under these stronger exogeneity and settlement assumptions.
Alternative realistic failure settlements require their own incentive
analysis; a small failure rate alone is not that analysis.

## Result card

- **Result and source:** Paper exact SE for copied policies of finite
  perfect-recall fixed-stage games, retaining correlated private types,
  binding choices and lawful withholding. Source terminal law is exact only
  conditional on physical completion.
- **Physical interface:** Finite source-independent service process with
  absorbing public abort, unchanged source menus/chance/observations,
  ancillary remembered service records and singleton physical waits. No
  strategic timing, retry, bidding or additional release channels.
- **Costs and quantifiers:** Interface and actual choice-independent abort
  utilities precede the selected source SE. Completion utility is the source
  utility. Fees, funding costs, producer incentives, participation, coalitions
  and outside markets are excluded; no refund feasibility claim is made.
  A separately proved variant allows abort utility to depend on immutable
  initial parameters, including initial private wealth.
- **Output and bounds:** Copied target strategy is an exact SE, not an
  approximate SE. Unconditional law is the explicit completion/abort mixture;
  its distinguishable-abort TV error is 1-p, bounded by the sum of conditional
  checkpoint failure bounds. No independence between checkpoints is needed.
- **Knowledge:** A common source-copy policy works across the service class;
  beliefs are service-specific. Independent hidden service with a common prior
  also fits. Source-correlated or strategic service does not.
- **Status:** An independent mathematical review accepted the complete
  consistency, local rationality, output-law, reliability and counterexample
  arguments. No Lean theorem or full native adapter is claimed.
