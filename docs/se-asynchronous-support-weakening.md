# Removing delayed-delivery support through a regenerative service

The [broadcast capstone](se-asynchronous-preservation-theorem.md) uses a
positive-probability delayed-delivery repair to make foreign failure rare at
every pre-exit information set. That argument is unnecessary for the more
structured service and reset described here. Foreign failure may be known with
certainty. Its continuation is compared directly.

Per-body noninterference alone does not supply this replacement. Two additional
properties do the work: future service for a not-yet-broadcast body is fresh
relative to the information available before its first broadcast, and the
post-failure game has a genuine reset which makes discarded operational memory
irrelevant to its legal continuation. Neither property gives the players a
public sending schedule or complete pending observation.

Everything below is finite mathematics. No Lean theorem is asserted for the
new service or reset adapter.

## 1. Where the unrestricted argument fails

Independence of source randomness X and operational randomness Z does not imply
that Z is irrelevant to a continuation game. Z can predict future inclusion,
other players' future information, or which authenticated messages remain
available. An equilibrium of a game which forgets Z need not be sequentially
rational in the actual game.

Here is a deadline-respecting example with no interference between bodies.
There is one relevant sender, one body, deadline 10, and a fair service bit z.
Before the decision the sender learns z through an earlier operational signal.
An admission at time 8 or 9 is recorded according to this table:

| Service bit | Send at 8 | Send at 9 |
| --- | --- | --- |
| 0 | Record at 9 | Record at 12 |
| 1 | Record at 11 | Record at 10 |

Every recording occurs strictly after admission and within three time units.
Utility is one for recording by 10 and zero otherwise. The source state can be
a singleton. A handler which forgets z uses a probability p of SEND at 8 and,
after WAIT, a probability q of SEND at 9. Its actual pure-action regrets include

    1-p       at (z=0,time=8),
    1-q       at (z=1,time=9),
    p*q       at (z=1,time=8).

The last quantity compares WAIT with the prescribed mixed action, keeping the
future probability q fixed. Their maximum is at least
(3-sqrt(5))/2. Indeed, if all three are at most d, then p,q>=1-d, so
d>=p*q>=(1-d)^2. Equality is attained at
p=q=(sqrt(5)-1)/2. Thus no sequence of such timing-blind policies has uniformly
vanishing regret. Earlier protected opportunities can be added, with guaranteed
timely recording; the example then occurs after the sender's own earlier
off-path waits. It is still a sequential-rationality obstruction to the
coarsening argument.

This example refutes the implication from noninterference to irrelevant
operational memory. It does not refute existence of a source-preserving SE:
the actual sender can use z. It is excluded by the conditional freshness
assumption in section 3, since the old signal predicts a not-yet-admitted
body's service.

There is also a separate multiplication issue. Writing a payoff as

    F + Pr(own completion) * (W-F)

is useful only if W is invariant across the compared timing policies. Suppose
F=0, a fair operational state c gives continuation value W(0)=1 and W(1)=3,
and two policies complete respectively only when c=0 and only when c=1.
Both have completion probability 1/2, but their expected payoffs are 1/2 and
3/2. Independence from a singleton source X says nothing about this covariance.
The positive theorem below proves completion optimality **conditional on every
foreign continuation scenario**, rather than assuming the multiplication.

Finally, an erased private commitment value is not automatically a disposable
random coin. If it determines an authentic retired opening which the actual
player can send and the coarse player cannot, the two action menus differ.
Dropping that value then removes a legal signaling action. The reset lemma
requires an action correspondence, not merely equality of current payoffs.

## 2. A precise reset lemma

Consider a finite continuation game H with hidden entry state x and each
player's retained entry information J_i(x). Its public entry state is s.
The actual continuation additionally remembers an operational record z_i and
a discarded own vector a_i. Assume the entry distribution has the form

    mu_s(x) * k_s(z) * product_i b_i(a_i | J_i(x)).             (1)

The b_i are normalized finite kernels; they need not be the same for different
private types. The operational records z may be arbitrarily correlated across
players. What is required is their independence from x conditional on s.
Each player's J_i remains in its later perfect recall.
The records in the actual information set are their observed projections only.
If an unsent vector is presampled to write (1), the player is not given that
vector; its unobserved coordinate is summed out. Likewise sampling a complete
operational probability space does not give a player an unobserved flight seed.

For later reveal failures a public receipt mask and its actually published
values can be included in s. If the mask is a function of operational data and
the values are the corresponding source coordinates, conditioning on the mask
and those values restricts the two factors separately. This yields (1) with
the appropriate updated source law. The mask is not silently omitted.

Require all of the following structural conditions.

1. Each actual continuation action has a legal coarse action, and each coarse
   action has a legal actual representative at every corresponding actual
   information set. Literal menus may use a controlled alias quotient, but
   old memory must not supply an extra effective action or certificate.
2. For matched actions, transition, observation and payoff kernels of the
   retained continuation depend on the coarse history only. Fresh service
   randomness is independent of the discarded entry record. Auxiliary noise
   observations can be kept, provided they have a causal simulation from the
   coarse own history and the player's retained auxiliary record.
3. A public failure boundary and the recording barrier precede this reset.
   No remaining old flight can expose a previously nonpublic source value or
   alter a new entry's service. Old timestamp/order information can remain
   visible, but the coarse controller and future service do not use it.

**Reset lemma.** Under these conditions, every fully mixed coarse behavioral
profile can be lifted to a profile which ignores the extra records at the
effective-action level. Its actual posterior and local effective-action gains
at a corresponding information set equal the coarse posterior and gains.
Consequently a coarse common fully mixed SE witness lifts to an actual witness.
The same conclusion holds for a family of coarse profiles with uniformly
vanishing local regret.

**Proof.** Fix an actual information set of i and its coarse own history.
In the path probability, other players' discarded-vector kernels sum to one,
because their prescribed effective continuation laws ignore those vectors.
The focal b_i(a_i|J_i) is constant across all hidden histories in that coarse
information set: J_i is remembered. The probability of the focal operational
record, after integrating foreign auxiliary records, is also a function of
the coarse own history and the observed auxiliary record, rather than of its
remaining hidden source state. This is exactly the conditional causal-channel
property in the
[transfer theorem](se-publication-transfer-mathematics.md).
Therefore the augmented path weight is the coarse path weight times a
nonnegative own-information factor. At a positive-mass information set that
factor cancels in Bayes' formula. At a zero-mass term it contributes nothing.

For a forced current action, condition 1 supplies the same coarse alternative;
condition 2 and induction on the remaining finite horizon identify the
continuation payoff kernels. Thus their local gains agree. Use positive alias
probabilities if literal actions have aliases. Apply the construction at every
index of the same coarse sequence and take a single subsequential limit of
profiles and beliefs. This proves consistency and sequential rationality;
mere agreement of limiting strategies would not prove consistency. ∎

For failed commitment blocks, equation (1) is obtained by mandatory rollback:
the current vectors have never been revealed, foreign current commitments were
opaque, and each owner selected its vector from its own phase-entry information.
The live source state returns to that prefix. The discarded a_i is then private
randomness conditional on remembered J_i, **provided condition 1 holds**.

One possible intermediate handler excludes all positively auditable messages,
including retired/unauthorized openings. It still allows current, structurally
authorized raw choices, including unusable values and guard-invalid values.
Thus its existence does not require a guard-admitted choice at every failure
state. With fresh canonical attempt handles, an old private catalogue supplies
no extra legal current action. Current failed guards and unresolved obligations
retain their ordinary exclusion rules. A precise backend must establish this
menu/transition quotient; the word “rollback” alone does not establish it.
Also exclude a first disclosure of a never-broadcast, genuinely authorized old
body. For a closed owned slot, such a first body can belong only to an already
excluded owner: an active owner's completed slot already has its accepted body.
This extra case is restored by the excluded-owner payoff comparison, not by
calling a historically valid body an audit offense.

This intermediate handler can have no audit charge on any retained path.
Every active base payoff is at least F_i, and exclusion fixes F_i. Therefore
its terminal payoffs are pointwise at least F_i. A finite constrained
information-agent equilibrium provides uniformly vanishing coarse local regret;
the reset lemma supplies the same bound in the actual retained handler.

### A concrete reset producer

The following compiler choices produce the required quotient for this
intermediate handler.

* Fix the settlement boundary and finish the old-entry recording interval before
  installing the next attempt. Every previously broadcast proper opening and
  its complete body are actually public. The coarse state keeps this archive,
  the failed-owner set, the saved source prefix, and each owner's still-live
  private inputs and bindings. Missing unbroadcast values are not made public.
* Roll back the entire failed current commitment block before issuing any
  resolve authorization for it. A later opening of one of these discarded
  candidates therefore has no genuine resolve authorization and is outside the
  intermediate menu. Earlier saved obligations and their private values are
  retained in the coarse state; they are not treated as discarded noise.
* Allocate a fresh canonical namespace for each physical attempt and slot.
  Neither the next namespace nor its legal current menu depends on a player's
  number of old private preparations or a carrier account nonce. Unused old
  candidates cannot be rebound in a new slot. Current/new raw values may still
  be unusable or fail a guard: their possible choices are the full fixed typed
  domain, so no post-failure intended-value selector is needed.
  Authorization names the logical attempt/event/accepted handle and the fixed
  settlement boundary, rather than an earlier packet's arrival rank. If actual
  proof bytes contain arrival metadata, they are transported as legal certificate
  aliases; the coarse handler sees their logical target, not a new strategic
  timing field. This is necessary for the handler value to be invariant when
  the focal packet's inclusion time changes but its successful logical result
  does not.
* Keep exact replay of an old public body available. Its body and certificates
  are in the common public archive. Copies do not create new application jobs.
  A still-live saved obligation receives a current resolve authorization and
  current-namespace body when its resolve phase is installed; the coarse game
  retains its owner's private bound value. A first genuinely authorized body
  for a closed old slot is excluded from this intermediate menu as above.
* Start the new attempt's service from its public reset state and fresh coins.
  The completed old jobs, old arrival order and old copies cannot change new
  job kernels, current menus, sample laws or base utilities. Keep all new
  operational observations in the coarse continuation: only the redundant
  entry record is dropped. New-body receipt and inclusion kernels are independent
  of old traffic even when an actor changes its replay policy.
* Filter every occurrence from a pre-reset namespace in the coarse handler,
  including a new broadcast of a public old body. At a handler site the actual
  retained action is the product of a coarse current action and a finite vector
  of old-public-body replay multiplicities. There is no smaller shared batch cap
  coupling these coordinates. Lift a coarse policy with a fixed positive
  source-independent law on the replay vector, independent of the chosen coarse
  action. All other lifted policies filter those old occurrences as well.

The last rule is necessary. Allowing old bodies to be a new strategic signaling
channel while forgetting old in-flight copies would be unsound: remembered
duplicate history could predict which apparent signals are fresh. Under the
stated filter, changing old replay coordinates changes no coarse state, no new
receipt kernel and no opponent's prescribed effective action. Their gain is
zero. Their actual observations are retained as causal auxiliary noise; they
are not asserted to be literally identical in a coupling. This product lift
has positive probability for every legal old replay vector and thus supplies
the required all-index full mixing.

For matching future actions, induction now gives the same new semantic and
operational state and the same distribution of all new observations. Retained
old signed bodies have the same replay options; discarded current candidates
have no legal opening option. Thus their different private heaps do not produce
different effective menus. Fresh service supplies condition 2. The recording
barrier and old-job isolation supply condition 3. Public old timestamps may
still be remembered, but the new controller and kernel do not consult them.

At a failed commitment reset, current source vectors were selected from their
own source information and never revealed. At a reveal reset, the archive
retains every value actually broadcast before closure. Hence the only additional
old source-valued observations are already in the coarse archive, and the
remaining entry record has the factorization (1). This proves the relevant
reset adapter for the specified controller; a backend which reuses private
allocation counters, lets an old packet affect a fresh queue, or permits a
retired candidate's authentic disclosure does not satisfy this producer.

## 3. Fresh service and a common timing optimizer

Fix a current public window and physical body class e. Settlement is at D;
there is a finite set T of possible first-broadcast times before D. At a site
where this body has not yet been broadcast, impose the following conditional
freshness contract:

* If first broadcast occurs at a in T, its eventual success-by-D probability
  is p_e(a), depending only on the public window, body class and a.
* Its fresh service randomness is independent of all source data, all past
  observations, and the other bodies' complete service processes. In particular,
  no earlier receipt can predict the not-yet-broadcast body's random coins.
* Its service cannot subsequently be cancelled, accelerated or delayed by any
  actor's other transmissions. Exact repeats do not create another service job.
* A body not yet authored cannot be first-broadcast by another player. Once
  its author sends it, another player can forward it, but this does not alter
  the original service job.

These assumptions are stronger than “the focal traffic does not change other
bodies' inclusion laws.” They say precisely what information can be relevant
before the focal body exists. They allow deterministic service, zero-probability
delivery patterns, and nonmonotone p_e(a). A bound a+Delta gives p_e(a)=1 at
protected times a<=A=D-Delta.

At an unsent site at time t define

    q*_e(t) = max {p_e(a) : a in T, a>=t},                    (2)

including never-send with success probability zero when necessary. Choose the
earliest maximizing a. The policy waits until that time and broadcasts then;
after an off-path additional wait it recomputes the same maximum over remaining
times. This is dynamically consistent: until the selected maximum is passed,
it remains a maximum of the remaining set. It is a policy of the public clock
and owned-body status, not of another player's messages or hidden type.

Let C retain the foreign **first** admissions, their semantic values and
distinct-body inclusion/failure data, the resulting distinct-body public
archive, and the source and coarse post-reset random coins sampled on an
equivalent probability space. Under foreign clock-only first-admission policies
and per-body noninterference, the focal timing policy does not change C.
It can change foreign receipt histories, known-body replay menus and replay
choices. Those are not asserted equal: duplicate noninterference and the reset
quotient remove their continuation effects. Fix an actual current information
set I.

For any allowed alternative first-broadcast policy tau, even one adapting to
later foreign receipts, conditional freshness gives

    Pr(own success | I,C, tau)
      = E[p_e(tau) | I,C, tau] <= q*_e(t).                    (3)

For the deterministic maximizing policy, equality holds for every C of
positive conditional mass. The future foreign receipts may correlate tau
with C; inequality (3) still holds pointwise because every p_e(a)<=q*_e(t).
No observation is allowed to reveal this body's fresh coins before tau.
After admission, its success event is fixed by that independent job and
further rebroadcast choices cannot improve it.

Thus one common timing policy maximizes completion conditional on every foreign
scenario. There is no need to solve separate optimizations using incompatible
beliefs, or to infer that all policies with the same marginal q have equal
payoffs. At protected sites the maximum is one, and the earliest maximizer
sends immediately. Everyone may use this rule concurrently.

## 4. Direct comparison when foreign failure is not rare

Use fixed public settlement times and the recording barrier. On any commitment
failure roll back the whole current commitment block. At a failed-window reset,
use the timing-blind handler supplied by section 2. Its coarse state retains
the actual failed-owner set, surviving saved obligations, and all source values
which really became public. It does not invent missing publications.

First fix a pre-exit opening site. There is no remaining semantic choice.
For each foreign scenario C, let W_i(C) be the retained continuation payoff
if i completes, using a common source continuation on success of the window
and the coarse handler on foreign failure. Since the handler is audit clean
and all base/source payoffs are at least F_i,

    W_i(C) >= F_i                                             (4)

pointwise, after sampling future source and handler coins. If i fails, its
permanent payoff is F_i. Reset equivalence makes W_i(C) independent of i's
emission time on the branch where i succeeds. It includes the same source
payload, while differences in old arrival times have been discarded only in
the continuation policy/kernel quotient, not in anyone's actual memory.

The expected payoff of a timing policy is therefore

    F_i + E[Pr(own success | I,C,tau) * (W_i(C)-F_i) | I].      (5)

Equations (3) and (4) prove that the common timing optimizer is optimal. This
argument permits arbitrary correlation of foreign failure and continuation
utility. It does not replace a survivor's handler utility by F_i.

At a binding site, let J be the actual corresponding source information and
let v_i(J,a) be the source continuation payoff for current legal vector a.
Current bindings are opaque, earlier openings are publicly recorded, and the
operational prescriptions are source independent. Hence the source posterior
is the prescribed source posterior at J, even on an operational history where
foreign failure is certain.

For foreign scenarios in which every foreign owner completes, own completion
continues the intended game with a. For the other scenarios, mandatory rollback
and the reset quotient erase a from the effective continuation. Accordingly,
for the maximizing timing policy the value of a has the form

    q*_e(t) * Pr(foreign clean | I) * v_i(J,a) + b_i(I),        (6)

where b_i(I) is independent of a. The clean coefficient is independent of the
remaining hidden source state at J. This uses the source/operational product
law, not merely the absence of a causal effect of a on a particular packet.
Thus a source-optimal a remains optimal. More generally a source regret R_n
contributes at most R_n to (6).

At an already-admitted site no semantic choice remains. Exact repeats leave
all service jobs unchanged; foreign clock-only policies and the reset handler
ignore any newly created operational signal. Such choices have zero gain in
the exact retained reference process.

For a fully mixed construction, perturb every protected/late maximizing action
by total mass epsilon_n, keep positive source probabilities from one source
witness, and choose a coarse handler profile with local regret delta_n.
At any current information set, the probability of a future operational
perturbation is at most H*epsilon_n, uniformly after arbitrary actual past
waits. Couple only the future from that site; there is no division by its
reach probability. If B bounds payoff differences, the comparison errors are
at most 2*B*H*epsilon_n. The handler's actual regret is delta_n by the reset
lemma. Thus a uniform retained-game bound is

    max(R_n + 2*B*H*epsilon_n, delta_n),                       (7)

up to an additional vanishing alias-floor error if the chosen literal action
representation needs one. There is no foreign-past-failure error term.
Take a common subsequence of these fully mixed assessments. The limiting
profile is an SE of the retained game. Protected sends occur on the initialized
limiting path, so no window fails and the selected initialized source law is
preserved.

The coarse handler is solved jointly at each finite index using the actual
entry distribution of that index. Equation (1) and the reset lemma then lift
its conditional comparisons. It is not a family of independently selected
posteriors unrelated to the common source witness.

## 5. What the raw extension must additionally establish

The intermediate handler above is structurally audit clean. Removing its
restriction requires the same causal suppression, positive-witness and
saved-debt comparisons as the
[authenticated extension](se-asynchronous-authenticated-construction.md).
No new full-support observation hypothesis is used by that comparison:
unexposed forbidden bodies must have no effect, while exposed forbidden bodies
must supply collectible evidence. The two requirements are different from
normal-explanation support.

A first historically authorized old disclosure by an already excluded owner
uses a different comparison. Its raw net payoff is at most F_i, while its
retained quiet continuation pays F_i. The direct continuation-extension premise
therefore restores this action without an audit witness. A foreign actor cannot
already possess such a never-broadcast authentic body at a retained reset;
once the excluded owner first discloses it, later forwarding lies in the newly
admitted continuation, whose equilibrium is supplied by the extension theorem.

Restricting only retired disclosures while retaining other audit-bad actions
would be insufficient for a single Boolean audit charge. At a retained history
where that charge is already sunk, another disclosure need not create an
incremental penalty. The clean intermediate restriction avoids that issue.
Alternatively a backend must supply a separate residual reserve or a direct
continuation comparison at those histories.

The existing direct API is
`GameTheory.Protocol.InformationModel.ActionRestriction.sequentialEquilibrium_extends_of_continuation_unclocked`
in [PassageRestrictionExtension](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean).
Its comparison asks for one legal retained policy under every extending profile
and every retained-site belief. A physical reset/menu quotient and a causal
audit comparator are therefore required; payoff identities alone do not
instantiate the API.

This gives a genuine alternative to the support-based proper-core proof when
the stated fresh-service and reset adapters hold. It does not justify the
unrestricted claim for every content-blind, deadline-respecting kernel. In
particular, a service with informative old mechanical state, old-flight queue
effects, unverifiable retired capabilities, or sender-dependent future handler
menus requires a different adapter or a different proof.
