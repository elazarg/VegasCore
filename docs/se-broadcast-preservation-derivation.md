# End-to-end preservation with strategic evidence reporting

This is the assembly of the finite mathematical construction. Its evidence
comes from actual game players and the public ledger, not an honest audit
monitor. It first uses sufficient finite capacity for the declared raw game.
Capacity reductions are separate refinements which must preserve the same
publication and reporting properties.

The intended game, initial law and utilities remain those of the source
program. The implementation adds fixed windows, publication barriers,
failure/exclusion transitions, funded authenticated submissions and a terminal
reporting protocol. Players can wait, send late, send malformed or conflicting
bodies, replay messages, withhold reports and communicate after exclusion.
Their receipts are partially observed. Only actual ledger publication creates
the public archive.

This is a hand derivation for the explicitly defined runtime below. It is not
a checked Lean result or a theorem about every bounded-delay builder. In
particular, nonrevocable submission and independent body service are stated
runtime conditions, not consequences of the existence of a deadline.

## 1. One statement and one order of quantifiers

Fix a finite, well-formed linear source program, a finite-support initial law,
finite strategic value domains and its intended perfect-recall game S. Require
S to have finitely many histories; in particular, every reachable source sample
has finite support. Initial private inputs may be arbitrarily correlated. Fix the bounded implementation,
its public clock, finite raw packet domains, service and observation kernels,
funding and verifier before choosing a source equilibrium.

For each source player i, choose a permanent exclusion payoff F_i below every
active base payoff of the implementation, including its failure continuations.
Let U_i bound all its base payoffs from above. Fix refundable audit collateral

    D_i >= U_i - F_i.                                         (1)

The audit subtracts D_i once when a positive violation by i is proved. Penalties
are not redistributed to game players. Proper reporting has zero incremental
player cost. Publication/report fees have a separate fixed funding allowance;
they are not secretly deducted from the preserved game payoff.

**Preservation statement.** Every sequential equilibrium sigma of S has a
sequential equilibrium of the full finite implementation with the same joint
law of initial source data, typed terminal source results, projected source
public results and realized net game payoffs. On that implementing law no
player is excluded or charged. The statement is existential about the
implementing equilibrium; it does not require every implementation equilibrium
to reproduce sigma.

The service class is the fresh independent-body class of
[the timing proof](se-asynchronous-support-weakening.md), instantiated by
[the explicit runtime](se-broadcast-runtime-mathematics.md). Complete and partial
observation are both possible when their kernels satisfy the stated conditions.
Correlated builder outages and the current Lean reserved tape are not thereby
included. Finite domains are actual theorem hypotheses; unbounded bids and an
unbounded arbitrary-byte side channel are outside this statement.

## 2. Proof components and their dependencies

| Component | Mathematical result used | Concrete producer |
| --- | --- | --- |
| Source-to-block correspondence | Batching preserves the source consistency witness, continuation choices and initialized readout law. | Existing source observation/guard structure; componentwise openings retain original reveal order and samples. |
| Runtime and public barriers | Every qualifying body keeps its individual publication promise; every old proper opening is public before a new binding decision. | Body-keyed immutable validation and the specified independent bounded service. |
| Retained equilibrium | Source choices, optimal timing and actual-memory failure play have uniformly vanishing local regret on one fully mixed family. | Fresh-body optimization and the concrete reset/menu quotient. |
| Raw extension | One causal retained continuation dominates every new raw choice at every retained information set. | Semantic debt, own exclusion, or positive evidence at the first external effect. |
| Actual collection | The required witness is in the final public archive or nonauthors' remembered receipts. | Public-body recording or complete-envelope receipt; no passive ingress reporter. |
| Strategic reporting | Canonical reports are optimal at every actual report information set; the reduced equilibrium lifts on one common sequence. | Frozen snapshots, monotone authorwise verification, funded simultaneous report rounds and immutable delivery. |
| Selected joint law | No failure or charge occurs on the limiting retained path; all extensions preserve the pre-report law. | Protected submissions, source transition correspondence and exact report-kernel matching. |

The substantive constructions are the
[source adapter](se-asynchronous-pre-exit-construction.md#8-the-source-adapter-for-finite-linear-vegas-programs),
[fresh-service proof](se-asynchronous-support-weakening.md),
[raw-message comparison](se-asynchronous-authenticated-construction.md),
[runtime specification](se-broadcast-runtime-mathematics.md) and
[strategic reporting proof](se-strategic-reporting-mathematics.md).
This document fixes their composition and does not substitute a list of desired
properties for those derivations.

## 3. What is a submission, and what capacity supplies

There is one partially observed broadcast operation in the modeled network.
A qualifying authenticated envelope creates an immutable publication job for
its canonical body. Copies create receipt occurrences but not a second job.
Qualifying outer validation is separate from executing the inner game action:
recording must still work when that action is stale, conflicting or rejected.

Public validation prevents a later conflicting envelope, funding withdrawal,
shared sender nonce, validator change or replay from invalidating the body.
It remains eligible until it is recorded; consuming its replay protection
implies that the same body has been recorded. The runtime document states the
corresponding validation invariant and induction. Those eligibility rules are
publicly enforced in the chosen message-inbox model. They do not require an
auditor to decide which player behaved honestly. Retention of an unseen submitted
body and its eventual inclusion are separate obligations of the specified
network service; a contract does not prove them by maintaining eligibility.

Timely inclusion then supplies publication within Delta of qualifying
submission. The model does not infer that receipt by one peer alone is a valid
submission. A distinct operation which announces qualifying bytes without
creating their publication job, or a carrier which can cancel that job, changes
this model and needs a new proof. Ordinary account-nonce transactions are not
silently treated as nonrevocable body jobs.

For a finite set Q of qualifying bodies with per-body work w(b), one deliberately
large application allowance is

    C_app = sum_(b in Q) w(b).                                (2)

With enough per-block service capacity to process that total, every permitted
set of due jobs fits. Independent early-inclusion coins can still defer other
jobs, so the model does not require every pending body in every block. Repeated
occurrences must have their separate bounded intake cost accounted for; their
lack of a new ledger job is not a zero-cost network claim. The allowance covers
all declared raw choices, not just the selected equilibrium path.

For reporting, let H_R bound all tail opportunities and let g_R bound the work
of one entire permitted raw tail batch. A sufficient tail allowance is

    C_report = H_R * g_R,                                    (3)

in addition to any residual application work. Report entitlements activate
only at the reporting boundary and cannot be consumed by earlier traffic.
The final deadline leaves time to drain that bound and finalize the records.
These are finite sufficient bounds, not minimal ones.

The proof below uses the publication, noninterference and final-delivery
properties produced by (2)-(3), not their particular numerical formulas.
A smaller service can replace them after proving the same properties for
every raw continuation quantified by the theorem.

## 4. Construct the retained runtime equilibrium

Call R the intermediate game. Before public failure it permits source-admitted
semantic choices and the specified operational choices, including late sends
and exact replays. After failure it uses the structurally audit-clean handler
of the fresh-service proof. The removed raw actions are restored in section 6;
they are not forbidden in the final game.

Batch each player's component choices within a private-choice block using the
product of that player's original behavioral probabilities. Its observations
within the block contain its earlier own choices and no newly available foreign
semantic data. Keep separate component handles and release only components in
their original reveal block. Samples and public observations retain their order.
The vector deviation is a legal source continuation, so finite perfect recall
transports the source one-step bounds to the batched game. Let r_n tend to zero
bound the resulting source comparisons along one source consistency witness.

Every window has a fixed public readiness time, last protected submission time
A, and settlement D=A+Delta. The next binding window waits until D+Delta.
Any proper opening submitted by D is therefore publicly recorded first,
including one rejected as late by the game. Success or exclusion is determined
from the ledger at D before another strategic decision; no voluntary timeout
call is needed to make a known miss effective.

At an unsent body class e and time t, fresh service gives a success probability
p_e(a) for first submission at a. Its coins are independent of source data,
past observations and foreign body jobs. The policy selecting the earliest
maximizer of

    q*_e(t) = max_(a >= t) p_e(a)                             (4)

maximizes completion conditional on every relevant foreign completion scenario.
A later receipt-adaptive policy only averages p_e(a)'s, each bounded by (4).
At protected times the maximum is one.

On failure, roll back the entire current unsaved commitment block. Retain saved
obligations, source private inputs, exclusions and every value actually made
public. New attempts use fresh namespaces and service; old packets cannot change
their menus or processing. Selected handler policies filter old-namespace replay
noise, while actual players retain all observations. The explicit action-menu
correspondence and conditional own-information factor in the reset proof justify
this prescription. No player is instructed to forget a known secret.

For an opening, the timing comparison conditional on foreign scenario c is

    F_i + Pr(own success | I,c) * (W_i(c)-F_i),

where W_i(c)>=F_i and is invariant under successful focal timing. For a binding
vector a, its a-dependent value is

    q*_e(t) * Pr(foreign completion | I) * v_source(J,a).     (5)

The other term is independent of a because foreign failure rolls back the
current block. The coefficient in (5) is independent of hidden source state
at J. This is the all-index source/operational factorization, not an inference
from the limiting strategy alone.

Perturb operational prescriptions by total mass epsilon_n at each site and
solve the coarse handler agents jointly with local regret delta_n. If H bounds
remaining operational decisions and B bounds payoff differences, the actual
retained local gain is bounded by

    max(r_n + 2 B H epsilon_n, delta_n),                      (6)

plus any explicitly used vanishing representation-floor term. The bound is
conditional on the actual information set and concerns future perturbations;
there is no inverse probability of reaching that set. One common limit of
the fully mixed profiles and their actual Bayes beliefs is an SE of R.

## 5. The evidence available at a raw deviation

Use the total, monotone, authorwise positive verifier of the authenticated
construction. A malformed or invalidly authorized signed body gives a singleton
witness. Distinct bodies for one physical slot, or improper handle reuse, give
a pair witness. Exact repeats are not new offenses. Unrevealed semantic guard
failures are handled by debt, not an imaginary visible witness.

Let E be the first external effect of a suppressed forbidden body strictly
before base payoff freeze T0 and before the semantic-debt or own-exclusion
stopping boundary. The runtime transition rules
give exactly two relevant possibilities:

* A nonauthor game player receives the complete authenticated body.
* The complete body becomes a public ledger record before its application
  effect. If the inner call is rejected, the outer record still exists.

Here "before freeze" means before the freeze transition in the execution order.
It includes recording/application substeps at clock T0 which precede that
transition; an effect in the final processed block is not lost by comparing
only numerical timestamps.

Until one of these occurs, independent channel/service transitions leave all
other players' observations and public state coupled. A passive relay possessing
bytes is not a third evidence case. Its possession need not cause any game effect.

Any earlier body needed for a pair belongs to the retained prefix and keeps
its individual publication promise under all later raw actions. Consequently
the complete witness W satisfies

    W subseteq P_final union union_(j != i) K_j,             (7)

where P_final is the actual final public archive and K_j is the actual player's
remembered evidence snapshot. The report snapshot is after base play freezes,
so every payoff-relevant nonauthor receipt is included. A first receipt only
after the base outcome freezes cannot create a base-game gain.

The runtime and reporting proofs derive collection from (7). There is no
premise that an arbitrary audit party notices the offense, nor a positive
lower bound on the chance of E. Gain and collection are compared on the same
event.

## 6. Restore raw application behavior before strategic reporting

Define G^- as the full pre-report raw game followed by a specified canonical
report-all terminal kernel. This is a mathematical intermediate game, not an
assumption that strategic players obey. Its actual strategic reporting choices
are introduced in the next section.

At any retained information set, fix any extending pre-report opponent profile,
any belief over its retained histories, and any new raw choice by i. Construct
one legal retained continuation from i's own information and private randomness.
It carries a virtual raw private history, copies compatible proper packets,
and simulates suppressed packets' independent flight coins. Until a stopping
event, the other players' actual observations agree. The comparator is a single
causal policy on the information fiber, not a policy selected using a hidden
source state.

Semantic repair is needed before the first public exclusion, where the retained
source menu supplies an admitted choice. After that exclusion, R already permits
current structurally clean but unusable or guard-invalid values. Copy those
choices literally. No post-failure admitted-value selector is assumed. The
removed handler choices are structural audit offenses and the separately
handled first old disclosures of excluded owners.

There are three substantive stopping comparisons.

1. **Bad semantic debt is saved.** Repair the raw private candidates only in
   the shadow heap. Before save, current handles are opaque and rollback erases
   the unsaved block. If an earliest bad obligation is saved, later play must
   open/check it or exclude its owner. Guard checks occur when their last
   required input is published. Thus the raw owner's eventual base payoff is
   F_i. The clean retained continuation guarantees at least F_i.
2. **The owner exits.** Its base payoff is permanently F_i and later audit
   charges are nonnegative. This also handles its first historically authorized
   old disclosure; such a disclosure is not falsely called an audit offense.
3. **A forbidden body has effect E first.** Equation (7) supplies a positive
   witness. In G^- the specified terminal kernel collects D_i. The raw base
   gain is at most U_i-F_i, while a clean quiet comparator guarantees F_i.

If none occurs before the base freezes, the coupled base utilities agree and
later nonnegative raw charges cannot improve them. Therefore

    E[raw net payoff - retained comparator payoff]
      <= (U_i-F_i-D_i) Pr(E) <= 0.                           (8)

The construction and inequality hold over the entire information fiber and
for every profile quantified by the direct restriction-extension theorem.
Report withholding is not among those profile variables in G^-: reports are
still part of its terminal kernel. This avoids a circular collection claim.

Apply
`GameTheory.Protocol.InformationModel.ActionRestriction.sequentialEquilibrium_extends_of_continuation_unclocked`.
It supplies an SE of G^-, including rational play and consistent beliefs at the
new raw information sets, and preserves the retained initialized law. The exact
Lean interface and its current runtime scope are recorded in the
[mechanization inventory](se-asynchronous-mechanization-inventory.md).

## 7. Make every report strategic

Let TK be the public reporting snapshot. Each original player j, including an
excluded player, can submit its snapshot of foreign-authored application bodies.
Reporting opportunities occur in fixed simultaneous rounds. Other players'
messages cannot remove a round or consume j's reporting entitlement. Players
still receive later messages and may choose raw tail actions; the prescribed
report simply depends on the remembered snapshot.

The base payoff is fixed. The verifier only adds authenticated evidence and
cannot execute a reported application instruction. A canonical report by i
contains no i-authored evidence, including nested evidence. Other players'
prescribed future bundles depend on their own fixed snapshots, not i's report.
Already admitted reports and old evidence-contributing body jobs are immutable.
Thus changing i's reporting action cannot remove its existing/future canonical
liability. It can add self-evidence but cannot improve its payoff. Canonical
reporting is optimal at every tail information set under every belief, even
after earlier malformed or partial reports. Withholding can be equally good.

Take any fully mixed Bayesian witness sigma_n for the SE of G^-. In the full
game copy it exactly before TK. At each actual reporting information set use

    (1-rho_n) * canonical + rho_n * positive_raw_action_law,

where rho_n>0 tends to zero. These choices form one fully mixed profile on the
entire finite game. Pre-report reach weights and Bayes beliefs are unchanged
exactly. If B_R bounds net payoff spread, the conditional probability of any
future report perturbation is at most H_R rho_n, so local gains are at most

    r'_n + 2 B_R H_R rho_n       before reporting,
           2 B_R H_R rho_n       during reporting,            (9)

where r'_n tends to zero by the sequential rationality of the limiting G^-
assessment. One common subsequential limit is the required full-game SE.
No report perturbation scale is divided by a rare pre-report reach probability.
The [reporting derivation](se-strategic-reporting-mathematics.md) proves these
statements for the full tail menu, not only for honest report actions.

## 8. Initialized law and the capacity refinement boundary

In the retained limiting profile protected messages arrive by their deadlines.
No failure occurs. The source correspondence identifies the typed terminal
results and projected public source trace path by path under the coupled
source randomness. This retains the joint law with the initial private data.
All transmitted retained bodies are audit clean, so the realized net payoff
equals the source payoff. Raw extension preserves that initialized law, and
the reporting lift has exactly the canonical terminal kernel in its limit.
This proves the statement in section 1.

Capacity enters only through the concrete validity/publication and report
delivery lemmas. It can be reduced without changing (4)-(9) if a replacement
backend proves those same lemmas and preserves the intended clean-path service.
That includes preserving the report entitlement after arbitrary raw application
traffic and preserving all old evidence contributions against tail cancellation.

There is an exact reporting reduction already available. For each foreign
author, report a local singleton/pair witness if one exists; otherwise report
the at-most-one known body per authorized physical slot. The
[evidence-summary theorem](se-evidence-summary-mathematics.md) proves that the
union of these summaries and any final public archive has exactly the same
Boolean penalty vector as the full reports. It can replace the canonical report
kernel in the proof. It does not reduce application publication capacity or
create a missing witness.

The mathematical endpoint is this specified finite inbox/broadcast game and
its full strategic report protocol. Formalizing it requires the concrete
transition, information and compiler objects listed in the inventory. Applying
it to an EVM carrier or a different network requires a refinement proving the
stated service and message interfaces; neither a reliable audit monitor nor a
generic transaction deadline is silently substituted for that refinement.
