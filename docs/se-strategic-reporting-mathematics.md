# Strategic terminal reporting and a common equilibrium witness

This note gives the reporting component of the finite asynchronous preservation
construction. The reporters are the actual game players. There is no additional
honest monitor or evidence-retaining ingress whose reporting behavior is assumed.
The public ledger supplies its own publicly recorded bodies; all other evidence
must come from a player's actual observations and chosen report.

The order of construction is essential. First solve the raw application game
with a specified report-all terminal payoff kernel. Then append strategic
reporting and lift that equilibrium on one fully mixed sequence. Collection
against arbitrary withholding profiles of the full reporting game is neither
assumed nor needed.

## 1. Finite data and exact payoffs

Let P be the finite player set and let B be the finite set of complete signed
application bodies in the declared raw domain. Authentication partitions B into
sets B_i of bodies authored by i. An outer report's transport signature is not
another signed application instruction. Authentication and the application/report
domains distinguish the two.

At a fixed public time T0 the base game stops changing its result and utilities.
Write u_i for this frozen base utility. Every obligation needed to determine that
result has been resolved or assigned its specified default/exclusion consequence.
The cutoff means the freeze transition in the ordered runtime history. An
application or recording substep at the same block clock which occurs before
that transition is still before base freeze and belongs to the exposure test.
Later messages cannot reopen the base result, create a new phase authorization,
transfer a reporting reward, or make another player's audit forfeiture part of
u_i. Let L be the immutable public authorization/history data used by the verifier.

At a later fixed public snapshot boundary TK, player j records

    K_j = {complete application bodies known from its own history by TK}.

Perfect recall makes this snapshot available at every later information set.
It includes bodies actually received, not merely their payloads or signatures
held by an unmodeled relay. Let P_final be the application bodies publicly
recorded by final audit settlement, including any promised retained-prefix
counterparts which finish recording after TK.

For each i, the deterministic verifier is a monotone predicate

    Bad_i(E_i; L),       E_i subseteq B_i.                     (1)

Monotonicity means E_i subseteq E'_i implies
Bad_i(E_i;L) <= Bad_i(E'_i;L). Its witnesses are positive signed evidence and
fixed authorization records. A later report cannot retract evidence, repair
an intrinsically invalid old certificate, or turn absence of an unreported
message into a violation. The final utility is

    U_i = u_i - D_i * Bad_i(E_i;L),       D_i >= 0.             (2)

Canonical reporting has zero incremental player cost and gives no positive
player reward. Other raw tail actions may have nonnegative extra costs; if
allowed, those costs are bounded and included in the payoff range below. The
primary statement takes them to be zero. Funding paid by an external reserve
must not silently be an avoidable cost deducted from the reporting player's
game payoff: such a cost would change its reporting incentive.

The verifier's evidence for i contains only i-authored application bodies and
L. A canonical report by i contains no i-authored body, including nested data.
The existing typed, nonnested application-body idealization supplies this last
property. It is a substantive domain condition. If a foreign malformed body
can embed the reporter's own incriminating signature, reporting that body can
harm the reporter. Silently filtering it out would also lose the alleged
offender's witness. Arbitrary malformed **report wrappers** are allowed below;
they do not justify removing this application-domain condition.

## 2. Raw report menus and service

After TK there is a finite reporting interval ending at submission cutoff TS
and final settlement TA. Each original player, including an excluded player,
has at least one reporting opportunity before TS. This is an opportunity to
choose an action, not a requirement that it report. Opportunities need not be
exclusive sender turns; all players may act in the same modeled blocks.
For a concrete producer, give every player one action at each of a fixed finite
number of simultaneous reporting rounds. Packet choices cannot create or remove
any player's remaining opportunities. This last condition is used even after
an earlier report was omitted: a merely ex ante promise of one opportunity,
already consumed at that prefix, would not justify invariance of future reports
if the focal action could suppress later opportunities.

At each tail opportunity the actual menu includes silence and every declared
bounded raw batch which the player can form from its current knowledge and own
signing capabilities. It therefore includes:

* partial or empty reports;
* canonical reports of known foreign bodies;
* self-authored bodies, malformed reports and arbitrary permitted wrapper data;
* forwarding bodies learned after TK;
* late application bodies and exact retransmissions.

The report parser is total on this finite raw domain. It ignores invalid
encodings or extracts their verified application bodies; it only adds evidence
to the per-author sets. It never executes a reported application instruction
or changes L. A malformed report can be ignored or create additional liability
for its own author under a separate positive rule, but it cannot erase another
report or lower the sender's existing application charge. No transfer, bounty
or claimant-priority mechanism rewards a reporting choice.

The canonical action of player j is the bounded bundle

    R_j = K_j \ B_j.                                         (3)

It is formed from the frozen snapshot, even if more evidence is learned later.
Use a canonical wrapper and submit the same bundle at every remaining report
opportunity; exact repetition is idempotent. The prescription may instead use
one designated guaranteed opportunity and silence elsewhere, but repetition
avoids relying on a consumable one-report permission.

The service must establish the following facts for every bounded raw tail
profile, not only for canonical reports.

1. Every submitted qualifying canonical report bundle is finalized by TA.
   Its accepted job cannot be cancelled or replaced by later actions.
2. Additional raw traffic cannot suppress, delay past TA, or remove another
   report's qualifying job. The same holds for the old public-body jobs needed
   by the witness comparison and every other existing job which can contribute
   to a player's audit liability. New bodies can add evidence but cannot delete
   a previously determined evidence stream. More generally it suffices that the
   canonical action's final own-author contribution is a subset of the one
   under each alternative, on a common coupling.
3. Each player's terminal report entitlement is segregated, activates at the
   snapshot boundary, and cannot be spent during application play or by another
   player. Earlier partial reports do not invalidate later canonical reports.
4. Every literal raw tail action has a fixed size/work bound, and capacity and
   funding cover the entire finite tail bound, including repeated, partial and
   malformed attempts. Admission or resource accounting cannot give a new raw
   action an indirect censorship effect excluded by point 2.

For example, with at most H_R opportunities in total and worst bounded
publication/verification work g_R per opportunity, reserve H_R*g_R work units,
plus the already declared residual-application allowance. A service rate c_R
with fixed finality delay L_R can use a tail of at least
ceil(H_R*g_R/c_R)+L_R after the last admitted report. The fee reserve must cover
that work at the chosen finite fee bound. An implementation can reduce this
budget later; the proof here does not charge only for the selected report-all
path and leave raw flooding outside the guarantee.

These are service liveness, noninterference and accounting assumptions. They
do not say that a strategic player submits a report. A deposit or a funded
transaction by itself proves none of them.

## 3. Snapshot knowledge does not stop physical reception

TK is a strategy snapshot, not a claim that the network becomes silent or that
players forget later receipts. Residual flights can still arrive; later raw
messages can still be broadcast; actual information sets remember them all.
The prescribed reporter ignores these new data when choosing the bundle (3).

The remaining old jobs have a fixed continuation under the stated immutable
service. Conditional on any reached tail prefix, changing one reporting
action cannot remove an old body's later public appearance or its already
observed copies. Thus the final old public evidence can be coupled identically
between two such actions. Extra bodies can add only positive evidence.

One simple timing choice is TK >= T0+Delta for the retained-prefix publication
bound Delta. It makes every relevant retained body emitted by T0 public before
reporting. The argument also permits its recording later, provided its promise
holds by TA independently of all subsequent raw traffic. No private-flight
delivery bound is needed merely to take the snapshot: a body whose first
possible strategic effect is after T0 cannot improve the frozen base outcome.

All strategic choices before TK remain in the pre-report raw game, including
any evidence-drain interval after T0. They are not replaced by assumed honest
silence. In the stopped raw comparison, an exposure before T0 must be covered
by section 4. If no such exposure occurs before the base freezes, the coupled
base payoffs already agree; subsequent nonnegative charges cannot improve the
deviator's payoff over the clean comparator. This is why a report of every
arbitrarily late newly learned body is unnecessary for the preservation proof.

If an old job can be cancelled during reporting to lower one's own eventual
charge, or if reporting can change the final authorization records, the
pointwise reporting proof below does not apply. Those actions cannot be hidden
inside the word “freeze.”

## 4. Exact evidence availability in the reduced game

For an accusation against i, let W be its finite complete positive witness.
Every signed body in W is i-authored; the remaining witness data are in L.
The actual availability condition is

    W subseteq P_final union (union_{j != i} K_j).             (4)

The union is of actually held complete bodies. Separate nonauthors may hold
different members of a pair. No individual has to recognize the violation at
receipt time or possess a complete global traffic list.

Under the prescribed bundles (3), every member of W held by a nonauthor is
submitted. Guaranteed report delivery and the public part of (4) make W
available to the verifier at TA. Therefore Bad_i=1 with probability one on
every coupled realization satisfying (4).

The runtime proof must derive (4) for its first effectful forbidden message.
Its acceptable cases are a complete-body receipt by a nonauthor game player,
or an actual public body record, with any retained-prefix counterpart still
guaranteed public. A private execution ingress's possession is not a third
case unless it is itself an explicitly modeled strategic player whose report
incentives and opportunity are proved. This note introduces no such actor.

A message which affects execution without public recording and affects other
players without any nonauthor acquiring its complete body does not satisfy
this collection condition. Neither signature verification nor a larger D_i
manufactures the missing evidence.

## 5. Reporting optimality at every actual tail prefix

Fix any reached tail prefix h, including prefixes after earlier partial,
malformed or self-incriminating reports. Fix any player i who acts there.
Give all future other players the prescription (3), based on their fixed K_j.
Their earlier submitted messages are already fixed at h. Their future bundles
are also fixed as functions of their own snapshots; they do not react to i's
new report, to newly forwarded data, or to its new application message.

Couple the service randomness for previously submitted and future prescribed
reports. By section 2, their eventual contribution to the i-authored evidence
set is unchanged by i's current choice. The old public-body contribution is
also unchanged. The canonical bundle R_i contributes no i-authored evidence.
An alternative may contribute none or add i-authored evidence, but cannot
remove any of these fixed contributions. Monotonicity of (1) therefore gives

    U_i(h, alternative; future report-all)
        <= U_i(h, canonical; future report-all)               (5)

on every coupled realization. Extra nonnegative action costs preserve this
inequality when the canonical action has zero cost.

This is a pointwise comparison, so it holds under **every belief** at the
actual information set. It does not assume that past reporters were honest.
It covers malformed wrappers, self-reports, forwarding newly learned data and
late application messages, provided the parser/service conditions above hold.
The conclusion is weak optimality: withholding can be equally good. The theorem
selects a report-all equilibrium; it does not make reporting strictly dominant
or prove collection against every reporting equilibrium.

## 6. Reduced raw extension without circular reporting assumptions

Define G^- to be the finite strategic game up to TK, followed by its actual
residual chance evolution and the prescribed canonical reporting kernel. Its
terminal payoff is the expected value of (2) under that kernel. Equivalently,
retain its residual chance nodes and insert canonical reports as forced moves.
There are no strategic reporting choices in G^-.

First construct the audit-clean retained runtime R and its selected SE using
the [fresh-service and reset proof](se-asynchronous-support-weakening.md).
Then establish the stopped raw comparison in G^-. It quantifies over every
extending **pre-report application profile** and every retained-site belief.
On the first relevant exposure E before T0, equation (4) and the forced
report-all kernel give collection. At a saved-debt or own-exclusion stop, use
the permanent payoff cap. If no such stop occurs before base freeze, the
coupled base payoff is unchanged. For collateral D_i>=U_i^base-F_i, the usual
comparison is

    E[raw net payoff - clean retained comparator payoff]
       <= (U_i^base-F_i-D_i) * Pr(E) <= 0.                    (6)

For an already excluded owner's first historical disclosure, use the direct
upper bound F_i and the retained quiet payoff F_i instead of alleging an audit
offense. The comparator is one legal causal policy over the entire retained
information fiber, as required by the raw extension theorem.

Apply
`GameTheory.Protocol.InformationModel.ActionRestriction.sequentialEquilibrium_extends_of_continuation_unclocked`
from [PassageRestrictionExtension](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean)
to obtain an SE of G^-. The collection argument is valid for all profiles
quantified by this call because reporting is part of the terminal kernel,
not an arbitrary profile variable in G^-.

Calling that theorem directly on the full strategic-reporting game while
asserting that everybody reports would be circular. In that larger game a
withholding profile is legal and need not collect the charge. The next step
proves a separate equilibrium lift instead.

## 7. One common fully mixed sequence in the full game

Let (sigma,mu) be the SE of G^- just obtained, and let
(sigma_n,mu_n) be one fully mixed Bayesian consistency witness converging to it.
All relevant pure-action continuation gains are continuous functions of the
finite profiles and beliefs. Hence their largest positive part r_n tends to
zero. This uses sequential rationality of the limit; it does not require the
generic extension theorem to have returned a preselected report policy.

In the full game G, copy sigma_n exactly before TK. At every actual reporting
information set I, including a site created by earlier report mistakes, choose

    tau_n(I) = (1-rho_n) delta_{canonical(I)} + rho_n nu_I,    (7)

where rho_n>0 tends to zero and nu_I has positive mass on every actual legal
raw tail action at I. The canonical action reports the remembered frozen
foreign snapshot. Its availability after earlier partial reports is supplied
by the terminal entitlement, not assumed from a one-use local menu.

This defines one fully mixed profile on the entire fixed finite game. Form
its actual Bayes beliefs. For a pre-report information set, both its reach
mass and every history weight in its information fiber equal those under
sigma_n: future reporting cannot change them. Its Bayesian belief is therefore
exactly mu_n at each n, not merely close after a rare-event division.

Let H_R bound the remaining number of reporting decisions and B_R bound each
player's terminal payoff spread, including deposits and any allowed costs.
From any actual reached prefix and under any belief, the conditional chance
that a future mixture in (7) uses its noise component is at most H_R*rho_n.
Couple perturbed and prescribed tails until the first such choice. The
continuations agree before then, so

    |V_perturbed - V_prescribed| <= B_R*H_R*rho_n.             (8)

Include the current baseline mixture in H_R when it occurs in a comparison.
The error of comparing a forced action with the current mixed law is at most
2*B_R*H_R*rho_n. These are conditional future bounds from the actual prefix;
earlier reporting mistakes do not introduce an inverse reach-probability term.

At a pre-report site, its pure one-step gain is consequently at most

    r_n + 2*B_R*H_R*rho_n.                                   (9)

At a report site, (5) and (8) give the uniform bound

    2*B_R*H_R*rho_n.                                        (10)

Both vanish. Compactness of the finite profile and belief spaces gives one
common subsequence. Its limit is consistent by construction. Continuity and
the finite perfect-recall one-deviation principle make it sequentially
rational at every pre-report and report site. Thus it is an SE of G whose
pre-report strategy is sigma and whose reporting strategy is canonical.

No hierarchy between rho_n and a rare pre-report information mass is needed.
The pre-report beliefs agree exactly and the tail comparison is uniform from
every actual reached prefix. The new reporting sites are not delegated to the
generic free-agent completion: they are handled explicitly by (5)-(10).

The limit uses report-all exactly, so its joint law of initialized source data,
frozen base result and realized net settlement is the law of G^-. In particular,
if the retained source-preserving law has no audit offense, the full reporting
game preserves its selected net-payoff law as well.

## 8. Existing API correspondence and remaining producer obligations

The applicable existing interfaces are the continuation-extension theorem cited
above and the finite local-gain/limit machinery in
[SequentialOneShot](../GameTheory/GameTheory/Analysis/Protocol/SequentialOneShot.lean)
and [SequentialLimits](../GameTheory/GameTheory/Analysis/Protocol/SequentialLimits.lean).
In particular,
`GameTheory.Protocol.InformationModel.BehavioralAssessment.continuationGain_le_of_localGain_le`
converts the uniform local bounds into whole-policy bounds, and
`GameTheory.Protocol.InformationModel.BehavioralAssessment.isSequentiallyRational_of_converging_deviations_bounded`
accepts a vanishing error along the common sequence. Alternatively,
`GameTheory.Protocol.InformationModel.BehavioralAssessment.isSequentialEquilibrium_iff_locallyOptimal`
applies to the consistent limiting assessment after the local inequalities
have passed to the limit.
No alternative equilibrium definition or new LP solver is required.

The new adapters are concrete: the finite terminal packet parser and menus;
the snapshot and per-author evidence invariant; actual nonauthor/public witness
availability; immutable uniformly live report delivery and segregated funding;
and the equality of pre-report history laws after appending the reporting
stage. A runtime must prove these facts. Report-all is the constructed player
strategy, while delivery of a report that was actually chosen is the service
assumption. Those two statements must remain separate.
