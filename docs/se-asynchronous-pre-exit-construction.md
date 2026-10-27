# A pre-exit construction using hidden transmission delays

This note gives a finite construction for the proper semantic core of an
asynchronous commit–reveal implementation. Its useful feature is that late
transmission can be observationally indistinguishable from an earlier
transmission followed by hidden network delay. This permits a conditional
probability argument at every information set before the first public exit,
including information sets reached after the observer's own earlier waits.

The construction uses no prescribed sender order, no rule that
flushes the entire pending pool, and no global abort payoff. It does require an
explicit support condition on the network, not merely an upper inclusion bound.
The semantic-invalid extension is separated at the end. These are mathematical
derivations; no new Lean result is asserted.

Only the pre-exit menus are restricted to the proper core. After the first
public exit, the handler may already be the full finite raw-message game with
its actual audit settlement. This avoids requiring a proper-value selector
at a post-failure source state where its guard may be unsatisfiable.

## 1. The finite window model

Use a finite time grid, finitely many players, finite message alphabets, and a
fixed finite bound on all transmission opportunities. Source initialization may have
arbitrarily correlated private information. Each semantic phase has:

* public readiness time r;
* simultaneous availability of SEND or WAIT to every active owner at each block;
* a protected admission cutoff A=r+Gamma;
* a public settlement boundary D=r+Gamma+Delta, with a fixed endpoint order;
* at most one qualifying immutable first entry per owner in the window;
* recording of every qualifying entry admitted at a by a+Delta, including an
  entry whose inner game call has become stale.

All players may transmit during the same protected interval. Their opportunity
to do so can be common knowledge; there are no prescribed sender turns. The
network has one broadcast action, with chance determining who observes it
before ledger publication. No sender selects a separate confidential channel.
Message bodies do not authenticate their original admission time.

The state at the boundary records all inclusions through D and the consequent
exits before another strategic decision occurs. Equivalently, expiry can be a
publicly computable predicate of the finalized ledger watermark. A separate
timeout transaction must not leave an interval in which the recording deadline
has passed but the protocol still treats the known failure as unannounced.

The next semantic phase waits for the publication barrier for the preceding
window. Entries admitted before closure are therefore public before another
binding choice. This is the already-derived
[publication inequality](se-asynchronous-publication-contract.md), not an
additional obstruction concerning covered old messages.

For the proper core, a commitment entry hides its entire semantic value; its
wire shape, admitted size and service class do not depend on that value.
An opening is the unique correct opening of the accepted commitment. Transport
and routing probabilities depend on operational metadata rather than on the
hidden source realization or the contents of a correctly formed payload.
Each owner sends at most one first entry, so after sending it has no remaining
gameplay transmission choice in that window. Retransmission and malformed
entries require their separate comparison or enforcement argument.

One entry can contain the owner's whole phase vector. This requires the
source-phase equivalence: no new foreign source observation arrives between
that owner's component choices, and later legal menus depend only on its own
earlier components and the phase's existing source information. Presampling a
legal vector then implements its original behavioral distribution. This is a
compiler representation of that phase, not a change in the intended game.
Alternatively the argument can be applied to suitable fixed dependency layers.

The owning source syntax has useful structure here.
`Vegas.SourceGuardRead` in
[Basic](../Vegas/Source/Basic.lean) is fixed when its commitment is introduced.
Publications it reads already exist then; unresolved commitment reads belong
to the guard author. A guard cannot acquire a dependency on a foreign
publication introduced later in that reveal block.
`Vegas.SourceProgram.Setup.WellFormed` and
`Vegas.SourceProgram.GuardsSatisfiableFrom` in
[IntendedGame](../Vegas/Source/IntendedGame.lean) ensure that intended choices
remain guard-admitted along intended histories. Private-dependent value menus
do not by themselves make packet timing value-dependent: the normalized law
on each actual legal menu still sums to one.

## 2. The normal-explanation property

Call an owner normal in a window when it admits its proper entry by A. Its
recording is then guaranteed by D. The following property is about finite legal
histories, not about player knowledge of the scheduler.

**Normal-explanation property.** Let h be a history before the first public
exit and at a decision of i. If another owner j previously remained unsent after
a protected cutoff, there is a history R_j(h) in which j was normal in every
preceding window, with the following properties:

1. Initial source data, all semantic values, public source samples and all
   delivered envelopes and ledger records are unchanged.
2. Every other owner's complete local information and action word are
   unchanged. In particular i's current information is unchanged.
3. Only j's post-cutoff action, admission and unobserved flight history is changed.
4. The repaired chance prefix has positive probability. Over the fixed finite
   game, the relevant positive chance ratios have a common lower bound c>0.
5. Source action probabilities at the repaired admissions are the same as in
   h. The source prescription ignores the changed operational record.

Here is the elementary broadcast-network construction behind this property.
If j's original first admission is s<=A, leave it unchanged. If s>A, replace
its WAIT at A by admission of the same entry. Keep all earlier opportunities,
waits and observations unchanged. Select no new observation of that entry
until its actual first exposure, then preserve the original receipts and
recording. Any record already observed in the window has time at most D, so
its new delay is at most Delta. If no entry has been observed yet, it can remain
unobserved through the present prefix and be recorded by D. Apply this to each
of j's completed windows; their source outcomes and boundary times stay fixed.

This argument needs the proposed schedules to be in the actual service's
support. A concrete producer permits every causal observation/recording pattern
satisfying the delay bounds, including no new receipt of a given broadcast
before its ledger recording. This positive-probability no-new-receipt pattern
is an explicit property of the observation rule, not a separate private channel.
A bounded queue model must additionally prove that the repaired pattern is
feasible under its capacity constraint.

An ample-capacity finite example permits every subset of the window's at most
M first entries to be recorded in a block, while requiring due entries to be
included. Assign positive probability to every permitted subset. Capacity at
least M makes all such repairs feasible; it does not require choosing the full
subset or mandate a full-pool flush. With smaller capacity, feasibility is an
additional theorem. A prefix with too many missing entries for the remaining
slots can otherwise rule out every normal explanation before D.

The property fails if the observer can inspect the complete undelivered pool,
if a signed receipt proves the original admission time, or if earlier
unobserved admission necessarily changes an observable service decision. None
of these failures is repaired by merely assuming eventual inclusion.

## 3. A uniform conditional bound on other owners' mistakes

At index n, fix type-independent early emission hazards rho_t in (0,1)
throughout the protected interval t<A. At A, an owner still unsent broadcasts
with probability 1-epsilon_n and waits with probability epsilon_n. The proper
value has its prescribed source distribution. Later operational policies can
be arbitrary fully mixed policies, including policies selected by a simultaneous
information-agent equilibrium. The early hazards depend only on public window
and time, not on the owner's accumulated operational record.

Let m bound the number of windows in one owner's complete history, and N the
number of finite histories. If h contains an abnormal window for j, its WAIT
at that window's A contributes epsilon_n. Each repaired cutoff contributes
1-epsilon_n instead. Earlier hazard factors cancel because the corresponding
waits and their public times are unchanged. After j's repaired entry has been
sent, its later actions in that window are forced silence. Source value factors
are unchanged, as are all other players' action factors by property 2.
The chance-ratio bound therefore gives

    weight_n(h) <= [epsilon_n / (c(1-epsilon_n)^m)]
                   weight_n(R_j(h)).                         (1)

No lower bound on a late operational action probability is used. If exact
source-factor cancellation is unavailable but the repair replaces at most d
source choices by supported choices of probability at least a_n, multiply the
denominator in (1) by a_n^d instead.

For an owner whose current entry has not yet been sent, use a finite augmented
probability space: at window readiness, sample its potential legal source
vector from the prescribed source kernel, but do not expose or install that
vector until its first send. The operational prescription ignores this unused
vector, so summing it out gives exactly the original history law. The repair
uses that same potential vector for its added cutoff send. Its source factor
then occurs on both sides of (1), including when the original history has no
literal semantic-send action yet. Apply the finite-history sum below on this
augmented space and then marginalize the unused vectors. Thus the specified
proper-core model needs no inverse minimum source-action probability. This
argument presamples only the player's permitted source choice; it does not
reveal a foreign value or give a strategy knowledge of future service coins.

At any actual pre-exit information set I of i, the repaired history is in that
same information set. Hence weight_n(R_j(h))<=mass_n(I). Summing (1) over bad
histories and foreign owners yields

    Pr_n(some foreign past abnormal window | I)
      <= |Players| N epsilon_n / (c(1-epsilon_n)^m).            (2)

This applies even when I is reached after many waits by i itself. Its own
information and action word are retained, so its possibly tiny own-play factor
cancels. The repair need not be injective. All divisions use positive masses
at the current fully mixed index, never a limiting off-path mass.

From a history with no foreign past abnormal window, a future foreign cutoff
WAIT has probability at most epsilon_n conditional on still being unsent.
Thus their union has probability at most L epsilon_n, where L bounds the
remaining protected cutoffs. Therefore, under any unilateral counted
continuation of i, foreign normality fails with conditional probability at most

    e_n = |Players| N epsilon_n/(c(1-epsilon_n)^m)
          + L epsilon_n.                                    (3)

This also uses the inclusion contract uniformly against i's allowed traffic.
Otherwise i could make a normally admitted foreign entry miss its deadline by
congestion, and protected admission would not imply foreign success.

## 4. One operational equilibrium, with no source types in its policy

Consider the finite operational window game that erases payloads and pays each
player the indicator that its own first entry is successfully recorded by D.
It retains actual local action, receipt and ledger metadata. It is not
a game in which the global schedule is public.

Fix the early hazards and the cutoff send probabilities as above. At all later
operational information sets, impose positive action floors with total mass
eta_n and take a Nash equilibrium of the finite information-agent game.
Existence follows from compact convex strategy sets and multilinear payoffs.
All other agents' policies are fixed when one agent optimizes.

For several windows, use one finite operational process stopped at the first
public exit. Each information agent receives the indicator of its owner's
completion in that agent's current window, multiplied by the indicator that
the agent's information set is reached. Different agents need not have the
same objective; this is an auxiliary finite agent game. Joint optimization
therefore uses one history law and one set of Bayesian entry beliefs, rather
than independently selecting window policies with unrelated entry priors.
An agent's current action cannot change its own prior reach probability.

At a later information set, positive reach allows agent optimality to be
converted to conditional optimality. The constraint costs at most eta_n times
the payoff range, which here is one. Thus every operational local gain is at
most eta_n. There is no inverse-reach loss. At any protected time t<=A, the
prescribed remaining hazards admit the entry by A with probability at least
1-epsilon_n. That event guarantees own success.
Its current completion regret is therefore at most epsilon_n, including at
early times where WAIT has a fixed positive probability. Put

    t_n = max(epsilon_n,eta_n).                              (4)

Use this same operational policy across source types. It may react to its full
actual operational information and need not be prompt after its own earlier
wait. Its existence is simultaneous across players and information sets, not
a collection of incompatible individually chosen timing rules.

Why can the policy ignore opening contents? In a content-blind transport model,
write X for source data and source random coins and Z for operational data.
At a fixed source phase, their joint reference law factors. Actual information
has the form

    (source own information, K(Z), V_K(X)),

where K is the remembered delivery/ledger pattern and V_K consists of the
payloads actually received in that pattern. Conditioning on K=k and V_k=v
restricts the two factors separately. Payloads do not change the posterior
operational law beyond k. They can change the expected source payoff, but not
which policy maximizes the probability of own success. At a commitment phase,
current entries are opaque, so V_K contains no foreign current choice.

The factorization extends across all completed windows by induction. Represent
the source initialization and all potential source behavioral/chance choices
by X, and the transport and operational random choices by an independent Z.
This is a probability representation, not disclosure of future choices. The
source prescription ignores operational history; the service ignores semantic
payloads; and the proper source layout and message counts are fixed. At each
completed window, its no-exit condition restricts operational history only.
The newly public semantic values restrict X. At the next binding window all
earlier received opening values are already in the public source record.
Conditioning on that record therefore preserves the two-factor form. Private
value menus may vary with source information, but each normalized semantic
choice kernel still sums to one when its opaque value is erased. This is why
the same operational information-agent game supplies the actual conditional
operational beliefs throughout the pre-exit process.

This is a substantive routing premise. An arbitrary content-dependent selector
can instead communicate X xor Z and couple the two conditional factors.
Initial independence alone does not justify ignoring the payload in that model.

## 5. Transfer the operational comparison to actual utility

Let sigma_n be one fully mixed source witness converging to the selected source
SE. Let R_n->0 bound its relevant source phase-choice gains, with the
phase-vector equivalence used when an owner has several component choices.
Use sigma_n's semantic distribution whenever an owner sends its entry, and
the common operational policy of section 4 for whether it sends.

Suppose all intended source-continuation payoffs are at least F_i. Other handler
outcomes need only be bounded; they are included in the exceptional-event error.
Own failure fixes i's base utility at F_i. With no audits this is its exact
continuation payoff. With an audited handler, section 6 gives a uniform
conditional interval [F_i-zeta_n,F_i], with zeta_n tending to zero, from a clean
own-exit entry. Work before the first public
exit. On the good event in (3), all foreign entries are normally sent and
successfully recorded by the fixed boundary, whatever i's counted timing.
Only i's own completion can fail in that window.

After a successful window, couple future source play using the same source
coins. With probability at least 1-L' epsilon_n, every subsequent protected
cutoff is met. All future windows then succeed, and their typed source history
equals that source continuation. This is a uniform future-error bound,
not a statement about the probability of reaching the current information set.

For a binding information set, let v_n(J,a) be the source continuation value
after semantic choice a, and let q_n(I,b) be own completion probability after
operational choice b. Up to the bounded error from (3), future missed
protected cutoffs and zeta_n, the actual value is

    F_i + q_n(I,b) [v_n(J,a)-F_i].                            (5)

The source posterior at J follows from the normal-history factorization:
other players' proper source actions have their sigma_n laws; metadata is
source-blind; the observer's own action factors cancel by perfect recall.
The weight of nonnormal foreign histories contributes the error in (3).
Timing never permits a new foreign semantic observation before committing.

For an opening site there is no new semantic action. The same equation uses
the expected source continuation given the actual received payloads. Its
surplus over F_i is nonnegative and the conditional operational factorization
in section 4 applies.

Let B bound all utility differences in the finite implementation, including
handler outcomes. A current semantic alternative contributes at most R_n;
a current operational alternative contributes at most B t_n. Changing either
continuation on an event of probability e changes the comparison by at most
2B e. Consequently a uniform pre-exit bound is

    actualGain_n(I,a) <= R_n + B t_n
                        + 2B(e_n + L' epsilon_n) + 2 zeta_n.   (6)

The same estimate covers arbitrary mixed current alternatives by linearity.
Importantly, the foreign-failure continuation has not been replaced by F_i.
It is bounded by B and charged to the uniformly small exceptional probability.
Own failure alone uses F_i.

## 6. Complete the handler on its actual private information

After the first public exit, do not copy the old proposal-archive source
prescription. Complete all remaining actual information agents jointly with
positive action floors. Fix an exited player's near-silence policy only when
its total payoff comparison justifies that prescription. The public permanent
marker prevents these handler histories from merging into copied pre-exit
information sets.

The operational policy of section 4 and the source prescription can be fixed
while this completion is chosen. Estimate (6) is uniform over the resulting
bounded handler continuations. Handler agents have vanishing constrained
local regret. The first exiter's actual payoff must remain capped as required
by the [first-quitter theorem](se-quit-handler-preservation.md).

For an audited full-raw handler, require that an exited player's base utility
is F_i, charges are nonnegative, and from a clean own-exit entry its legal
quiet continuation cannot acquire an authentic new liability. Already retained
proper messages are audit clean, including their delayed recording. Thus quiet
guarantees net F_i from such an entry, under any other players' handler policies.

Let xi_n bound the total local handler action-floor mass, and let H_h bound the
number of future own decisions. Each handler information agent has unconstrained
pure-action regret at most B xi_n. Replace the exited player's continuation by
quiet and telescope the corresponding one-step differences. Perfect recall
means that each later own information set remembers the entry information,
the preceding own action and the public exit. Its hidden-history posterior is
unchanged by this unilateral policy replacement: the own-play likelihood
factors cancel. Hence, for the actual Bayesian entry distribution,

    F_i-H_h B xi_n <= V_handler,n <= F_i.

Take zeta_n=H_h B xi_n. This is not a bound conditional on an arbitrarily more
informative hidden node. It is the expected continuation bound needed by the
pre-exit one-step comparison. No separate loss for a trembled quiet comparator
is needed: pure quiet is a legal policy of the actual game, and the pure-action
regret bound has already accounted for the artificial floor constraint.

Choose epsilon_n,eta_n,xi_n->0, and, if needed, epsilon_n=o(a_n^d). One common
subsequence of the resulting fully mixed Bayesian assessments gives an SE
of this proper-core implementation. On the initialized limiting path every
protected admission cutoff is met, hence every qualifying entry arrives on time.
The phase equivalence and publication barrier give the selected initialized
source state/outcome/payoff law. No independence between players' initial
private information was used.

This is a finite sufficient theorem for the stated normal-explanation,
content-blind service and proper-core model. Its main new comparison is (6):
foreign failure is conditionally negligible at every pre-exit site, while
later own timing is solved jointly in one operational game.

## 7. What this theorem does not silently classify as a timing mistake

An unusable handle or a guard-invalid semantic binding is not a late proper
entry. In particular, an authentic guard-invalid opening privately received
before public rejection can certify foreign failure. Changing its binding to
a proper one changes the observed bytes, so the normal-explanation repair
does not apply to that history.

The counted semantic extension needs its own stopped normalization argument.
The useful runtime structure is: before commitment settlement, a changed
private binding has the same opaque wire; foreign commitment failure rolls
both versions back before any valid opening; after a successful save, the
invalid version irreversibly owes its owner a failure, while proper continuation
payoffs remain at least F_i. A causal own-memory simulation must preserve every
legal counted continuation after rollback, including inaccessible old handles.
These are the specific hypotheses for the owning binding-shadow comparison,
not a consequence of (2).

The save stopping point is essential. A guard is evaluated at its last required
publication, not necessarily when its subject is opened. For example, let an
earlier own commitment a require a=0 and a later own commitment b require b=a.
Raw a=b=1 is repaired to a=b=0. The source may reveal b, make another commitment,
and reveal a only afterward. The first changed opening b then has no immediately
public false-guard witness. The source adapter below deliberately preserves
this pending-obligation behavior.

After the bad block is irreversibly saved, however, the earliest invalid
binding guarantees its owner's eventual floor. If any of that owner's required
publications fails or is omitted, it is excluded. Otherwise every own guard
input eventually publishes its immutable binding, and
`Vegas.SourceProgram.Obligation.accepts_eq_predicts` makes the initially false
prediction fail when the final input is published. Previously available public
guard inputs cannot change. Only the current unsaved commitment block may roll
back; a later foreign failure cannot erase this older saved obligation. This
requires actual guard checking and owner exclusion as part of the controller's
progress rule, not merely a requirement that some opening bytes eventually exist.

The semantic shadow can therefore stop at irreversible bad save and compare
raw eventual payoff at most F_i with a legal clean quiet continuation paying at
least F_i. Before that save, genuine current-block opening authorization does
not exist; a foreign rollback erases the changed live values, while an exposed
premature opening is covered by its authorization defect. No stronger
publication order or immediate guard witness is needed.

Historical raw openings, conflicting entries, retransmission effects and other
raw disclosures then need the authenticated action-extension comparison. The
reserve and reporting lemmas apply only after their evidence and incremental
collection hypotheses are supplied. Thus the proper-core theorem is not a
claim that every raw private disclosure has already been normalized or audited.

## 8. The source adapter for finite linear Vegas programs

For the existing `Vegas.SourceProgram` syntax, the required successful-path
phase grouping can be derived directly. Its constructors are commit, reveal,
public sample and return. There is no data-dependent branch or hidden loop in
that syntax. Assume the finite intended game and
`Vegas.SourceProgram.Setup.WellFormed` hypotheses used above.

Split the syntax into maximal consecutive commitment blocks, maximal consecutive
reveal blocks, and individual public samples. Never move a choice across a
public sample or another publication boundary. The following argument is about
this source syntax; a richer frontend must first establish the same properties
for its elaborated source program.

**Commitment blocks.** The definition `Vegas.sourceObserve` in
[Semantics](../Vegas/Source/Semantics.lean) exposes public cells, publications,
the observer's own inputs and its own commitments. It hides every foreign
commitment. `Vegas.SourceProgram.commitSuccessor` appends a commitment only to
its owner's private history. Thus, by induction through a commitment block,
the information at player i's kth choice is a deterministic function of its
phase-entry information, its previous k-1 own choices and the fixed syntax.
Intervening foreign commitments add only fixed-position hidden cells.

The intended menu is computed from this same observation by
`Vegas.SourceProgram.ProtocolView.intendedAvailable`; well-formedness makes
its predicted-value set nonempty at every intended prefix. Consequently the
set of legal own vectors is a function of phase-entry information alone,
with later components checked against the earlier components of that vector.

For a source behavioral profile beta, define the vector kernel by

    beta_i^block(a_1,...,a_k | J_i)
       = product_l beta_i(a_l | J_i,a_1,...,a_(l-1)).

Successive summation over the last component proves normalization. Conditioning
on a complete phase-entry history, the original interleaved joint choice law
is the product of these player kernels: the finite factors can be regrouped
by owner because none reads a foreign current choice. This proves exact
equality of the resulting typed state, not merely expected utility.

A vector deviation can be implemented by sequential conditional probabilities
over its own prefixes; choose any legal action at zero-probability prefixes.
Conversely every original own behavioral continuation gives such a vector
kernel. At an owner's first original choice, intervening foreign choice laws
sum to one and add no source observation, so its phase-entry posterior is the
batch-entry posterior. Sequential rationality of the original source assessment
therefore bounds every vector deviation. Applying the construction to the same
fully mixed source witness supplies the batch beliefs and limiting rationality
on one sequence. A player with no commitment in the block has the singleton
empty vector. All previous own vectors and source observations remain in recall.

**Reveal blocks.** Intended reveal has the single action true. An owner's
required opening values are already fixed by its accepted bindings. Each guard
was created at its commitment; its public reads existed then and its other
commitment reads belong to that same owner. A foreign publication introduced
later in the current reveal block therefore cannot become a new guard input.
This follows from the indexed constructor `Vegas.SourceGuardRead`, not from
an assumption that a future guard will ignore newly published data.

The controller may collect each owner's vector of certified openings in one
window and then replay the block's `Vegas.SourceProgram.revealSuccessor` steps
in their original syntax order. On the proper path all those publications
match their bindings. The exact prediction identity
`Vegas.SourceProgram.Obligation.accepts_eq_predicts` in
[GuardPrediction](../Vegas/Source/GuardPrediction.lean), together with the
intended guards, gives the same guard verdicts. Obligations whose inputs are
not all revealed remain pending just as in the source. No additional semantic
choice occurs while this reveal block is being collected.

Thus the typed state, obligations, revelation map and each owner's semantic
action history after the block are exactly the original ones. Ledger arrival
order can differ; the semantic history is reconstructed in source-event order
from the publicly recorded vector. All current opening values are public before
the next commitment block. The extra arrival order is operational information
handled by the conditional factorization, not an invented source observation.

**Public samples and return.** Execute each sample at its original boundary
using exactly its source kernel evaluated on the already reconstructed public
environment. `Vegas.SourceProgram.sampleSuccessor` then installs the same value.
Return uses the same final typed state and original utility function. Induction
over the block/sample decomposition proves equality of the joint initialized
source-state, source-outcome and utility law whenever all proper windows
succeed. The probability of a missed protected cutoff vanishes in the constructed
sequence, giving the asserted limiting joint law.

This discharges the mathematical source adapter for finite well-formed programs
of this linear syntax under the specified vector compiler. It does not claim
that the current Lean compiler has already been changed to implement those
windows, bundles or canonical reconstruction steps.

## 9. Observable replay batches and fresh opaque labels

The simple menu above has one fresh first entry and silence. The same proof
extends to a finite broadcast-batch menu when its support permits the following
repair. In each block, choose a multiplicity between zero and K for every known
canonical body; an unsent owner may also introduce one fresh current body with
positive multiplicity. There is no smaller shared aggregate bound that prevents
adding that one body while keeping the old replay coordinates. The finite body
alphabet, finite K and finite time horizon still bound the entire traffic load.
This is one broadcast batch, not a separate recipient-selecting channel.

After protected admission, prescribe a fixed full-support distribution on the
available replay multiplicity vectors, with a uniform positive minimum d. The
law depends on known entry identities and other operational metadata, not on
their semantic contents. At A, own admission has probability 1-epsilon_n and
every compatible replay vector retains positive probability. Late timing agents
optimize over the complete remaining operational batch menu.

To repair a late owner, add its hidden first body at A while leaving every
original replay coordinate unchanged. At its original later first-send time,
broadcast the same body and multiplicity as a replay. All original later replay
choices remain legal: the repaired owner retains its original received bodies
and additionally learns its own body sooner. Preserve all observed duplicate
receipts. Only sender-local knowledge of whether the first admission already
occurred changes. There must be no authenticated global admission-rank field
which exposes that distinction to another actor.

At most H_r later action factors are replaced by fixed replay factors. Their
cost in the likelihood ratio is at most d^(-H_r), a constant independent of n.
Thus (1)--(3) retain their vanishing epsilon_n numerator. Once a protected first
entry is admitted, own completion is guaranteed and every replay choice has
the same completion payoff one. Nonparticipants have no required completion to
improve. Their fixed replay law therefore has only the already-bounded actual
utility error from foreign failure or future missed cutoffs. The late agents'
completion comparisons continue to be supplied by the joint operational game.

The batch support matters. In a one-packet menu, an observed replay at A can
prevent insertion of the owner's first entry while preserving that receipt.
Replacing the original later send by a replay does not fix this earlier
collision. Such a menu does not obtain this replay extension for free.

Fresh opaque handle labels can also be varied if the fresh-label set is
metadata-measurable and independent of the hidden semantic value. Use a fixed
full-support label law and construct the operational game on the label-erased
controller, with service and routing invariant under consistent fresh-label
renaming. Lift its policy to ignore the actual label names. Every proper value
then has the same label possibilities, and a label deviation has the same
controlled completion law because other prescribed policies also ignore names.
The extra label factors are source-independent likelihood factors, not new
information about a private value. For finite label sets their positive minima
are absorbed into the constant in (1).

This argument does not cover a supposedly fresh label whose availability
secretly depends on a semantic value, a sender-chosen label with a verifiable
relation to that value, or service that treats different labels differently.
Reuse of an initialized or earlier allocated handle belongs to the raw
classification and its positive-witness argument.
