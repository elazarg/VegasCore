# Asynchronous reference information and conditional incentives

An information refinement used only in a proof can expose past transport and
service history without giving that information to the actual players. This
can repair the missing likelihood argument for private reception and visible
replay. It does not, by itself, replace the service assumptions of the
continuation comparison being transferred.

There are two distinct conclusions here. The finite filtering and repair
arguments below justify a substantially richer reference information model
for the existing indexed preservation construction. Extending its service
producer to arbitrary asynchronous bounded inclusion remains a separate
mathematical obligation. A bounded-inclusion counterexample at the end shows
why the existing prompt continuation cannot simply be retained for every such
service. No new Lean theorem or asynchronous preservation capstone is asserted.

## 1. The reference signal

Let h be a finite native history and t a supported service seed. Use the
explicit latent-seed implementation rather than treating the behavioral
scheduler's posterior as an independent draw. For the prescribed profile at
index n, write its joint reach weight as

    w_n(h,t) = r_n(h) p(t | h).

Here r_n is the actual history reach weight and p(t|h) is the actual seed
posterior computed from environment recall. Equivalently,

    w_n(h,t) = prior(t) r_n^t(h).

The equality is the existing scheduler-mixture realization, not an assumption
that an observed history is independent of the scheduler. The source initial
law may correlate players' private inputs arbitrarily. The existing service
construction samples its seed separately from that source initialization.

For player i, let I_i(h) be its original complete-pending information. Define
the refined reference information to be

    F_i(h,t) = (I_i(h), L_i(h,t)),

where L_i records the past operational wire and service prefix: submitted
envelopes and their order, inclusion and rejection receipts, public application
states, actual commands, and elapsed service flags. It does not record another
player's private preparation, hidden source cells, or future service flags.
Keep the entire prefix, so past refined observations are remembered.

Elapsed flags are needed if the service has hidden no-op branches. An enabled
processing epoch on an empty queue and a disabled processing epoch may both
produce the command WAIT. Recording only realized commands then fails to say
which branch would have processed a replay. The reference can distinguish
those past branches without revealing a future flag to actual players.

Keep the old dependent action menu at F_i and copy the prescribed strategy:

    beta_n^+(I,l) = beta_n(I).

This is a legal fully mixed profile when beta_n is fully mixed. Its physical
law, after erasing the added observations, is exactly the old law at every n.
The issue is sequential rationality under the new Bayes beliefs, not legality
or the initialized marginal.

## 2. The existing mechanical index is already sufficiently rich

`Vegas.PhaseProposalQualifiedBinding.mechanicalProjection` and
`Vegas.PhaseProposalQualifiedBinding.mechanicalWord`, in
[PhaseProposalNativeSourceInformation](../Vegas/Game/PhaseProposalNativeSourceInformation.lean),
record every raw step, including silent callbacks. Their fields include the
public application, the network's service projection, receipts, environment
recall, and the focal observation and recall. The service projection really
contains the full pending pool and submitted input list: see
`Interaction.MessageNetwork.publicView` in
[MessageNetwork](../Interaction/MessageNetwork.lean). It is the scheduler's
projection, not a claim that the ledger publicly reveals pending traffic.

The mechanical projection also records prepared-slot freshness. This is
stronger than the proposed reference signal. Erase foreign freshness and
other private-preparation data when defining L_i; do not expose those merely
because the proof's bookkeeping contains them.

`Vegas.PhaseProposalQualifiedBinding.MechanicalIndex` is a mechanical word
paired with the original service tape. Thus the proposed label has the form

    L_i(h,t) = ell_i(mechanicalWord_i(h), t).

For the intended past-only refinement, ell_i reads just tape coordinates
whose service opportunities have elapsed. The tape is used as an integration
index in the proof. It is not added to actual players' information.

## 3. Filtering a source–mechanics rectangle

The relevant existing result is
`Vegas.PhaseProposalQualifiedBinding.qualified_annotation_native_balance` in
[QualifiedBinding/Likelihood](../Vegas/Game/QualifiedBinding/Likelihood.lean).
Its normalized native replay law is already indexed by each original
mechanical word and tape. Summing that law gives
`Vegas.PhaseProposalQualifiedBinding.qualified_annotation_rectangle_of_native_atoms`
in [QualifiedBinding/AnnotationMass](../Vegas/Game/QualifiedBinding/AnnotationMass.lean).

Here is the exact finite algebra needed for an information refinement.
Fix one original native information site I and its associated source site J.
Let k index mechanics, g a source history at J, z a completed source block,
and a a legal proper binding value. The existing annotation identity has the
form

    A_n(k,g,z,a) = c_n(k) d_n(g,z,a),                    (1)

after dividing by the positive common source-own-play and class factors.
The coefficient c_n(k) is nonnegative and **does not depend on a, g or z**.
The source density is

    d_n(g,z,a) = r_n^S(g) 1[foreign-good(g)] K_a(g,z),

where K_a is the normalized source forced-block kernel. Therefore

    sum_g,z d_n(g,z,a) = M_n(J)

is independent of a. This is a weighted product identity, stronger than an
equality of an already averaged payoff.

For a refined label l, restrict the mechanical sum to ell_i(k)=l. Then

    sum_{k:ell_i(k)=l} A_n(k,g,z,a)
      = C_n(l) d_n(g,z,a),

    C_n(l) = sum_{k:ell_i(k)=l} c_n(k).                (2)

**Proof.** Substitute (1) and factor the term d_n(g,z,a) out of the finite
sum. No conditional independence is introduced. If C_n(l)=0, every selected
qualified mass is zero. If C_n(l)>0, summing over g,z gives
C_n(l) M_n(J). Normalization cancels C_n(l), leaving exactly the same
foreign-good source posterior and forced-block kernel as before. ∎

The refinement restricts mechanics, not source histories independently of
their annotation. The association between a native history, its mechanical
index and its source counterpart remains the existing one. In particular,
one may not replace (1) by a bare equality of terminal marginals and expect
(2) to follow.

Let m_n(I,l) be the actual refined information mass and Q_n(I,l) its qualified
submass. For positive information mass put

    rho_n(I,l) = Q_n(I,l) / m_n(I,l),
    0 <= rho_n(I,l) <= 1.

Equation (2) proves that this retained weight is independent of the current
proper value a. The qualified payoff law at the refined site is therefore

    rho_n(I,l) * sourceCausalLaw_n(J,a)
      + (1-rho_n(I,l)) * delta_none.                 (3)

This is the refined version of the qualified-binding comparison. A refined
cell with zero qualified mass uses the all-none branch. A feasible cell has
positive information mass at every full-support index; never divide by its
possibly zero limiting mass.

If R_n is a uniform upper bound on the positive source local gains, (3)
contributes at most R_n, because multiplying a gain by a number in [0,1]
cannot increase its positive part. Source error terms from conditioning away
foreign bad preparation remain the existing source-site errors at J. They
are not conditioned again on l: the cancellation in (2) is exactly what
justifies that statement.

## 4. Bad-preparation posteriors in the refined fibre

The annotation argument is used on good histories. The probability of a bad
history must still be bounded conditional on the refined site. An old
coarse-site bound alone would be insufficient.

The existing repair is unusually strong.
`Vegas.EventGraphRuntime.BindingShadow.repair_counted_history` and
`Vegas.EventGraphRuntime.BindingShadow.repair_counted_history_ownPlay` in
[PhaseProposalShadowHistory](../Vegas/Pending/PhaseProposalShadowHistory.lean)
preserve the entire external prefix. The record
`Vegas.EventGraphRuntime.phaseExternalObservation` in
[PhaseBindingOpaqueStep](../Vegas/Pending/PhaseBindingOpaqueStep.lean) contains
the full network, receipts, environment recall, the public application view,
and every non-designated player's own information. The repair retains the
literal initial draw and works under the same fixed scheduler.

Consequently, when repairing a foreign owner's unusable preparation, use the
same tape t. All submitted bytes, inclusion/command history and elapsed flags
are unchanged. The focal player's original I and proposed L_i are unchanged.
The repair can change the designated owner's private catalogue, which is why
that catalogue must not be part of L_i.

The finite conditional estimate needs no injective repair. Suppose every bad
joint prefix x=(h,t) in a refined fibre F has an image R(x) in the same fibre
such that

    w_n(x) <= b_n/(q a_n^d) * w_n(R(x)),              (4)

where q>0 is a fixed positive chance floor, a_n>0 is a lower bound on every
required repaired owner action, and d bounds the repaired owner word length.
Let N bound the number of joint prefixes. Since w_n(R(x)) <= mass_n(F),

    Pr_n[x | F] <= b_n/(q a_n^d).

Summing over all bad prefixes and then over foreign owners gives

    Pr_n[foreign bad preparation | F]
      <= |Players| N b_n/(q a_n^d).                 (5)

This proof works at every refined fibre, including extremely rare ones.
Choosing b_n=o(a_n^d) makes (5) uniformly vanish. The source and ordinary
operational trembles determining a_n are chosen first; b_n is chosen after
them. Positivity at each index is retained.

The exact existing probability surfaces are
`Vegas.EventGraphRuntime.PhaseProposal.historyReach_le_of_designated_word` in
[PhaseProposalRepairLikelihood](../Vegas/Game/PhaseProposalRepairLikelihood.lean)
and
`Vegas.exists_phaseProposal_generatedPreparation_posterior_bound` in
[PhaseProposalPreparationPosterior](../Vegas/Game/PhaseProposalPreparationPosterior.lean).
Their proof is precisely the per-bad-history estimate followed by summation.
The extra work for refined sites is to retain the same tape and record that
the external repair preserves L_i. With the finite supported tape law, one
may choose a common chance floor over its supported fixed-tape histories.
The factor prior(t) cancels from (4); no assumption that it is uniform is used.

## 5. Why the timing comparisons survive this conditioning

`Vegas.phaseProposal_unflagged_wait_finish_le` in
[PhaseProposalCleanBindingGain](../Vegas/Game/PhaseProposalCleanBindingGain.lean)
is a fixed-history, fixed-tape inequality. At an authentic clean unsent
binding it compares waiting now with the prescribed ordinary continuation.
Its hypotheses include no saved/current own failure, no already forced reset,
no foreign generated unusable preparation, and the existing service margins.

Write its two continuation values as V_wait(h,t) and V_prompt(h,t). The owning
result states, on the appropriate good histories,

    V_wait(h,t) <= V_prompt(h,t).                    (6)

For any refined posterior nu on those pairs, multiplying (6) by nu(h,t) and
summing preserves the inequality. Thus observing a past flag that predicts a
future flag causes no problem **when (6) holds for every supported full tape**.
No future tape is made available to actual players by this averaging proof.

Publication and already-flagged binding comparisons also have fixed-tape
stopped-continuation proofs in
[PhaseProposalPublicationGain](../Vegas/Game/PhaseProposalPublicationGain.lean)
and [PhaseProposalCurrentBindingGain](../Vegas/Game/PhaseProposalCurrentBindingGain.lean).
Their top-level gain statements do not require Bayes consistency of the
displayed assessment. This permits arbitrary refinements that are functions
of the native history alone. If the label also reveals elapsed hidden tape
flags, however, it changes the continuation tape posterior at a fixed native
history. Then use the underlying fixed-tape comparison and integrate against
the **new** posterior; merely replacing the old assessment's belief on native
histories would leave the wrong continuation kernel.

The marginal identity
`Interaction.ReactiveApplication.schedulerMixture_finish_marginal` in
[ReactiveSchedulerTerminalMixture](../Interaction/ReactiveSchedulerTerminalMixture.lean)
and the actual posterior in
[ReactiveSchedulerImplementation](../Interaction/ReactiveSchedulerImplementation.lean)
identify the seed mixture to condition. A fresh independent seed draw after
the refined signal would be an incorrect replacement.

Future perturbation errors are conditional continuation bounds: at every
remaining decision, the probability of an operational perturbation is bounded
by the prescribed rate. For a finite horizon H, a union bound gives H times
that rate under any starting history and fixed tape. Therefore these bounds
also survive the refined posterior. Past bad preparation is different and
requires (5).

## 6. The resulting finite information-refinement argument

The components combine as follows, using the same prescribed profile at
every refined copy of an old site.

* Menus and all old information-based case tests are unchanged.
* At an excluded site, the permanent payoff comparison is pointwise.
* At a publication or flagged binding site, integrate the fixed-tape local
  continuation comparison and add (5) and the uniform future perturbation
  error.
* At a clean binding site, improper responses and WAIT use the fixed-tape
  comparison; proper values use the filtered rectangle (2)–(3), with exactly
  the same source site and uniform source-regret bound.

Thus the required uniform error has the same form as the original one,
with a refined-fibre preparation bound in place of the old one:

    gain_n(F,a) <= R_n
      + C_u * |Players| N b_n/(q a_n^d)
      + C_u * H operationalRate_n
      + sourceError_n.                              (7)

Here C_u is a fixed payoff-range constant; exact existing constants can be
retained when the comparison lemmas are restated. Every term can tend to
zero on one positive common sequence. Finiteness then supplies a common
subsequential limit of strategies and Bayesian beliefs, yielding sequential
rationality of the copied reference strategy in this refined information
model. Its initialized physical law is the same as the old prescribed law,
because the copied strategy ignores the added label.

This establishes the finite information argument from the indexed rectangle,
the repair inequality and the fixed-tape continuation comparisons. The
corresponding refined `InformationModel` and theorem assembly have not been
implemented. More importantly, the result retains the service hypotheses of
those comparisons. It is not yet a proof for an arbitrary new asynchronous
inclusion model.

There is no need to replace the existing protocol or invent a new probability
library. A refined `GameTheory.Protocol.InformationModel` has product
information and the old menu. Use an explicit latent-seed carrier when the
label reads seed flags. Existing
`GameTheory.Protocol.InfoSignals.withOwnPlayRecall` supplies perfect recall
if needed. The new algebra belongs next to the qualified annotation sums;
the posterior repair belongs next to its existing fibre repair.

## 7. What this does and does not solve for replay

Full past operational information resolves two failures of the earlier
coarser reference. It knows whether another actor had a past silent callback,
and whether an empty processing opportunity was enabled. Thus a simulation
of that actor's causal transport knowledge and replay coins no longer needs
to infer these events from a fixed public callback calendar.

Along a fixed refined mechanical prefix, ordinary foreign literal-alias
kernels can again sum to one, provided they affect no fixed class or replay
knowledge. The focal alias record remains causal from its initial own
catalogue, own choices and simulated observations. Actual private reception
can be garbled from the refined past pending/occurrence history.

There is still a controlled-transition requirement. If replay consumes a
service slot and changes when another entry is included, erasing that replay
need not produce the old physical continuation. A richer information signal
does not repair this state-transition mismatch. Either treat retransmission
as an observable notification of an immutable existing admission, leaving
the canonical application/service queue unchanged, or prove the appropriate
incentive comparison for its actual queue effect. The latter is not supplied
by a likelihood calculation.

Similarly, source-query legality at actual binding decisions requires actual
publication of earlier qualifying openings, for example a contract-controlled
cooldown with its proved inclusion bound. Exposing their contents in a
proof-only reference cannot make an actual private strategy legally depend
on an unpublished proposal.

## 8. Bounded inclusion alone does not prove the old timing inequality

Consider one unresolved owned opening. Success before time 10 pays 1;
exclusion pays 0. At an off-path callback at time 8 the player has not sent.
Its next opportunity is time 9. At most one first protocol entry can be sent.
The service includes every qualifying entry within Delta=3, with these times:

| First submission | Inclusion time | Game result |
| --- | --- | --- |
| 8 | 11 | Excluded at 10 |
| 9 | 9 | Success |

This is a bounded inclusion service: 11<=8+3 and 9<=9+3. Nevertheless WAIT at
8 followed by SEND at 9 gains one over SEND at 8. A packet's inclusion bound
does not imply that submitting earlier cannot lead to later inclusion. An
early initial opportunity, for example time 0 with inclusion by 3, can still
guarantee success on the intended path. The counterexample concerns the
late off-path comparison needed for SE, not on-path liveness.

To isolate the information-refinement problem, let a hidden fair service bit
select between the displayed table and its reverse:

| Seed | Send at 8 | Wait, then send at 9 |
| --- | --- | --- |
| 0 | Inclusion 8, payoff 1 | Inclusion 11, payoff 0 |
| 1 | Inclusion 11, payoff 0 | Inclusion 9, payoff 1 |

All four inclusion times satisfy Delta=3. At the coarse site both alternatives
have expectation 1/2, so prescribing SEND is locally optimal. Let an earlier
unused service flag equal the seed. Its actual command was WAIT on an empty
queue in both cases. A reference refinement revealing that elapsed flag makes
WAIT strictly preferable in seed 1. Thus arbitrary SEs do not survive this
information refinement automatically, even though the added signal concerns
only past service.

The example can be completed to a full finite SE. Give the player an initial
opportunity at time 0, with inclusion by time 3 under either seed. Prescribe
SEND at 0; after an off-path initial WAIT, prescribe SEND at 8, and after
another WAIT prescribe SEND at 9. At 0 the payoff one is maximal; at 8 the
two alternatives tie at one half; at 9 sending weakly dominates no send.
Independent positive trembles at the player's opportunities keep the seed
posterior one half at the unrevealing coarse histories, giving a common
consistency sequence. Let the unused signal occur at time 4. Refining the
off-path time-8 information by that signal makes the copied continuation
strictly suboptimal in seed 1, while leaving the original on-path success
unchanged.

Frequent opportunities do not remove the example. Add a callback at every
integer before time 8 and make every first send at those earlier opportunities
succeed under either seed before the deadline, for example by recording it
immediately at its submission time. This satisfies the same three-unit bound.
Prescribe SEND there. The
history reaching time 8 consists of earlier WAIT trembles. Own opportunity
gap one and the same initially generous deadline therefore coexist with the
late-site reversal.

This also obstructs arbitrary copied reference sequences. Let p be the
coarse-measurable SEND probability at time 8 and q its probability at time 9
after waiting. Three refined-site gains are respectively 1-p (SEND at time 8
in seed 0), 1-q (SEND at time 9 in seed 1), and pq (WAIT at time 8 in seed 1).
Therefore the uniform regret is at least

    max(1-p, 1-q, pq) >= (3-sqrt(5))/2 > 0.

Indeed, if this maximum is r, then p,q>=1-r and r>=pq>=(1-r)^2; solving the
quadratic on [0,1] gives the displayed lower bound. With the rational
continuation q=1, the time-8 bound alone is max(1-p,p)>=1/2. Thus no sequence
of coarse-measurable strategies can have uniformly vanishing regret in this
refinement. Revealing all operational prefix information is a sufficient
proof technique only when its conditional timing comparisons can actually
be established; it is not a necessary condition for preservation in the
original private-information game.

This does not refute existence of a source-preserving target SE: an adaptive
off-path policy can choose the better timing. It refutes importing the old
prompt-reference comparison from a mere bounded-inclusion assumption. A new
asynchronous proof must either derive an earlier-send comparison from its
actual service semantics or construct the required off-path operational
strategy jointly with the source continuation.

Finally, if a service signal is allowed to depend on an otherwise hidden
source bit, the stronger information obstruction applies: a source player
choosing a constant best guess can acquire a perfectly informative operational
signal and strictly prefer another guess. A label that exposes foreign
preparation values has the same problem. The rectangle (1), rather than the
word “operational”, is what excludes that illicit source-information gain.

## 9. Successful delivery does not automatically replace the proposal archive

A weaker publication condition might say that every unexcluded owner's correct
opening is public before the next binding. Under this condition, any missing
earlier proposals belong to failed owners. This can be useful, but it is not
the archive equality used by the existing source prescription.

The distinction is explicit in the owning definitions.
`Vegas.SourceProgram.Setup.proposalRecoveryQuery` in
[ProposalRecoveryProjection](../Vegas/Source/ProposalRecoveryProjection.lean)
retains the complete proposal archive as part of the strategy key.
`Vegas.SourceProgram.Setup.proposalRecoveryPublic` and
`Vegas.SourceProgram.Setup.proposalRecoveryProposalOf` in
[ProposalRecoveryObservation](../Vegas/Source/ProposalRecoveryObservation.lean)
record a truthful disclosed value even when its semantic publication is
withheld. The public proposal is a separate component of that recovery
observation. Correspondingly,
`Vegas.EventGraphRuntime.PhaseProposal.sourceArchive` in
[PhaseProposalSourceArchive](../Vegas/Game/PhaseProposalSourceArchive.lean)
extracts submitted typed opening claims without consulting receipt status or
guard acceptance. The native query
`Vegas.phaseProposalQuery?` in
[PhaseProposalQuery](../Vegas/Game/PhaseProposalQuery.lean)
adjoins this archive to the source-control key.

### Filtering successful delivery at one fixed source information set

Fix J and the product density (1). Let x=(g,z), and write d_a(x) for its source
density, whose total mass M is independent of a. Let s(k,x,a) in [0,1] be the
conditional probability of the proposed successful-delivery event, with any
additional service randomness already integrated. Define

    C = sum_k c(k),
    L_a(x) = sum_k c(k) s(k,x,a).

The successful sublaw on x has mass L_a(x)d_a(x). Thus the following exact
criterion is sufficient for one action-independent scalar survival factor:

    L_a(x) = C_s
    for every a and every x with d_a(x)>0,               (5)

where C_s does not depend on a or x. For C>0 and M>0, put q=C_s/C. The normalized
joint source/success law then satisfies

    Pr(success, X=x | J,a) = q d_a(x)/M.                (6)

This follows by substituting (5) and dividing by CM. Conversely, if (6) holds
for the full source outcome X, then (5) follows at every positive-density atom.
Equality only after one chosen payoff projection is weaker and does not prove
this full-law criterion. If C=0 or M=0, the whole annotated branch has zero mass
and no normalization is performed. Zero-density atoms impose no condition; if
C_s=0, success has zero mass and its conditional law need not be defined.

A sufficient producer is s(k,x,a)=s(k): success is a property of mechanics
alone under the coupled annotation. Independence of the initial service seed
from source inputs does not prove this producer. A causal service may later
select delivery using an opening value or other source-dependent wire data.

If, in addition, failure gives the **focal player** the same fixed utility F
under every continuation, then (6) gives the exact payoff identity

    V_native(J,a) = F + q (V_source(J,a)-F).             (7)

For fixed timing, q must be the same for every compared semantic action.
Then each local semantic gain is q times its source counterpart. More generally,
one can allow a failure utility measurable in the pre-action source history g,
whose marginal is the same under every a, when the joint source/failure law has
the same product factor. Merely writing F(g,z) without an action argument would
not suffice: the completed-block variable z can itself have an action-dependent
law. An action-dependent success probability does not give
the same gain identity: it multiplies the different nonnegative payoff
increments by different coefficients.

Crucially, the none branch in (3) is a bookkeeping value of the qualified
payoff law. It is not an assertion that every unqualified history gives the
actual player F. That replacement needs a separate payoff lemma. In the
individual-exclusion runtime, a foreign owner's failure fixes that owner's
utility, not the surviving focal player's utility.

### Merging source information sets is a different operation

Let A be the missing failed-owner archive and let J_A denote the full source
information. Actual information K may merge several J_A values. Applying (5)
separately at each J_A leaves a mixture over those source information sets. It
does not make them the same J, and it does not make their prescribed actions
equal.

For example, if pi(A|K) are the pre-action mixture weights, all compared action
menus agree, and failure gives the focal player F, the exact expression is

    V(K,a) = sum_A pi(A|K) [F+q_A(V(J_A,a)-F)].         (8)

If the source prescribed law sigma_A differs with A, the formal baseline

    sum_A pi(A|K) [F+q_A V(J_A,sigma_A)-q_A F]

uses information unavailable at K. Averaging the sigma_A laws does not repair
this: the averaged choice is independent of the actual hidden A, while the
displayed baseline correlates its choice with A. To copy the construction,
one needs a single legal prescribed law at K (at every perturbation index),
with the required continuation law and local comparison. Alternatively one
must construct a different actual-information continuation after failure.

Here is a precise information boundary. A failed owner has a bit theta, and a
surviving owner's private bit equals theta under the initial correlated prior.
A third player must commit a guess before that survivor reveals its bit, and
receives one exactly for a correct guess. Suppose the failed owner attempted
to disclose theta, but its opening was not published. The full proposal archive
reveals theta; the weaker ledger-only archive need not. At the two full source
sites the unique optimal guesses are respectively zero and one. With a fair
prior and no other signal, any common guess-one probability p has gains p at
the theta=0 fine site and 1-p at the theta=1 fine site. Its maximum fine-site
regret is at least one half. Independent, source-blind delivery failure does
not remove this obstruction: the missing observation itself distinguishes the
source information sets.

This example concerns copying the archive-based recovery continuation. It is
not a counterexample to preservation of the original on-path source SE. The
failure branch can be off path, and a different joint continuation on the
actual private information may be sequentially rational. What fails is the
claim that successful publication of all survivors, plus the failed sender's
own payoff floor, already proves the old archive-based source comparison.

### A different recovery extension can avoid copying those source sites

The [first-quitter extension](se-quit-handler-preservation.md) supplies an exact
source-level alternative. Preserve the intended game on all no-failure
histories. After a first publicly identified permanent exit, retain survivors'
actual private observations and complete the resulting finite continuation
jointly. If the first exiting player's utility is capped below every intended
continuation, the extension preserves every selected intended-game SE.
Survivors need not know the failed owner's proposal and need not receive that
owner's floor. Their handler beliefs come from the same full-game consistency
sequence, rather than from the archive-based prescription being copied.

This changes the auxiliary recovery construction, not the intended successful
game. The actual failure settlement must still satisfy the stated cap. At
native binding sites before the first exclusion, success-or-exit implies that
all previously resolved owners' correct values are already public. This is
precisely where an archive-free intended-game comparison is most plausible.
After that public boundary, source-query equality can be replaced by rational
completion on the actual information, if the remaining extension conditions
are established.

The missing connection is the interval before the public boundary. A late
opening is not itself a Quit: it can succeed, fail, reveal data privately, or
interact with another owner's failure. To realize a source-level Quit
comparison, a unilateral native deviation must either have a legal intended
continuation or enter a failure branch that actually caps that deviator's
utility. A foreign exit generally gives a different survivor continuation.
Its probability, entry information and payoff cannot be discarded. New private
observations before the marker also cannot simply be relabelled as observations
of an already-entered handler.

The [scalar timing theorem](se-asynchronous-timing-policy.md) proves one precise
bridge when those branches are genuinely the source continuation on success
and the acting player's own floor on failure, with the required conditional
source/service separation and a legal optimal timing policy. It does not supply
that decomposition for concurrent rollback with possible foreign failure.
Thus a different private-information failure extension removes the need to copy
the old post-exit archive prescription; it leaves a specific pre-exit timing,
information and attribution comparison to prove.
