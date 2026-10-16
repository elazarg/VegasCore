# Concurrent SE preservation: mathematical audit

This note works with the theorem and runtime semantics of
`docs/se-preservation-commit-reveal.md`. It records mathematical arguments,
not claims of Lean verification. No runtime or target assumption is changed.

**Math draft: source/reset construction specified; Lemma T repaired; full Lean theorem open.**

The source strategy is selected with the erasure and failed-attempt pins
constructed below. This is not a claim about an arbitrary source extension
or an arbitrary completion of the current native policy family.

## The object at a commitment information set

Fix a native information set I of j and its original commitment attempt a.
Freeze the owners active at the beginning of a. Let A be these owners other
than j. A failure of an owner in A still counts after that failure excludes
it. Extend the original attempt to its first full attempt-identifier exit,
before any decisions in a retry. Read the completed original attempt from its
archive if settlement restores the saved state, including exhausted restore
with unchanged generation. Otherwise read its successful completed image.

Phi means that every binding belonging to an owner in A succeeds in this
original attempt. It does not mean success of a later retry. An already
observed failure of an owner in A makes Phi impossible.

The transported object is the joint private trajectory of the owners in A,
including their earlier choices and their later choices in this attempt.
Repeated choices of one owner remain one trajectory. No independence between
that owner's private choices is asserted.

## Charged histories can be removed inside rare Phi

Here is a direct finite-game argument; it does not condition an already
proved pre-I total-variation estimate.

Let H bound the number of extended histories and let T bound their length.
Absorb all positive fixed chance and builder atoms into a constant b>0. Such
a constant exists because the actual extended game is finite and its chance
laws are fixed, including its original setup law. It is not an information
mass floor and does not bound a perturbed behavioral probability.

At a fixed stage n, write rho_n for the minimum positive source action atom,
zeta_n for the native perturbation scale, and M for the charged-action
exponent. For sufficiently large n, each uncharged prescribed local atom has
the lower bound

    d_n = c (zeta_n^3 rho_n),

for some constant c>0 independent of n. This accommodates a late timing
tremble and a slot tremble, as well as native-only bindings. The uniform
failure rates tend to zero over the finite collection of public regions.

Perfect recall fixes every past behavioral factor of j throughout I.
Let q_n(I) be their product. For any specified extended history reaching I,
its probability is q_n(I) times the product of the remaining behavioral and
fixed chance factors. Full mixing makes q_n(I)>0. Future choices of j are
not included in q_n(I).

Assume Phi is possible in the document's precise sense: there is a clean
history in I with a positive uncharged continuation satisfying Phi. Fix one
such extended history g. Its support is independent of n. Consequently

    Pr_n(g) >= q_n(I) b d_n^T.

At a forced or lifted set, a charge already determined by j's recalled own
actions cannot occur: otherwise there would be no clean history in I.
Every charged extended history therefore has a charged action factor outside
the fixed past factors q_n(I), possibly a future action of j. Its probability
is at most C q_n(I) zeta_n^M, with C independent of n. Summing gives

    Pr_n(charged and I and Phi) / Pr_n(clean and I and Phi)
      <= (H C / b) zeta_n^M / d_n^T -> 0.

The last limit is exactly the charged-tier separation imposed in the
construction. No lower bound on Pr_n(Phi | I) is used. Restricting the
numerator to Phi can only lower it; the denominator uses an actual clean
Phi history rather than an unrestricted repair image.

If clean Phi is impossible, every I-and-Phi extended history is charged.
One must then use the unconditioned charged-history bound at I to conclude
Pr_n(Phi | I)->0. A conditional transport claim is neither made nor needed
there. Unrestricted positive stage-n Phi mass is not clean possibility.

This argument requires that charge status relevant before I be determined
by the focal player's own information, as used by the document's one-shot
charge argument. It must be checked against the authentic audit, rather than
identified with a random later collection outcome.

## A normalized uncharged reference law

Deleting charged paths does NOT leave a normalized continuation kernel.
In particular, summing a focal future only over those paths need not give
one. Use an explicitly constructed reference profile Q_n instead.

At a full own-information set J, firstness, authorization, preparation and
own certificate data determine the uncharged action set U(J). It is nonempty:
silence is always available. Specify a normalized Q_n(J), supported on U(J),
using the local timing, source-value, slot and native-only tiers. Choose each
total tier before distributing its mass over available packets; a foreign
menu's cardinality must not determine the local send probability. On every
clean-information fiber define the actual fully mixed prescription by

    P_n(. | J) = (1-chi_n(J)) Q_n(. | J) + chi_n(J) C_n(. | J),
    0 <= chi_n(J) <= C zeta_n^M,

where C_n is supported on the charged complement. If that complement is
empty, set chi_n(J)=0. Leave the actual free-agent profile unchanged on
charged-only fibers. Every Q_n-reachable prefix is clean, so none of those
fibers is reached by Q_n. Define Q_n arbitrarily on its unreachable fibers.

For each clean complete extended history h, the fixed original chance laws
and identical uncharged atoms give the exact identity

    P_n(h) / Q_n(h) = product_{J visited in h} (1-chi_n(J)).

The ratio is uniformly 1+O(T zeta_n^M). The same relative comparison holds
after restricting to ANY event of positive Q_n mass, including I-and-Phi;
normalization preserves a vanishing error without dividing by its mass.
Combining this comparison with the preceding charged/clean ratio transfers
the actual I-and-Phi conditional law to the normalized Q_n conditional law.
Exact focal-future summation below is performed in Q_n, whose behavioral
kernels sum to one, rather than in P_n conditioned on remaining clean.

This specifies a witness. An arbitrary existing whole-menu-uniform profile
need not have the required local normalized uncharged part; its mere
decomposition into charged and uncharged atoms is insufficient.

## Native-only bad bindings require a different comparison

The preceding absolute lower bound does not by itself remove the zeta_n^3
native-only tier: it would lose too many powers of zeta_n. This part needs a
comparison that preserves operational factors inside Phi.

For a still-active foreign owner k, replace its unopenable or wrongly typed
bindings by the SAME ordinary typed values already used by its prescribed
virtual source history. Keep the original signed binding envelopes, their
identifiers, slots and emission times. Keep every other owner's actions and
every fixed chance and builder realization.

Include old bindings voided by earlier retries, not just currently held bad
bindings. Since k is still active, none was revealed unsuccessfully: it is
still unopened or was voided before it could be opened. Stop at the original
current attempt's end. The replaced material is never opened on this path.

The comparison must establish all of the following from the construction:

1. k's virtual source history after replacement is exactly the history used
   by its native prescription, including its previous ordinary violations.
   Being regular here does not mean that every ordinary source guard holds.
2. The replacement has the same focal full information I. Opaque binding
   packets reveal no replacement value, and previously published results
   remain fixed.
3. All local activation, emission and resolution words remain the same.
   In particular Phi is unchanged. This uses actual own-service policies,
   not a timing policy allowed to read foreign traffic or private values.
4. The counterpart has positive probability under the same original source
   and builder laws. No initial input or private seed is redrawn.

These four facts follow for the explicit virtual-history prescription as
follows. Replace a bad declaration's prepared meaning, not its fresh handle
or emitted envelope. By definition the ordinary replacement appends the same
virtual action that the bad declaration appended. Inductively the owner's
later virtual source views are identical. No ordinary guard violation needs
to be repaired: it is an allowed source action. Opaqueness preserves every
foreign observation. Deferred guard checks involving the replaced material
have either not executed or were discarded by the unchanged reset. Actual
own-service keeps the same local words and inclusion/miss outcomes. Thus the
entire original operational history, including earlier retries and current
Phi, is preserved. Freshness is unchanged because the same slot was first
prepared at the same callback.

Under these facts, the native-only atom zeta_n^3 is compared with a
source/slot atom of at least c zeta_n^2 rho_n. The other operational factors
cancel or have a uniformly bounded ratio. If a bad owner is forced to send
on time, its WAIT atom zeta_n is no greater than the counterpart's
alpha_n+zeta_n; its SEND ratio is at most 1/(1-alpha_n-zeta_n)<=2 eventually.
At most T callbacks absorb this constant.

If the original pure-policy coordinate at this query was unused by the raw
declaration, integrate it under the SAME original prior. The counterpart
requires it to equal the virtual representative, costing at most 1/rho_n.
This is not a pathwise claim fixing an arbitrary unused policy coordinate,
and does not replace the prior at a later entry. Distinct full occurrences
(or the antichain of reduced source pools below) ensure that this coordinate
was not queried elsewhere on this path. At most T source factors change.
Finite multiplicity then gives

    bad_mass(I,Phi) <= C' zeta_n rho_n^(-T) regular_mass(I,Phi).

The prescribed separation zeta_n=o(rho_n^T) proves the required negligibility.
This is the comparison that must be proved. A pre-I RAW mass estimate, or a
repair map whose image is not shown to retain Phi, cannot replace it.

One may use the stronger regular subset excluding all old and current bad
emissions of owners active at I. This also removes obsolete bad-value factors
from the active private trajectory in the factorization below. Bad material
of an excluded owner is not repaired and stays in its operational weight.

The directly specified local-tier witness needs only this bad-binding
restriction. A whole-menu RAW implementation can also produce an ordinary
typed SEND from its RAW tier. If its retained submeasure deletes that origin,
it requires an ADDITIONAL comparison: keep the same typed value and fresh
slot and replace its RAW origin by the source/slot tier. The same
zeta_n^3/(c zeta_n^2 rho_n) bound applies, with the same finite-multiplicity
argument. Bad-only deletion is not a proof about that larger submeasure.

## Local service independence and the permitted packet quotient

Use the exhaustive inputs of the document's concurrent S1. For a binding,
content enters success only through well-formedness; for a reveal the
opening/guard outcome also matters. Consequently replacing an authorized
fresh first binding handle or its transport nonce, at the same emission
clock, preserves success for each fixed event seed. A merely value-blind
functional allowed to read the entire envelope does NOT imply this fact.
The earlier Stage-S statement allowing late-slot preferences is broader.

Work in Q_n. Predraw the original foreign event seeds, source-policy
randomness and local timing randomness. Consider two continuations differing
only in the focal future. Before a foreign event's first SEND, its seed fixes
its local activation calendar under S1. Its source query reads the old
entry's public data and its owner's preceding source choices. Its local timing rule thus
gives the same first SEND clock, or the same decision never to send. S1 and
the packet quotient then give the same success bit. Exact inclusion times
need not agree. Induct in a topological order of the phase graph, retaining
each owner's order. A cross-owner predecessor can change the absolute
readiness clock, but S1 uses clocks relative to readiness and the original
seed for that occurrence. A failed predecessor still completes; the phase
completion contract readies its successors. Commitment opacity and source
play ignoring in-phase observations preserve the induction.

Survivors keep these laws after a focal expiry while the old attempt remains
open. Reset waits for the entire old attempt to finish. The completion
contract ensures the finite runner cannot cut an unresolved event off and
call that its result. Hence both Phi and the joint foreign old-attempt
trajectory are functions of the non-focal original randomness alone.

The induction must establish one more independence before any bad-path
restriction. Let B flag ANY old or current native-only bad emission of a
foreign owner still active at I. Predraw each local tier label before its
packet encoder: ordinary labels use the source draw; bad labels append the
fixed virtual representative. Their total probabilities and local timing
read no foreign menus. Conditional slot/bad encoders have total mass one,
and S1 erases their handle choices from success. A bad flag can change its
owner's later prescription, but that change depends only on its own labels
and virtual history. Thus the JOINT variable (foreign virtual trajectory,
Phi, B) is independent of the focal future under Q_n. This stronger
statement is necessary: Phi independence alone would not justify deleting
bad paths and then summing the focal continuation to one.

The measure order is consequently as follows. Transfer P_n(.|I,Phi) to
Q_n(.|I,Phi) by the charged bound and the clean-path density comparison.
Apply the same-prior bad-binding repair under Q_n to obtain

    Q_n(B != 0, I, Phi) <= r_n Q_n(B = 0, I, Phi),   r_n -> 0.

Restricting to B=0 then costs at most r_n/(1+r_n) in total variation.
Because B and Phi are non-focal variables, the NORMALIZED focal Q_n
continuation sums to one for each fixed remaining realization with B=0
and Phi. No restriction is imposed on the focal owner's own bad bindings.
Only at this point apply the regular source factorization below.

At an unsent focal site, let L be its OBSERVABLE event-local transcript:
relative clock, its activations, own emissions and survival. Absence of an
activation up to the observed clock constrains the calendar. No assumption
that internal polling replies are observable is needed. Let Z be all
original randomness except its event seed xi. S2 gives the prior
mu(dxi) nu(dZ). By S3 the information
event has the form

    {xi agrees with L} x R_I.

Indeed, fixing L fixes every way the event seed may enter the outside run;
all remaining observation and focal action constraints are constraints on Z.
Bayes therefore gives mu(. | agrees with L) times nu(. | R_I). This is the
original filtered seed law, not its unconditioned prior and not a refreshed
entry distribution. Finite local backward induction gives an optimal rule
at every remaining local record. Its action space is complete because of
the packet quotient; a protected first SEND has success one.

The existing arbitrary addressed-controller interface does not itself imply
this strong S1. It can inspect transport identifiers and can make later
activations depend on emissions. Independent original seed coordinates and
deadline expiry are insufficient substitutes. This is an interface mismatch
to resolve when implementing the mathematical theorem, not a proved
counterexample to the theorem with S1.

## Conditional factorization once these comparisons hold

Fix the public source record UP TO I and the focal source history projected
from I, not a future focal failure record. Use the source prescription
constructed below: through the old attempt foreign value kernels keep their
no-new-miss queries and their failure rates are fixed in advance. They
therefore do not acquire a dependence on a future focal failure before that
failure is summed out. Owner-locality alone would not remove this mixture.
The summation uses the normalized Q_n focal continuation, not a restriction
of the actual continuation to uncharged paths.
Each other owner's entire private trajectory has its own consistency
constraints: its published results, its private decisions, and the success
requirements in Phi. The source program's public samples contribute their
fixed kernels evaluated on the same public record. The source laws and
independent private inputs therefore factor over complete owner trajectories;
there is no factorization over successive private cells of one owner.

Group the other active owners into o and excluded owners into e. Compatibility
with the fixed public record, focal source information and Phi is an
owner-by-owner condition. It therefore defines a product domain O x E and
the source weight A_n(o) B_n(e). Hidden choices of a repeated owner are kept
together. Initial private-input support is the original product support,
not an independently reassembled collection of fields from posterior entries.

Owner-private initial atoms may be unequal under a substitution. Put their
ORIGINAL densities into A_n(o) and B_n(e) first. Only the remaining public
chance and builder/service factors are unchanged; product support does not
mean equal private input probabilities.

Here is the physical domain argument. For fixed e, take an actual regular
realization for one compatible o. Erase active hidden meanings from its
live, saved AND archived states, from the preparation catalogue and from
derived private views. Retain event/attempt occurrences, signed envelope
headers, handles, clocks, commands, public results, focal data and all
excluded-owner data. Call the resulting operational template omega.

For any other source-compatible o', insert its COMPLETE original supported
private tuples and typed choices into the SAME occurrences and handle slots.
Induct through the original physical operations:

- Activation, clock and leaks have the same operational observations and
  S1--S3 local responses. Binding opacity hides the substituted meanings.
- WAIT preserves the paired states and the same local timing factor.
- Binding SEND prepares its selected typed value at the same fresh handle;
  ownership, readiness, token and empty evidence are unchanged.
- Binding inclusion takes the same branch: admission reads these conditions,
  while guards are deferred. The same event completes at the same cut.
- Missing/expiry reads the same clocks and local success decisions, so the
  same completion and exclusion flags are recorded.
- An earlier active opening has its value and successful guard verdict fixed
  by the public source record. Compatibility of o' enforces that verdict.
  Excluded-owner opening content is part of the fixed e/template. No changed
  active private binding is opened during the current commitment phase.
- Sampling uses the same public-data kernel and supported public draw.
- Normalization sees the same flags and exclusions. It advances, retries or
  exhausts in the same branch, restoring corresponding saved tuples and
  discarding exactly the same current bindings.
- The final count audit reads the same firstness, authorization and envelopes.

Thus the completed old attempt, the first-exit predicate, Phi and focal I
are retained. Full mixing and the same-slot source tier give positive
behavioral support. Source-compatible initial tuples retain positive
original input support. Inserting o back is the inverse. Hence the template
set Omega(e) is independent of o. It may be empty; K_n(e)=0 is allowed.

Chronological content is read from this SAME template, not from restored
post-reset choices. For every counted surviving event, clean packet
uniqueness gives one SEND and inclusion gives its immutable typed result.
Conversely every such completed binding has that originating SEND. Same-owner
order puts the occurrences in their source order, preserving repeated-owner
multiplicity. Whole completed images supply previously pending SENDs. Saved
prefixes give earlier successful phases; failed attempts use their literal
archives, including exhaustion with unchanged generation.

Construct the source path by a canonical weave, starting at the original
setup draw. Process the source instructions in program order within each
physical phase. Use the SAME archived completed image for every failed
attempt. Mark each actual miss at its canonical source rank; append the
actual supported reveal and public-sample transitions; perform the source
close/restore for the same failure vector. This constructs a genuine source
history, not just a reachable endpoint or a chosen checkpoint equality.

At each occurrence, fill the canonical source predecessor with these typed
choices. A source observation reads only public results and its owner's
private predecessors, so concurrent foreign holes do not affect this read.
Earlier public reveal results are scanned in source order. The recorded
missing-owner flags likewise reconstruct each old source exclusion scan.
In the present Phi-restricted phase, the active foreign slots are all moves.
If a sequential source exposes a focal miss earlier than the native
interleaving, the failed-attempt pins below identify the relevant VALUE
KERNELS, not the information states. After an old reset, erased-word sharing
does the corresponding identification. These specified kernel equalities
are why the inserted history has precisely the selected source likelihood.

The remaining operational likelihood may depend on e, through an excluded
owner's failed opening, but must be independent of o after summing over all
compatible local service transcripts. In the current commitment attempt,
Phi fixes every counted foreign binding to be a move. Its successful packet
law is value blind; its timing and slot tiers do not read the chosen value.
Earlier successful openings are fixed public values at I. Averaging the
once-sampled complete source policy over the distinct chronological queries
therefore supplies precisely its source action factors. Keep every physical
nonsend factor. Source reveal-TRUE factors omitted by canonical native
openings give a finite product tending uniformly to one on active clean
paths; excluded-owner corrections stay in K_n(e). Binding-WAIT RAW residues
likewise give a uniformly near-one product; opening RAW WAIT has exact
whole-menu symmetry. For the document's directly specified local timing
tiers this locality is direct; a whole-menu RAW implementation needs these
relative comparisons, not an assertion of exact own-service.

Summing over the COMMON domain Omega(e) gives K_n(e), independent of o,
with a uniform relative error tending to zero. No nonsend term or original
entry posterior has been deleted or refreshed. A full pure-policy predraw
must be indexed by genuine recovery occurrences, or the reduced-source
antichain below. An ordinary source table that aliases distinct retries
does not supply this identity merely by being called the same source prior.

If the regular native o-weight is

    A_n(o) C_n (1 + epsilon_n(o)),
    C_n = sum_e B_n(e) K_n(e) > 0,
    sup_o |epsilon_n(o)| -> 0,

normalization removes C_n even if C_n tends to zero. The normalized regular
law and the normalized source o-law have vanishing total variation. Transfer
back through the bad-path, reference-law and charged-path comparisons to
obtain Lemma T without an information-mass or Phi-mass floor.

Explicitly, set a_n=(1-C zeta_n^M)^T -> 1. Let c_n bound the charged/clean
P_n mass ratio inside I-and-Phi, let b_n bound the bad/regular Q_n ratio
there, and let |epsilon_n(o)|<=epsilon_n<1. The L1 error between the actual
conditional active law and the source law is at most

    2 c_n/(1+c_n) + 2(1-a_n)/a_n
      + 2 b_n/(1+b_n) + 2 epsilon_n/(1-epsilon_n) -> 0.

The first and third terms bound mixture remainders. The second uses the
uniform clean-path density ratio, including normalization on I-and-Phi.
The fourth subtracts the source-weighted mean of epsilon. None divides by
the unnormalized mass of I or Phi. If a larger RAW-origin submeasure is
used, add its same-value-repair remainder as well.

The o-law includes the complete typed private trajectories of the other
active owners, including their old voided typed choices. It is not merely
a law of current live cells. The excluded e-law may remain tilted by K_n(e).
Canonical weaving and equality of selected query kernels prove neither
equality of full virtual/actual information states nor equality with a
factory's particular chosen source trace. Those stronger claims are not
needed for the active posterior and incentive comparison.

## Constructing source play that ignores voided private choices

Past-blindness with respect to timing does not imply indifference to a
remembered voided value. An arbitrary source SE may use such values as
private mixing seeds after a reset. Therefore choose the source extension
with an explicit additional strategy property, while keeping its full
information sets and perfect recall unchanged.

At a source information set retain the entire genuine public history,
the full event/attempt occurrence, and the owner's restored semantic view.
Erase voided own choices from EVERY derived private signal and own-play
entry. Do not erase a value still present in the restored context, a public
sample, a public exclusion, or a public result. Call the result the reduced
information. Prescribed conditional value distributions are shared over
full information sets with the same reduced information.

Fix positive failure trembles alpha_n independently of private values before
optimizing these distributions. They tend to zero. In particular, omission
does not signal whether an owner is privately doomed. Conditional value
polytopes have full-support lower bounds preserved by the erasure.

These rates must also preserve the GIVEN honest assessment, including its
beliefs at rare honest information sets. Let rho^H_n be the minimum positive
atom of its fixed consistency sequence and the original chance laws. Choose
the failure rates and the additional violating-value/free-agent floors
before the pooled fixed point, sufficiently small that their total one-step
mass theta_n satisfies

    theta_n = o((rho^H_n)^T).

This stronger sufficient choice implies Proposition 1's source separation.
At an honest-compatible set, cancel the focal remembered action likelihood.
A fixed honest witness then has remaining mass at least b(rho^H_n)^T;
the first foreign failure or violation has mass at most C theta_n. A finite
sum makes their conditional mass vanish. On histories without either event,
the copied honest likelihood differs only by a uniformly 1+o(1) product.
Thus the copied honest beliefs are retained. Merely requiring positive
floors tending to zero would not suffice; the later native zeta hierarchy
cannot repair an incorrect source belief limit.

To justify sharing, fix a public history p and a player's restored private
information t. Expand the reach likelihood under an arbitrary profile of
shared value distributions. By the owner-trajectory factorization, adding a
specified voided own word w multiplies every compatible opponent world by
the SAME own-trajectory likelihood L_j(w;t,p). The word is unrevealed and
its guard obligations were discarded. All public failure factors are fixed
by p. Thus, whenever the information has positive probability, normalizing
cancels L_j. The conditional distribution of opponents' retained states,
private words and future decision rules is independent of w.

Future legal menus and payoffs also ignore w. The same erasure transports
the player's future policies between the full information sets. For shared
opponent continuations, every member of a reduced-information pool therefore
has the SAME conditional payoff vector over current nonmissing actions.
This is individual equality of rankings, not an assertion about a sum of
possibly conflicting member gains. A pool is not visited twice along one
source path: its key retains the full occurrence; retry changes the attempt,
and ordinary progress changes the source event.

Take an equilibrium of this finite perturbed pooled-agent game. Its compact
convex value simplices and continuous finite-game payoffs give the usual
fixed point. Affinity in a pool's own distribution follows from the
antichain property. The identical-ranking calculation makes its best
response a best response at EACH constituent full information set. Copied
honest agents and the privately doomed agents are pinned as in Proposition 1.
Honest histories contain no voided word, so this sharing does not restrict
the requested honest SE.

The limit-optimality of failure and opening is separate. At a non-doomed
set, a guard-accepted move followed by optimal nonmissing continuations has
value at least m_j-o(1), by backward induction on the remaining own choices.
The fixed failure and mandatory-value trembles contribute a vanishing
finite-horizon error. Immediate failure gives a_j<m_j. At a doomed set,
moving either leaves payoff a_j or permits rescue by another owner's reset;
it cannot do worse than a_j. Opening correctly weakly dominates withholding.
Together with the individual value optimality above, the limit assessment
is a full-information source SE, not merely an equilibrium of a quotient
whose members cannot deviate individually.

There is a second, separate constraint inside a failed commitment attempt. The
mathematical source of the document hides in-phase foreign failures. A
sequential source implementation may already expose them. A survivor whose
old attempt is certain to reset has only payoff-irrelevant current value
choices: all are voided before any reveal, and the reduced reset state is
the same. Such value choices may be pinned to the no-new-miss source
prescription until that original attempt closes. The failure tremble used
by that prescription must likewise remain independent of the newly observed
foreign failure; choosing the failure tremble globally or by the OLD entry
control permits this. Specify the no-new-miss representative and its shared
value distribution before taking the fixed point. Its known-failed members
have EXACTLY constant conditional-value payoff once future play erases the
voided word; its no-miss member can have nonconstant rankings. These are
zero-gain pins, not the identical-ranking pools of retired-word copies.
They impose no competing best-response requirement on the known-failed
members. This is a property of the chosen strategy, not equality of the
full source information states or a change to runtime observations.

Specify that representative as a map F, not an informal edit to the current
exclusion set. Canonically weave the ENTIRE current-attempt personal signal
and own-play timeline with no new foreign misses, retaining the original
entry, the current occurrence and the owner's complete typed prefix. Rebuild
the information tags on earlier own actions as well. There is no public
sample or reveal inside a commitment block, and foreign values are opaque,
so the resulting personal information is independent of the compatible
foreign filler values. F is idempotent. It commutes with erasing PREVIOUS
retired words, which occupy disjoint attempt segments. These facts make the
combined sharing constraints coherent and preserve the occurrence key;
they do not identify two ordinary members with different retained histories.

More explicitly, form these shared classes BEFORE taking the fixed point.
For a final class K, let R_K be its ordinary retired-word variants and F_K
its known-failed attachments. Its owner, event and attempt are fixed, so it
is still an antichain. For any admissible opponents and future profile, its
payoff as a function of the shared value distribution x has the form

    U_K(x) = c + sum_{I in R_K} r_I (x . V_K)
               + sum_{I in F_K} r_I c_I.

Here r_I>0 is the reach probability, independent of x. Ancillary-word
cancellation gives the SAME conditional vector V_K at each ordinary member;
the failed-member c_I is exactly action-independent. Thus maximizing U_K
maximizes each ordinary member's conditional payoff, while failed members
impose no competing ranking. This calculation holds for every admissible
future profile; it does not assume future optimality to obtain the fixed
point. This maximization applies to free classes; copied honest and doomed
classes keep their specified pins and use the separate limit arguments.
Empty R_K classes have only indifferent members.

For a free conditional-value source agent, the common reset term also gives
the phase-success comparison. Differences between its nonmissing values are
Pr_n(Phi | I) times their conditional successful-phase value differences,
with an additional common positive own-survival factor if the owner has
later bindings in the same phase. Fixed failure trembles make that factor
value-independent; all of the owner's failure branches pay a_j.
If the multiplier is positive, its exact constrained best response ranks
these values by the latter differences, even if the multiplier tends to
zero. The forced honest agents use honest conditional optimality in the
limit; at doomed agents the successful-phase payoff is the same for all
current values. Known-failed pins have a zero multiplier.

## Reset value and timing value

Couple the original inputs, public chance, other event seeds and one original
reduced-information source plan per owner. Compare two different values v
of j in the same original commitment attempt. Other owners' source choices
and own-service outcomes ignore v. The binding service also ignores v.

If j fails, its payoff is a_j. If another owner fails while j survives,
read the whole failed attempt before restore. Every new binding of this
attempt is erased. At retry the two runs have the same restored semantic
state and retained public failure history. An exhausted restore has no
surviving phase owner, so it belongs to j's payoff-a_j branch; it still uses
the old archive for the measured trajectory and Phi.
All changed private memories are precisely voided words, which the chosen
source strategy ignores. Future source choices can therefore be coupled
identically in the limit/reference profile. Later prescribed native events
send at their protected first callback, so operational timing and old
catalogue differences do not change
these semantic outcomes. The reset payoff is one common function R(Z).
No claim about an arbitrary selected memory-dependent source SE suffices.

This is not exact pathwise equality for arbitrary fully mixed finite-stage
native continuations: a later charged action may enter a free information
fiber. Their contribution must be removed before applying the coupling.
Inside rare Phi use the relative comparisons above; beyond the already
measured phase boundary, future errors have a uniform finite-horizon bound
because Phi imposes no further condition on those future draws.

For a FIXED v, compare delivery policies s. On j's success, the same coupling
gives a common payoff G_v(Z), independent of its send time. This is different
from comparing different v on a successful phase, where values do matter.
With the original focal event seed xi independent of Z after its recovered
local transcript is fixed, write pi_s(Z) for its remaining success chance.
Then

    payoff(s) = a_j + E[(G_v(Z)-a_j) pi_s(Z)].

For a general information-dependent policy, fix Z. Its extra observations
are then determined by Z and its own local transcript. It is a permissible
local policy with success probability at most P*, the optimal local value
under the same filtered seed law. Clean terminal payoffs give G_v(Z)>=a_j:
j is either excluded with payoff a_j or survives with payoff at least m_j.
This lower bound uses no source best-response or delivery-optimality claim.
Consequently,

    payoff(s) <= a_j + P* E[G_v(Z)-a_j].

An optimal own-service rule attains equality. This proves the richer-policy
bound without asserting that a general policy's payoff depends only on its
unconditional success probability. The local action space must include all
permitted uncharged delivery choices; a SEND/WAIT optimizer alone does not
cover slot-dependent service unless the service law erases those slots.

The fixed-v inequality alone does not cover an arbitrary policy that also
chooses its value adaptively after waiting. Close that issue with one-shot
deviations at EVERY full information set. At an unsent binding set I, let
tau be the prescribed value law at its full-occurrence source query and put

    W_v = E[G_v(Z)],       W_tau = sum_v tau(v) W_v.

Conditional source value optimality, transport and the common reset term
give W_v<=W_tau in the limiting comparison. The vanishing finite-stage
errors have already been controlled relatively inside Phi. For copied
honest approximants an error delta_n->0 suffices: multiplication by a
success probability at most one preserves that error, without division by
Pr_n(Phi|I). For an immediate uncharged SEND(v,slot), S1 makes its success
probability p_now independent
of v and Z. Since p_now<=P* and W_tau>=a_j,

    a_j + p_now (W_v-a_j) <= a_j + P* (W_tau-a_j).

No pointwise comparison between different values' G_v is asserted. WAIT
now followed by the prescription uses the SAME source query at its eventual
SEND. No own source event occurs while it remains unsent, no reveal or
sample can cross the phase barrier, and the old-entry pins remove new
in-phase exclusion dependence. Its value can be predrawn once with law tau:
intervening WAIT atoms are value-independent and the projected query ignores
these clocks. The
same mixed value law consequently has common success payoff W_tau, and its
local timing rule has success probability at most P*. The prescribed
optimal timing rule attains the upper bound. These two cases exhaust
uncharged one-shot choices at an ordinary unsent binding set. Proving them
at every later full information set, then using perfect recall, rules out
adaptive multi-step value/timing deviations as well. Own bad material and
charged actions use their separate pointwise arguments below.

## Order of the native rationality argument

Use saved entry exclusions, not the current exclusion set, for induction.
For N source instructions and m players, a suitable boundary measure is

    (m - |E_entry|) (N+1) + remaining(saved_source_point).

A retry increases saved exclusions and strictly lowers the first term; a
successful advance lowers the remaining source rank. Exhausted restore
also advances, and is measured using its original archived attempt. Inside
one fixed attempt use the finite local service decision problem with the
already-established boundary continuation values.

Construct source play first, then local service optima, then the native
profiles pinned on both forced AND lifted clean-information fibers. Only
charged-only fibers are left to the perturbed free-agent equilibrium. The
pins need not be best responses at finite n. Prove their limit rationality
by the boundary induction, conditional transport, the common reset/timing
payoffs above, and the deposit bound for charged one-shot deviations.

Exact focal-future independence applies on the uncharged reference law.
Charged focal continuations can move another owner into a charged-only
information set where its prescription is free. Use the Phi-relative charged
bound and the uniform clean-path density ratio to transfer to Q_n before
applying independence. Do not identify Q_n with the actual law conditioned
on no future charge, or claim exact independence of every fully mixed
finite-stage continuation.

## Sequential rationality, consistency and the preserved law

The preceding comparisons apply at each forced or lifted commitment fiber
with clean Phi possibility. Their relative errors vanish even if that event
has vanishing probability. Source conditional value optimality then ranks
the honest/ordinary value deviations. A different own-service timing rule
cannot improve the common-success payoff; the richer-information inequality
also rules out choosing timing based on leaks or other receipts. A protected
first SEND has success one. If clean Phi is impossible, its limiting mass
is zero; the common reset payoff, not this probability fact alone, makes
ordinary value choices indifferent.

For an own bad binding, a standing value leads to payoff a_j regardless of
its delivery. If a co-phase failure can void it, successful own delivery can
instead permit the common reset continuation, worth at least a_j. The same
local success maximization is weakly optimal. A correctly certified opening
is uncharged; if none exists, silence is the available uncharged response.
Other inactive or already-sent clean sites likewise prescribe silence.

At any clean-information site a charged one-shot deviation gives at most
max(gross_j)-alpha K_j, whereas prescribed uncharged play gives at least
min(gross_j). The strict deposit inequality makes the deviation worse.
Firstness and validity of the focal past packet word are known at that
information, so this does not assume a second charge saves an already-paid
deposit. Charged-only sites are instead the free agents of the perturbed
equilibrium. Their individual best responses pass to the limit in the
finite game. These arguments cover all information sets. Perfect recall and
the one-shot deviation principle give sequential rationality.

All profiles in the native sequence are fully mixed on the fixed finite
menus. No source, public-chance, initial-input, builder-seed or audit law is
perturbed. Pass to one subsequence on which the profiles, Bayes beliefs and
the finitely many required Phi-conditioned laws converge. This supplies
Kreps--Wilson consistency for the SAME assessment used above.

On its paths, the limit profile chooses the honest source values and sends
every packet at the protected first callback. Every such event succeeds and
the audit finds only authorized first packets. No owner is excluded, no
reset occurs and no charge or forfeit is collected. Events of different
owners inside a phase commute: they read their own private data and the
already fixed public past, with same-owner order retained. Canonical weaving
therefore gives the original honest run using the SAME original inputs and
public chance kernels. This identifies jointly the initial parameters,
public results and realized net payoffs, not just their separate marginals.

This is a mathematical proof draft for the selected construction under the
document's explicit strong service assumptions. It is not a checked Lean
theorem and does not identify the existing implementation as its witness.

## Boundary between this construction and the implementation

The existing broad post-exclusion native completion is not the pinned
construction above:
a focal expiry can change another owner's still-pending old-phase value
before reset. Nor does its ordinary source-policy carrier automatically
identify distinct recovery occurrences. The arbitrary controller contract
also does not enforce the strong service packet quotient used above. These
differences must be resolved before an implementation of the mathematical
construction is reported as full SE preservation.

The formal auxiliary source also admits an accepted failed binding separately
from an omission. Conditioning on no omission, or on its continuing menu,
does not yield a law on domain values. A realization through that larger
source must keep an explicit accepted-failure source tier beta_n, separate
from the native zeta_n^3 tier. If these extra source paths are removed by
content repair, choose beta_n=o(gamma_n^T), where gamma_n is a preselected
lower bound for ordinary domain actions, and prove the same-path repair.
The full source minimum rho_n includes beta_n and cannot replace gamma_n in
that estimate. This is an adapter obligation for the larger formal source;
the mathematical domain-value source used above has no such extra action.
