# Concurrent SE preservation: mathematical audit

This note works with the theorem and runtime semantics of
`docs/se-preservation-commit-reveal.md`. It records mathematical arguments,
not claims of Lean verification. No runtime or target assumption is changed.

**Math audit: source/reset ✓ · full-fiber conditioning ✓ · rare-event normalization ✓ · full Lean SE open.**

The source strategy is selected with the erasure and failed-attempt pins
constructed below. This is not a claim about an arbitrary source extension
or an arbitrary completion of the current native policy family.

## Scope and proof dependency

The mathematical conclusion here is Theorem 3 of the main document, whose
program starts in the empty context. Its native transport argument also
applies to independent initial OWNER tuples, allowing arbitrary correlation
within one owner's tuple. The source erasure argument below retains an
arbitrary original joint setup density, but that fact alone does not extend
native transport to correlated tuples across owners.

In particular, Lemma T uses both a product compatibility domain and a
factorization over active and excluded owners. If their initial bits satisfy
X=Y almost surely, the support is diagonal. An operational factor depending
on the excluded owner's Y can change the active owner's X posterior. The
claimed cancellation of that factor is then unavailable. An arbitrary
correlated-initial-law preservation theorem needs a separate transport
argument; it is not established here. This scope distinction leaves the
formal target and its checklist unchanged.

The proof has the following dependency order. All experiments retain the
original setup, public chance and builder laws.

1. **Select a source assessment.** Chronological substitution of voided own
   words gives a common support D(q) and the exact cylinder identity

       p_n(z,omega,w,q) = 1{z in D(q)} A_n(z,omega;q) L_j(w;q).

   Bayes normalization cancels L_j separately at each full-information
   member. This holds also under the common future occurrence coins. Thus
   ordinary members have the same successful-phase payoff vector H_K;
   known-failed attachments have action-independent payoffs. A class is an
   antichain, so its payoff is affine in its shared current distribution.
   At a free class the objective has the form constant+Lambda_K*x.H_K.
   Exact constrained maximization cancels every positive Lambda_K before
   any limit. With d domain values its conditional regret is at most
   d*gamma_n*spread_j. The zero-coefficient members are indifferent.
   Honest pins retain the given honest assessment by the relative departure
   bound. The terminal payoff floor and the exact common-reset identity
   compare omission and accepted failure without future optimality. This
   produces a full-information source SE with
   the required sharing and successful-phase value optimality.

2. **Construct the native prescription from observable data.** The forward
   archive scan produces a genuine reduced source key at every unsent
   callback. It consumes each original attempt once, including exhausted
   restore. That key's domain coordinate has never been read: preceding
   callbacks at this occurrence were value-independent WAITs. Conditioning
   therefore preserves its selected law and the actual posterior of every
   remaining original coordinate. The local seed is separately filtered by
   its observable service transcript. Finite local backward induction
   selects a success-maximizing own-service rule under that filtered law.

3. **Transport inside the actual rare event.** Fix I and clean possibility
   of Phi. First compare the actual fully mixed law with normalized Q_n
   inside I-and-Phi. Then remove effective foreign RAW origins by relative
   repairs preserving that SAME event. Whole-phase induction makes the
   retained foreign word and Phi independent of the focal future, allowing
   its normalized continuation to sum to one. For the enlarged formal
   source, separately repair its accepted-failure tier with relative error
   O(beta_n*gamma_n^(-T)); beta_n remains distinct from native RAW.
   On the common operational
   domain, the regular active-owner weight is

       A_n(o) C_n (1+epsilon_n(o)),
       C_n>0,  sup_o |epsilon_n(o)| -> 0.

   The source weight is proportional to the same A_n. Normalization
   cancels C_n even when it tends to zero. The explicit remainder estimate
   below transfers the resulting total-variation limit back to the actual
   conditional law. No error is divided by the mass of I or Phi.

4. **Compare original native deviations.** Source conditional optimality
   and transport give W_v<=W_tau+delta_n at each ordinary binding input,
   with delta_n->0. Reset contributes a common term, and W_tau>=a_j.
   Write P_star for the optimal remaining service success probability.
   An immediate SEND with p_now<=P_star consequently obeys

       a_j+p_now*(W_v-a_j)
         <= a_j+P_star*(W_tau-a_j)+delta_n.

   WAIT followed by the prescription retains the same unused domain law
   and has remaining success probability at most P_star. The local-seed
   argument also bounds policies reading extra operational observations.
   Own bad bindings use the common reset payoff; correctly opening and
   silence at inactive sites use their pointwise comparisons. Charged
   one-shot deviations lose the strict margin alpha*K_j-spread_j.
   Charged-only sites use the perturbed free-agent best responses.

Take one subsequence for all native profiles, Bayes beliefs and required
phase-conditioned laws; finiteness makes this simultaneous. The comparisons
give sequential rationality at every original information set by the
one-shot deviation principle. The subsequence gives consistency. On its
initialized paths every packet is sent at its protected first opportunity,
so the original honest joint law is preserved with no charge or exclusion.
The arguments below establish the identities and bounds used in this chain;
their full Lean realization remains open.

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

This does not require atoms in an original seed space. A seed can first be
pushed to its complete response table on the fixed finite collection of
possible local records. There are finitely many such tables. Use the
minimum positive atom of that pushforward law (and the corresponding
finite remainder-response law) when defining b. This is a deterministic
quotient of the SAME initialized randomness, preserving its independence
and observable run law; no seed law is perturbed or refreshed.

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

There is a third case when the retained event excludes EVERY effective
active-foreign RAW origin: a RAW-origin WAIT at an eligible unsent callback.
Replace its latent origin by BASE while retaining the identical physical
WAIT. If b_n>=c zeta_n is the base WAIT atom, its RAW-to-base weight ratio
is at most

    C zeta_n^3 / ((1-C zeta_n^3) b_n) = O(zeta_n^2).

Both binding and opening WAIT have the required positive base floor in the
selected prescription. At a pure-WAIT callback the bound is O(zeta_n^3).
The origin is unobserved and virtual updates read the physical response,
so all later records, I and Phi are literally unchanged. Replacing every
such origin has finite multiplicity and gives a relative O(zeta_n^2)
remainder on the SAME I-and-Phi domain. Perform this comparison together
with the bad-SEND and same-value-SEND repairs BEFORE restricting to the
no-effective-RAW event. A later near-one likelihood estimate for physical
WAIT factors alone would not establish this deletion. Sent and inert
singleton-WAIT callbacks need no restriction: integrate their unread labels.

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
only in the focal future. For a genuinely ready foreign binding e, enumerate
the potential relative activation calendar C_e(xi_e) fixed by S1. The owner's
compiled order prevents a different simultaneously live own event from
excluding it. Until the first SEND, WAIT leaves e ready; a never-SEND episode
therefore exhausts C_e before expiry. The completion contract rules out
cutting this episode off at the finite runner's horizon.

Index its original timing tape by this calendar. If two first-SEND indices
were k<l, the second episode would have taken WAIT at k despite having the
same tape and local record. A sent episode and a never-SEND episode give
the same contradiction, since the latter exhausts the calendar. Thus the
first SEND has the same relative clock in both runs, or neither sends. S1
and the packet quotient give the same resolved success bit. Exact inclusion
times need not agree.

The whole-phase induction has a precise invariant. For every processed
foreign occurrence the paired runs have the same virtual typed choice,
skip status, relative first-SEND decision and resolved success bit. For
each owner they have the same preceding virtual word. Start with the same
old entry and original random coordinates. A minimal unprocessed foreign
event has the same skip status and virtual query by that invariant and
the no-new-miss prescription. An ordinary encoder reads the same original
domain coordinate. Its timing tape gives the same local decision at each
potential relative activation; if one episode never sends, completion
forces it to consume the entire remaining calendar. S1 then gives the
same success bit. Readiness and inclusion may occur at different absolute
clocks, which the selected binding query and service rule ignore.

Foreign predecessors already satisfy the invariant. A focal predecessor
can change readiness time but cannot prevent readiness: even a failed
event completes, and the old attempt cannot close until its events finish.
Same-owner order prevents a second live own event from excluding this
owner during its unresolved episode. Thus the induction covers all events,
including repeated ownership, and reaches the completed ORIGINAL attempt
before any restore. Its foreign word and Phi are functions of the original
nonfocal randomness. This proves locality of the selected whole-phase
experiment; independent event seeds alone would not prove it for policies
that read foreign traffic or hidden value-dependent menus.

The source query reads the old entry's public data and its owner's preceding
virtual source choices. Induct in a topological order of the phase graph,
retaining each owner's order. Earlier own outcomes determine skips and later
own queries. A cross-owner predecessor can change absolute readiness, but
S1 fixes the relative calendar and seed law for that occurrence. A failed
predecessor still completes, so the phase completion contract readies its
successors. Commitment opacity and the no-new-miss query preserve the
induction. This proves independence for the selected prescription, not for
arbitrary source-query or timing rules allowed to read foreign observations.

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

For a whole-menu RAW encoder, the post-RAW virtual word might itself read
private alias data. In that realization use a stopped variable instead:
write G={no effective active-foreign RAW use, Phi}, and let Y be the foreign
virtual word and survivor vector on G, and a cemetery symbol otherwise.
Only this jointly restricted output must be non-focal. Fix one run in G
and pair it with another supported focal future under the SAME nonfocal
randomness. Before any first discrepancy, ordinary foreign episodes have
the same preceding virtual word and query. Their complete relative calendars
and timing tapes force the same first SEND, or the same never-SEND result.
A first RAW in the paired run is impossible: that genuinely unsent ordinal
would be unsent in the reference run too, or an earlier common SEND would
already have ended both unsent episodes. The same ordinal tier flag would then
make the reference run RAW. A first foreign expiry is likewise impossible:
the reference survivor's true receipt supplies a genuine request at that
event; the common first-SEND decision and S1 force the same success.
Thus both runs are in G, and the foreign words agree. Reversing the roles
shows that G and Y are non-focal. This proves neither independence of an
arbitrary post-RAW word nor equality of the identity/order of first RAW
occurrences on discarded runs. Remove all RAW origins by the bad-SEND,
same-value-SEND and same-action-WAIT repairs before using this good-event
statement. There is no need to assert independence of an arbitrary trajectory
after its first RAW action.
At sent or inert singleton-WAIT callbacks, the base and RAW response laws
are identical. Integrate out their unread tier labels; counting them as a
bad event would make the event depend on irrelevant callback multiplicity.

The measure order is consequently as follows. Transfer P_n(.|I,Phi) to
Q_n(.|I,Phi) by the charged bound and the clean-path density comparison.
Apply the same-prior bad-binding repair under Q_n to obtain

    Q_n(B != 0, I, Phi) <= r_n Q_n(B = 0, I, Phi),   r_n -> 0.

In the direct bad-only construction, restricting to B=0 costs at most
r_n/(1+r_n) in total variation. Both B and Phi are non-focal there, so the
NORMALIZED focal Q_n continuation sums to one for each fixed remaining
realization with B=0 and Phi.

For the whole-menu RAW construction use G={no effective active-foreign
RAW use, Phi}. The bad-SEND, same-value-SEND and same-action-WAIT repairs
compare Q_n(. | I,Phi) to Q_n(. | I,G). The stopped-variable argument makes G
and its foreign word non-focal; it does not assert that Phi or B separately
remain non-focal after RAW. Integrate the normalized focal continuation
only after this restriction to G. No restriction is imposed on the focal
owner's own bad bindings. Only at this point apply the regular source
factorization below.

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

### Averaging the original timing tables

The fixed-table coupling must represent the actual behavioral Q_n law.
For every owner sample its ENTIRE address-by-ordinal timing table once, at
initialization, independently with the prescribed coordinate laws. An address
contains the full attempt identifier and event; the ordinal counts that
owner's callbacks at this address. Keep the original vector of per-owner
tables, including unused coordinates, together with all primitive randomness.

At an actual prefix, fix its next owner and coordinate c. Changing only this
coordinate cannot change the prefix: earlier callbacks at this address used
strictly smaller ordinals; other addresses read different coordinates;
opening and inert responses ignore this coin; no outside actor can inspect
an unread private coordinate. Split the SAME product prior as mu_c x nu.
The likelihood of the actual full prefix consequently has the form ell(R),
where R is the entire remainder. At every positive prefix,

    Law(T_c,R | prefix) = mu_c x Law(R | prefix).

Averaging the next member response under mu_c gives exactly its prescribed
behavioral response mixture. Induction over the finite original runner then
identifies the stopped Q_n law together with its likelihood-induced table
posterior. Equivalently this is the original table prior integrated against
the fixed-member stopped kernel; it is not the behavioral law multiplied by
a fresh independent table prior. A later entry uses this same posterior. The
formula is not asserted for an arbitrary replacement entry prior, and is
not asserted after conditioning on future G or Phi, which may read this coin.

The same calculation must be made for the FULL native information fiber,
rather than only the implementation's private memory. Here is that step
explicitly. Fix a positive decision information value I that determines the
next address/ordinal coordinate c. Mask just that coordinate in the ORIGINAL
per-owner table vector. Let R contain this masked vector together with all
other original primitive randomness, including source plans, setup and
service seeds. The original prior splits as mu_c(dx) nu_c(dR); mu_c is fixed
by c and the stage parameters. Derived entry tags may be retained as
functions of R, once prefix-unreadness below has shown that they do not read
c. They are not additional independent primitive draws. Any randomness not
predrawn can equivalently remain in the original runner kernel.

For each possible observation time t, and each actual prefix ending at I,
the coordinate c has not been read. Replay with only its value changed:
earlier callbacks at this address used smaller ordinals, other addresses
used other coordinates, and inert callbacks ignored it. Hence the entire
prefix and its observation at time t are unchanged. This also preserves
which prefixes belong to I; it is stronger than agreement of their final
private-memory records. Summing their original runner likelihoods and the
original observation-time weights gives a nonnegative function ell_I(R)
independent of x. Therefore, with Z_I>0,

    Law(T_c=x, R in dR | I)
      = mu_c(x) nu_c(dR) ell_I(R) / Z_I,
    Z_I = integral ell_I(R) nu_c(dR).

Observation-time weights here are those defining the original assessment;
one may use a uniform independent time on its fixed finite horizon, whose
common factor cancels. No prefix is reweighted after observing its input.
The deterministic mask and reinsertion recover the SAME original table
vector. Thus the right-hand remainder is its actual updated posterior,
including correlations induced between all the other primitive tags.
An auxiliary independent table attached to an already sampled history
would not prove this identity. Nor does the identity apply after restricting
to a future event that reads c. The good-event coupling and relative repairs
are used only afterwards.

To apply the fixed-member coupling one may read each address from its
owner's original table; the unused coordinates and original per-owner table
vector remain tags. This is a deterministic readout, not a new table draw.
Condition first on those tags and the genuine entry, apply the pathwise
good-reference argument, then average under their actual posterior. Only
after proving the required SAME-event relative repairs restrict to G and
sum the normalized focal continuation. Its conditional kernel sums to one
even when it is correlated with the retained entry tags.

Two distinct obligations enter this argument. Table unreadness proves the
behavioral realization; scalar G invariance does not. Conversely scalar G
invariance does not identify a foreign typed word: a value rule allowed to
copy a focal leak could change that word while every delivery succeeds.
The selected prefix-causal query invariant rules this out. Each foreign
query reads only its original source entry, its preceding virtual own word
and its occurrence. The native scan establishing that invariant stops before
the queried binding and uses no future focal miss or Phi. The good-reference
induction above can therefore obtain typed-word equality without assuming
the posterior transport it is meant to prove.

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

On regular active-foreign branches the directly selected typed encoder has
one preparation for each value/slot pair. If it has additional hidden
aliases, first sum them conditional on that pair and the selected tier.
The required local identity is

    sum_alias Q_H(label,v,slot,alias)
      = t_H(label) tau_n(v | reduced_query(H)) s_n(slot | F(H)),

where tau_n is the conditional source value law. All aliases in this sum
emit the same envelope, and subsequent prescriptions read the virtual typed
word and local service record, not the hidden alias. A whole-menu RAW tier
does not automatically satisfy this identity: remove its active-owner
origins by the three repairs above, or prove the identity for its pushforward.
In particular, unit total SEND mass alone is insufficient. Excluded-owner
raw preparations and evidence retain their ACTUAL probabilities in e or
the operational template; they need no matching alias normalization.
Opacity by itself does not give a bijection between raw preparations in
different private contexts.

Concretely, let F(H) be the bounded fresh slots at a genuine unsent binding
history H. Substitution preserves the fresh/occupied status of every slot,
so F(H) is unchanged. Every typed result can be prepared at every slot in
F(H), with the same emitted envelope at that slot. A canonical-plus-uniform
slot law has the same probability in both contexts,

    s_n(slot | H) = w_n/|F(H)| + (1-w_n) 1{slot = min F(H)}.

Thus slots and headers remain in the operational template, with their
actual likelihoods. They cannot be integrated out merely because S1 makes
success slot-independent: the focal information can observe them.

Here is the physical domain argument on this weighted operational quotient.
For fixed e, take a regular quotient realization for one compatible o.
Erase active hidden meanings from its live, saved AND archived states,
from the preparation catalogue and from derived private views. Retain
event/attempt occurrences, tier labels, signed envelope headers, fresh
slots, handles, clocks, commands, public results, focal data and all
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
are retained. Every fresh slot in the selected encoder admits every typed
domain value: freshness tests the handle, not the hidden meaning, and guards
are deferred. The same-slot source tier therefore gives positive support
for the substituted value with the same envelope. Source-compatible initial
tuples retain positive original input support. Substituting o back inverts
the operation on quotient templates. Hidden preparation fibers need not
have equal cardinality: each was already integrated under its normalized
ordinary encoder. Hence the weighted template set Omega(e) is independent of o.
It may be empty; K_n(e)=0 is allowed.

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
likewise give a uniformly near-one product. Opening WAIT needs no exact
whole-menu symmetry: its trembling base atom b is at least c zeta_n at an
eligible unsent callback. Adding a RAW residual of total weight at most
C zeta_n^3 changes it to (1-w)b+w r, with 0<=r<=1, whose ratio to b is
between 1-C zeta_n^3 and 1+(C/c) zeta_n^2. Apply the same bound to opening
SEND only after grouping aliases by the unique permitted emitted opening
envelope, not to a particular hidden alias with zero base mass. A pure
WAIT branch has its own 1+O(zeta_n^3) estimate; excluded-owner exceptional
factors stay in e/template. Finite products are uniformly near one. For the
directly specified local timing tiers locality is exact; a whole-menu RAW
implementation needs these relative comparisons. A pure canonical rule
with a zero WAIT atom would not justify this relative estimate.

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

For the enlarged formal source, apply its separate whole-owner beta repair
before this comparison. Native ordinary encoders use the conditional domain
law tau, whereas a source ordinary atom is
(1-alpha_n)(1-beta_n) tau. The missing beta factors contribute only a
uniform factor 1+O(T beta_n); beta is not a native packet tier. The source
conditional mass removed by that repair must also be included in the error.

Explicitly, set a_n=(1-C zeta_n^M)^T -> 1. Let c_n bound the charged/clean
P_n mass ratio inside I-and-Phi, let b_n bound the bad/regular Q_n ratio
there, and let |epsilon_n(o)|<=epsilon_n<1. The L1 error between the actual
conditional active law and the source law is at most

    2 c_n/(1+c_n) + 2(1-a_n)/a_n
      + 2 b_n/(1+b_n) + 2 s_n/(1+s_n)
      + 2 epsilon_n/(1-epsilon_n) -> 0.

Here s_n is the source beta/regular mass ratio from whole-owner repair;
epsilon_n includes the uniformly vanishing beta correction. The first,
third and fourth terms bound mixture remainders. The second uses the
uniform clean-path density ratio, including normalization on I-and-Phi.
The last subtracts the source-weighted mean of epsilon. None divides by
the unnormalized mass of I or Phi. If a larger RAW-origin submeasure is
used, add its same-value-SEND and same-action-WAIT remainders as well.

For completeness, the normalization step is a finite calculation, including
when some source weights vanish. Write p(o)=A_n(o)/sum_u A_n(u), and let
epsilon_bar=sum_o p(o) epsilon_n(o). The regular native marginal is exactly

    p_regular(o) = p(o) (1+epsilon_n(o))/(1+epsilon_bar).

Consequently its L1 distance from p is at most
2 epsilon_n/(1-epsilon_n). A zero A_n(o) has zero regular native weight as
well; an additive leakage at such an o must instead be counted in a
remainder. Adding a disjoint remainder of mass at most r times the regular
mass changes the normalized law by at most 2r/(1+r) in L1. These identities
prove the displayed bound by the triangle inequality. They do not require
C_n, the total regular mass, or the mass of the conditioned event to be
bounded away from zero. The substantive part of Lemma T is therefore the
same-event repairs and the common operational domain established above;
normalization cannot supply either of those properties.

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

Explicitly, let q retain p, the whole original private tuple, the live own
typed cells and the occurrence. Static restriction of q together with w
reconstructs every earlier personal information state i_r(q,w) and action
a_r. For a compatible other-owner world z, write

    Pr_n(z,w,q) = 1{z in D(q)} A_n(z;q) L_j(w;q),
    L_j(w;q) = product_{past own r} sigma_n(a_r | i_r(q,w)).

The original own-input density is already conditioned in q, or is included
in L_j. The domain D(q) is independent of w: no voided value was published,
and no obligation reading it survived restore. Original public-chance and
other-owner factors belong to A_n. Thus L_j cancels from the conditional
law separately at each positive full-information member. This argument
retains other owners' complete private trajectories, including their voided
words; it does not replace them by independent live cells.

Here is the global support argument behind that identity. Fix an ACTIVE
target owner j. Let w record the raw focal choices at all voided commitment
occurrences, including accepted-failure choices, at their original logical
clocks. It does not record an unused domain-table answer behind an
accepted-failure choice. Let z record the complete nonfocal raw histories,
the original supported joint setup draw apart from j's tuple already in q,
and the supported public draws. Unused random coordinates are integrated
out. These are chronological records from initialization, not separately
chosen entry posteriors.

The pair (q,w) determines every past focal observation and raw choice.
Source contexts extend by fresh names. Every nonvoided focal commitment is
therefore the restriction of the retained typed store to its original name.
A surviving focal reveal was TRUE: withholding or a rejected reveal would
permanently exclude j. Samples have no focal choice. Public chronology
locates the remaining, voided commitment segments and their close cuts;
w supplies exactly their missing choices. Reconstruct the information tags
on own-play records by replay, rather than treating those tags as new data.

For fixed q and z, take one supported prefix with word w and substitute
another locally admissible word w'. Replay in chronological order:

1. In each voided commitment window retain the same omission word and all
   nonfocal raw choices. A changed domain value or accepted-failure bit is
   private. No reveal, public sample or deferred guard check occurs inside
   that window. Every nonfocal full observation and own-play record is
   therefore unchanged. The full raw menu permits these values even when
   a deferred guard would reject them.
2. The unchanged omission word gives the same exclusions and real close.
   Restore discards all substituted cells AND their obligations, leaving
   the same saved typed state and public record. A retired window containing
   an active choice of j closes by retry, since j survives to the target.
   An exhausted window with no active focal choice is retained literally;
   it contributes no word to substitute.
3. Between these windows replay the unchanged nonvoided focal choices,
   nonfocal choices and supported public draws. Their typed inputs and the
   public results agree. Thus every executed guard has the same result and
   every public sample has the same original kernel and draw. Earlier
   private word differences can remain in recall, but cannot enter a
   nonfocal observation or survive as a live focal typed value.

This induction keeps each nonfocal FULL information state unchanged, not
just its erased endpoint. The construction depends on z only through its
fixed records; local admissibility of w' is determined by q and w'. Reverse
substitution recovers the original prefix. Consequently compatible prefixes
are indexed by the same domain D(q) for every admissible w.

Their behavioral cylinder weights now split exactly. Each nonfocal action
is evaluated at the same full information state, and each Nature kernel
at the same public input, so their product is A_n(z;q). Keep the ORIGINAL
joint setup density in this factor, conditional on the focal tuple fixed
in q. No independence or equality of setup atoms is inferred from the
splice. Each focal factor is evaluated at its reconstructed i_r(q,w), so
their product is L_j(w;q). This proves the displayed likelihood identity.

The future version additionally uses the selected sharing constraints for
j's OWN continuation, as well as those of its opponents. Starting at paired
prefixes, their live typed states and nonfocal full memories agree. Couple
unused occurrence flags and domain draws. Shared focal queries erase the
only remaining word difference; nonfocal queries see identical full
information. Induction gives the same future typed path and payoff.
Adjoining this future randomness to z proves the corresponding identity
with A_n(z,omega;q). An arbitrary memory-dependent focal continuation would
invalidate this last step. No equality of previously conditioned private
table joints is needed.

Here is the corresponding statement directly on the ORIGINAL information
fibers, without choosing a new game or a prior on reduced labels. Let I and
J be genuine active decision information sets with E(I)=E(J), and write
H(I), H(J) for their finite sets of complete prefix histories. Fix reference
histories i in H(I) and j in H(J). For h in H(I), substitute j's focal raw
word into h, keeping h's literal original setup prefix, public draws and
every nonfocal raw word. The chronological support argument gives a UNIQUE
history T(h) in H(J). Full focal information determines its raw word,
including automatic and omitted coordinates. Substitution of i's word is
therefore the inverse: both composites retain the original setup, public
word and every raw coordinate, which determine the original history. Thus
T is a bijection of actual information fibers.

Fix any fully mixed behavioral profile sigma. Decompose original reach as

    p_sigma(h) = r_I c_sigma(h),            h in H(I),
    p_sigma(k) = r_J c_sigma(k),            k in H(J).

Here c is counterfactual reach, including the ORIGINAL joint setup and
Nature densities, and r is the product of past focal behavioral factors.
Perfect recall makes r_I constant on H(I) and r_J constant on H(J); both
are positive. Substitution preserves each nonfocal full observation and
action and every Nature factor, so c_sigma(T(h))=c_sigma(h) exactly. Hence

    p_sigma(T(h)) = (r_J/r_I) p_sigma(h),
    Z_J = sum_{k in H(J)} p_sigma(k) = (r_J/r_I) Z_I,
    mu_J(T(h)) = mu_I(h).

The last line is the actual Bayes belief, with Z_I,Z_J>0. Information
fibers are antichains, so these sums are the probabilities of their
information events. This argument allows an arbitrarily correlated
original setup law: no setup atom is changed by T. It says nothing about
the different active/excluded-owner product required for native transport.

Belief transport alone does NOT identify continuation values under an
arbitrary sigma. For the selected shared profiles, force the SAME current
domain value at h and T(h), then couple the future as above. Induction on
the original bounded tree gives equal live states and public histories;
the old focal word is their only private difference. Shared focal queries
erase it and nonfocal full information agrees. Consequently both runs use
the same future action laws, original chance kernels and occurrence flags.
The remaining-attempt flag event D has the same indicator and the paired
payoffs agree. Integrating this conditional coupling against the displayed
Bayes equality proves equality of the joint law of D and payoff for every
current domain value. If D has positive probability, its conditional
payoff vector H is equal too; when it has zero probability, only the
unconditional reset comparison is used. This establishes the successful-
phase ranking needed BEFORE the auxiliary best-response calculation.

This bijection applies to equal E-keys, not to arbitrary equal combined
keys E(F(I)). At ordinary members F leaves the information unchanged, which
reduces combined-key equality to E equality. A known-foreign-failed
attachment can have a different true public chronology. It requires no
Bayes identification with the ordinary member: couple two of its current
nonmissing choices using the same original occurrence flags. If the focal
owner later omits, both payoffs are a_j. Otherwise the already fixed foreign
miss forces a retry, discarding every changed value and obligation, and
the erased continuation is the same. Thus its NONMISSING value payoff is
constant. Current omission need not tie with that constant; it is compared
separately using the lower bound on the reset continuation. These two
arguments justify the ordinary rankings and the attachment pins without
asserting that all members have identical public histories or beliefs.

Future legal menus and payoffs also ignore w. The same erasure transports
the player's future policies between the full information sets. For shared
continuations of all owners, every member of a reduced-information pool has
the SAME conditional payoff vector over current nonmissing actions.
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
the requested honest SE. More precisely, the key retains all live own typed
cells, original private inputs and the complete public chronology. On a
no-reset honest history, restrict those cells to each earlier static context
to reconstruct every earlier private signal; own choices are the stored
values and earlier reveal actions are TRUE. Thus the key determines the
original honest full information. Two copied honest members cannot impose
different honest laws on one class. A coarser current-state key would not
justify that pin coherence.

Failure and opening require a separate comparison. Every terminal payoff is
at least a_j. Omission and reveal withholding give exactly a_j. For a current
accepted failed binding, the common-reset identity below shows that replacing
it by a domain value changes only the no-reset payoff, from a_j to a payoff
at least a_j. These comparisons hold before any future best-response claim.
Together with individual domain optimality and honest-pin preservation, they
give sequential rationality in the original full-information game.

The perturbation choices have a noncircular order. Take T>=1, let C bound
the finite menus, and let 0<h_n<=1/(n+1) bound the positive honest action
and fixed chance atoms from below. For example, first choose

    eta_n = h_n^(T+1)/(n+1),       gamma_n = eta_n^2/(2C).

Use the globally fixed omission rate eta_n, give every conditional domain
action at least gamma_n, and put only O(eta_n^2) total mass on extra
guard-violating actions of copied honest agents. These constraints are
nonempty for all sufficiently large n; discard a finite initial segment.
Their total honest-departure mass is O(eta_n), and
eta_n/h_n^T=h_n/(n+1)->0. All these numbers are fixed BEFORE selecting the
pooled equilibrium. They do not depend on the equilibrium's eventual reach
probabilities. A global omission rate is a permitted special case of a
public-region rate and also supplies the old-entry pins below.

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

    U_K(x) = c + pi_K sum_{I in R_K} r_I (x . V_K)
               + sum_{I in F_K} r_I c_I.

Here r_I>0 is the reach probability, independent of x, and pi_K>0 is the
fixed probability of taking the current domain branch. Ancillary-word
cancellation gives the SAME conditional vector V_K at each ordinary member;
the failed-member c_I is exactly action-independent. Thus maximizing U_K
maximizes each ordinary member's conditional payoff, while failed members
impose no competing ranking. This calculation holds for every admissible
future profile; it does not assume future optimality to obtain the fixed
point. This maximization applies to free classes; copied honest and doomed
classes keep their specified pins and use the separate limit arguments.
Empty R_K classes have only indifferent members.

There is a useful quantitative consequence of the reset decomposition below.
Let H_K be the conditional successful-phase vector. Ancillary cancellation
also applies after adjoining the future original randomness omega. The
joint weight is A_n(z,omega;q)L_j(w;q); the success event D is a function
of the common occurrence flags, independent of w and the current domain
value. Restricting to D therefore leaves the same cancellable L_j factor.
Given q,z,omega and the current value, erased-word sharing makes the later
payoff independent of w. Thus H_K is common to the ordinary members;
equality of their unconditional payoff vectors alone would not prove this.
Write their payoff vectors as
`c_I + lambda_I H_K`, with lambda_I>=0, and absorb every failed attachment
into the constant term. The pool objective is then

    constant + Lambda_K (x . H_K),
    Lambda_K = pi_K sum_{I in R_K} r_I lambda_I.

At a binding pi_K=(1-alpha_n)(1-beta_n); without the accepted-failure
tier it is 1-alpha_n. It is common to the class and independent of x.

If Lambda_K>0, its constrained maximizers are EXACTLY the constrained
maximizers of x.H_K, however small Lambda_K is. For a domain menu of size d
with a uniform lower bound gamma_n<1/d, write

    x = gamma_n 1 + (1-d gamma_n) y,    y in the probability simplex.

A best response puts y on maximizers of H_K. Hence the selected conditional
domain law tau_K satisfies, for every domain value v,

    H_K(v) - tau_K.H_K <= d gamma_n osc(H_K).

The oscillation is bounded by the fixed terminal payoff range. This error
tends to zero WITHOUT dividing an approximate payoff bound by Lambda_K or
by a phase-success probability. This order is essential: an unconditional
regret bound alone would give no conditional guarantee at a rare success
event. If Lambda_K=0, every ordinary coefficient in this nonnegative sum is
zero, so the entire class is action-independent; no conditional ranking is
needed. Copied honest classes use the separately preserved honest beliefs,
rather than this free-agent maximization.

### The finite game and the conditional best-response bound

Here is the fixed-point argument with its quantifiers made explicit. Fix n
and the failure rates and domain floors first. The players of the auxiliary
game are the FREE reduced classes K, not the original full-information
members. A pure action of K is a domain value in its common finite menu;
its mixed action is a distribution x_K with x_K(v)>=gamma_n for every v.
Insert these distributions into the original full-information source game,
using the specified honest and doomed pins at the other classes. This
defines a genuine behavioral profile for EVERY auxiliary strategy profile.
Use the original owner's ex-ante expected terminal payoff as K's utility.

No genuine source path visits K twice: the key preserves the logical
occurrence, which strictly advances at every source transition. The reach
weight r_I of each member I is consequently independent of x_K. All
occurrences of x_K in the expected payoff are disjoint current-action
factors. Holding the other classes fixed therefore makes the utility affine
in x_K. The utility is continuous in the whole finite profile. The product
of the nonempty compact convex floor simplices thus has a constrained
equilibrium by the finite-game best-response fixed-point argument. There
is no Bayes denominator in this existence argument and no equilibrium
reach probability enters the choice of gamma_n.

To identify that equilibrium's INDIVIDUAL incentives, fix its opponents
and future play, and fix an ordinary full-information member I of K.
Let w be its erased own retired word. Its retained key q and w reconstruct
every past own observation and action by static restriction, in source
order. Substituting a compatible w changes no public observation: a voided
binding is never opened, its obligations are discarded, and subsequent
foreign kernels and reset continuations read the shared key. Hence the
complete other-owner/chance domain D(q) is unchanged. For complete future
original randomness omega, the unnormalized likelihood is exactly

    p_n(z,omega,w,q) = 1{z in D(q)} A_n(z,omega;q) L_j(w;q).

This identity is for the original fixed setup and chance laws. In
particular A_n retains entire other-owner private tuples and retired words.
At a positive full-information member, L_j(w;q)>0 cancels in Bayes' rule.
The remaining-block success event D uses the common occurrence-level
omission/failure coins; it reads neither w nor the forced current domain
value. Restricting the displayed identity to D leaves the SAME cancellable
factor. Conditional successful-phase payoff H_K is therefore common across
ordinary members, even at finite n. Agreement of unconditional vectors
alone would not establish this step.

For fixed other classes, the source reset decomposition below now gives

    utility_K(x_K) = constant + Lambda_K (x_K . H_K),
    Lambda_K = pi_K sum_{ordinary I in K} r_I Pr_n(D | I) >= 0.

The current domain-branch probability pi_K is fixed before optimization:
it is (1-alpha_n)(1-beta_n) at a binding and 1-alpha_n at a reveal.

Known-failed attachments contribute only constants: every changed current
value is voided, or its owner is itself excluded. The common-flag coupling
and erased continuation give the same reset distribution in either case.
No future best-response assertion is used here. If Lambda_K>0, an EXACT
auxiliary best response maximizes x_K.H_K. Write d for its menu size and
S_j for the fixed terminal payoff spread. The floor-simplex representation
x_K=gamma_n*1+(1-d*gamma_n)*y yields the explicit individual bound

    H_K(v) - x_K.H_K <= d*gamma_n*S_j   for every domain value v.

The bound has no inverse reach weight or inverse success probability.
If Lambda_K=0, full mixing gives r_I>0 at every genuine member, so each
ordinary Pr_n(D | I)=0 and its unconditional current-action payoff is
constant. Such a class imposes no successful-phase ranking. Honest pins
instead use the separately retained honest beliefs and honest optimality
in the limit. These statements establish precisely what the pooled fixed
point supplies; an equilibrium of a game that merely SUMS incompatible
conditional rankings would not suffice.

### The original plan uses reduced occurrences as coordinates

Before taking any fixed point, let I_j be the finite set of genuine source
decision information states.
Define kappa_j(i) to retain the owner, instruction address and attempt
generation together with the reduced no-new-miss information E(F(i)).
The index set K_j=kappa_j(I_j) is fixed independently of n and of the
optimized profile. The erased object is only a LABEL; it
need not itself be played information. Common-menu transport follows from
the retained live typed view and actor. Let mu_(j,k) be the shared source
law selected above on that common menu.

An actual source transition strictly advances

    generation*(N+1) + instruction_position.

Retry increases generation; exhausted restore advances past the block even
when generation is unchanged. E and F preserve this occurrence. Thus no
path visits one key twice. Repeated ownership and retries have distinct
coordinates, while native WAIT callbacks intentionally reuse a key.

Draw one table X_j with law product_(k in K_j) mu_(j,k) at initialization,
independently over owners and of the original inputs and chance. At a
genuine source information state i, use X_j(kappa_j(i)), transporting its
menu membership. For a fixed genuine source history h, distinctness gives
the exact cylinder identity

    Pr{X_j(k_r)=a_r for every own occurrence r in h}
      = product_r mu_(j,k_r)(a_r).

Multiplying by the ORIGINAL setup and chance factors proves the entire
behavioral source history law. It does not redraw a plan at entry. At a
current pre-action i, kappa_j(i) was unused on every history in its fiber.
That information event is measurable without this coordinate, so

    Law(X_j(kappa_j(i)), remainder | i)
      = mu_(j,kappa_j(i)) x Law(remainder | i).

The remainder keeps the actual posterior of inputs, previous coordinates,
other policies and entry tags. The same holds after further conditioning
that does not read this coordinate. An independent table indexed by FULL
information states has the same external source run law, but different
private table joints. Equal laws at two full information states do not make
their sampled entries equal. In particular, querying such a table at an
unplayed erased object would read a fallback, not mu_(j,k).

At bindings, refine a coordinate into independent omission, accepted-failure
and domain-value draws. In the domain-value source the middle coin is absent.
Their prescribed nested mixture has exactly the source action law. Put
omission, accepted-failure and timing coins in the remainder for native
conditioning: WAIT can
filter them, so the entire source-action law need not remain unchanged.
The unused domain-value coordinate V_k is different. Every WAIT and silent
preparation branch before choosing SEND is independent of V_k; the actual
SEND encoder may then read it. A native bad declaration uses its specified
virtual representative instead. In the selected normalized Q_n experiment,
at a positive unsent native input J with fixed reconstructed key k,

    Law(V_k, remainder | J) = tau_(j,k) x Law(remainder | J).

This is an original-prior non-reading argument for that experiment, not for
an arbitrary assessment. It neither identifies a
native posterior with an independently reset source prior nor explains
arbitrary focal RAW actions as source draws.

For the reset coupling choose the following concrete realization at
INITIALIZATION. Independently sample O_(j,c) with rate alpha_n and B_(j,c)
with rate beta_n for each public owner/event/attempt occurrence c, and
V_(j,k) with law tau_(j,k) for each reduced private key k. All of these are
independent of the original inputs, Nature and service seeds. At a source
binding consult O, then B, then V. At a reveal consult its fixed-rate
withholding coin. Each actual source path visits c and k at most once, so
its cylinder factors are exactly alpha_n, (1-alpha_n) beta_n, or
(1-alpha_n)(1-beta_n) tau_(j,k)(v), as appropriate. This proves the same
entire behavioral source history law.

This realization correlates failure flags across counterfactual private
keys at the SAME public occurrence. Its full private-table joint law is not
the independent full-Choice table joint above. Both realize the stated
source behavior, and the chosen occurrence-flag/domain-table realization
is fixed once, before any entry or conditioning. It permits changed own
values to use the same later omission/failure flags even when they change
later own private keys. Equal rates alone would not justify that pathwise
claim for an independently sampled full-Choice table. Predrawing these
variables is an analytical representation, not an extra observation added
to the extensive-form game.

The native ordinary encoder reads ONLY V_(j,k), with its conditional domain
law tau. It does not encode the source B coin as a native bad packet, and
need not read the source O coin: its actual first-WAIT coin has the fixed
prescribed rate. The source beta tier is handled by the separate source
repair, not identified with native RAW.

Define the virtual update from the ACTUAL recalled declaration d. An
ordinary typed declaration appends its typed value; a bad declaration
appends a fixed domain representative determined by d. In particular, two
sampling tiers producing the same physical declaration produce the same
virtual update. The latent tier label may be used in a probability bound,
but cannot be read by a native strategy or by its query decoder. Restored
virtual stores discard the same voided declarations as the physical reset.
On ordinary paths the virtual and physical typed stores agree; at an own
bad binding they need not, and rationality uses the separate pointwise
own-bad-binding argument.

Here is the precise native non-reading proof. Fix a positive UNSENT input
J of an active owner under Q_n, with reconstructed key k, and split the
original experiment into
(V_k,R_k) with prior tau_k x nu_k. Replacing V_k alone cannot change the
prefix event {input=J}: earlier occurrences use different keys, any earlier
callback at this key was WAIT with a value-independent atom, and a previous
SEND at this key cannot coexist with UNSENT. A retry has a different key.
Every domain value admits the selected legal SEND encoder, so there is no
value-dependent fallback to WAIT. The origin-blind RAW decoder also reads
no unused V_k. Consequently its likelihood has the form ell_J(R_k), and

    Pr(V_k=v,R_k=r | J)
      = tau_k(v) nu_k(r) ell_J(r) / sum_s nu_k(s) ell_J(s).

This is the asserted product with the ACTUAL posterior of the entire
remainder: all other table entries, occurrence flags, input tuples, timing
coins, seeds, commands, entry tags and private operational records stay in
R_k. The argument does not reset an entry prior. Conditioning additionally
on a future Phi requires the separate non-focal phase induction; it is not
an automatic consequence of current-key non-reading.

The key is a deterministic function of an unsent native input J. Its inputs
are the fixed source syntax and phase partition; current full attempt ID and
binding address r; ordered public retired records with their original IDs,
completed-event sets and omission masks; the immutable typed public store;
the owner's original private tuple; and its recalled first declarations
with their immutable catalogue meanings. An attempted later overwrite is
not used to reinterpret an earlier declaration. Unused preparations are not
virtual source actions.

For a static source cursor c, let P(c) contain exactly the public-data and
publication observations present in its source context, read at their
original immutable native addresses. All private-input and commitment
observations are absent and the private history word is empty. Every public
cell needed for P(c) is retained: a reset crosses only a commitment block
and discards no public cell. A voided cursor may be beyond the restored
cursor, but its additional cells were commitments and P discards them.

Scan the source instructions forward, consuming archived attempts in their
chronological order. Respect the source signal convention: there is the
pre-setup signal and one genuine setup transition, with no additional
initialization transition. At a commitment block [a,b), start with the
scanned saved exclusion set E. A matching retired record (a,g) supplies
its completed omission mask: a binding completed without an accepted result
is missing; an already-excluded slot is automatic. This is read from the
completed event record, independently of any later sampled audit charge.
At each rank add the owner precisely on an
original missed binding; an already-excluded automatic slot adds nothing.
At nonfinal ranks the next cursor is the following rank, with generation
g and saved rank a. At the LAST slot apply the actual close once:

- a new failure with a surviving original block owner returns to a with
  generation g+1 and saved rank a;
- a new failure with no surviving block owner advances to b with the SAME
  generation and saved rank b;
- no new failure advances to b without an archive.

The close supplies that last slot's next signal; it does not append an
extra fictitious pre-close signal. A nonarchiving completed block is read
from its retained successful image. Samples and reveals advance one rank,
using their retained public results; a failed reveal adds its owner to E.
Both set the saved rank to the new cursor. This FORWARD scan reconstructs
the public controls instead of subtracting exclusions from the final set.
It also covers periods with no native callback to the owner.

For the current attempt stop that scan at its saved entry a. Append the
no-new-foreign-miss prefix [a,r): excluded slots are automatic, active foreign
slots use arbitrary supported domain fillers with missing=false, and own
slots use the retained VIRTUAL declared values. No sample or reveal is
crossed. Public projections are P(c), exclusions remain the saved E, and
generation/saved-rank controls are (g,a). Foreign fillers cannot change
the owner's typed view or this logical signal word. Its length counts
source instructions, not native WAIT callbacks.

The resulting key retains the owner, event and generation, the CURRENT
typed virtual view with its history erased, and this entire PAST PUBLIC
signal word. Current own private cells and original private inputs remain;
they are not replaced by P. Old voided private words are never reconstructed.
Precisely, the scan produces the complete newest-first public signal recall,
including its current head. Form the erased information with the current
virtual typed observation/control as head and the TAIL of that scanned
recall as its past. This counts the current signal exactly once.

To prove that the key is in K_j, replay genuine source instructions from
the SAME supported original setup draw. Decoded ordinary moves and recorded
omissions are in the full source menu. A surviving owner's live bad native
binding has not been revealed, and no completed guard could have read it;
replacing it by its virtual domain representative therefore changes no
earlier public result. Voided replacements also change no public result.
Public samples use the same supported atoms at the same public environment.
Finally replay the current no-miss prefix. Erasing this genuine full source
information gives exactly the constructed key. Different hidden fillers or
retired private witnesses give the same label. The erased label itself need
not be played information or equal a decoder factory's chosen full history.

This chronology, rather than equality of saved/current views alone, proves
native measurability. Following a reset, two runs differing only in voided
own choices have the same reduced key. The SAME original table therefore
gives literally identical later choices in the reset coupling.

The induction invariant for this reconstruction is stronger than endpoint
agreement. Use the actual compiled MAXIMAL phase partition. After consuming
each completed phase/attempt record, there is a genuine source prefix from
the SAME supported setup draw with all four properties:

1. Its cursor, generation, saved cursor and current/saved exclusions are
   exactly those of the forward scan.
2. Its entire public signal recall is the scanned word: the pre-setup signal
   occurs once and each source instruction contributes its actual next
   signal, including the last instruction's close.
3. Its current and saved focal typed stores are the virtual stores, with
   original setup cells unchanged. Any old private word remains only in the
   genuine witness and is removed when applying E.
4. Consumed native archives are exactly the chronological prefix, with
   every original full attempt identifier used once. A retry or exhausted
   close consumes its completed archive; success consumes its retained image.

Initialization supplies the genuine setup step. In a commitment block,
static source order and the completed acceptance/omission mask give the
intermediate transitions. Both source and native close inspect the same
original phase-owner set and ending exclusions, so they choose the same
retry, exhausted or successful branch. An accepted handle with a deferred
bad value is not misread as an omission. Within the block, saved exclusions
remain at the entry set while current exclusions accumulate misses. The
last-slot close installs the ending set as BOTH current and saved exclusions,
including on retry and exhaustion. A sample or reveal likewise installs
its updated exclusion set in both fields and consumes its
actual retained public result; no reset has discarded a public cell.
These cases preserve the invariant, including across periods with no focal
callback. At the current ready binding, compiled own-order supplies the
completed own predecessors. Only the unfinished commitment prefix uses
arbitrary foreign fillers; old successful public openings retain their
original constraining values. The genuine no-new-miss replay then gives
the current witness and its erased key. Thus the invariant proves both
observable determinacy and membership in the genuine query image; neither
is an assumption supplied by a chosen source endpoint.

### Choosing the native scales after the source profile

After this source equilibrium has been selected at stage n, let rho_n<=1
be its minimum positive action/chance atom. One explicit native choice is

    zeta_n = rho_n^(T+1)/(n+1),       M = 3T+1.

Both required ratios then vanish:

    zeta_n/rho_n^T = rho_n/(n+1) -> 0,
    zeta_n^M/(zeta_n^3 rho_n)^T = rho_n/(n+1) -> 0.

Fixed menu constants only multiply these ratios. Thus the source fixed
point is chosen before the native scales, and the charged comparison does
not require selecting a source equilibrium after observing native beliefs.
The enlarged formal source fixes beta_n before its source fixed point as
well, as detailed below; its full rho_n includes beta_n. Scale separation
alone does not replace the extension and repair arguments.

For a free conditional-value source agent, the common reset term also gives
the phase-success comparison. Differences between its nonmissing values are
Pr_n(Phi | I) times their conditional successful-phase value differences,
with an additional common positive own-survival factor if the owner has
later bindings in the same phase. Fixed omission and accepted-failure rates
make that factor value-independent. In the no-reset branch a later own
omission or standing accepted failure gives a_j. In a reset branch an
accepted failed binding can be rescued and belongs in the common reset
term, rather than being assigned a_j merely because it was chosen.
If the multiplier is positive, its exact constrained best response ranks
these values by the latter differences, even if the multiplier tends to
zero. The forced honest agents use honest conditional optimality in the
limit; at doomed agents the successful-phase payoff is the same for all
current values. Known-failed pins have a zero multiplier.

### The formal source's extra accepted-failure action

The larger formal binding menu has three disjoint cases: a domain value,
an accepted failed binding, and an omitted binding. The second is not a
native RAW action and is not an omission. Construct the pooled source
profile directly on this menu. Before the fixed point, choose the same
value-independent omission rate alpha_n=eta_n and a value-independent
accepted-failure rate

    beta_n = gamma_n^(T+1)/(n+1).

After no omission, use beta_n for accepted failure and (1-beta_n) tau for
the conditional domain law. Only tau is optimized. Erasure and F share
these prescribed rates as well as tau. The earlier honest-belief bound
still applies: beta_n=O(eta_n), and all three classes have positive mass.
No equality with a separately chosen domain-only extension at every
off-path information set is required.

A standing accepted-failure binding makes its owner own-doomed. If it is
from a retained earlier phase, no current reset can remove it, and eventual
payoff is a_j. If it belongs to the current commitment attempt, either it
stands and eventually excludes its owner, or a foreign miss voids that
binding AND all of the owner's new values. The reset distribution ignores
those values, and erased continuation play ignores them after restore.
Thus all current domain choices have the same payoff in this own-doomed
case, even when rescue is possible. Such classes may use uniform domain
pins. A live bad binding remains in the retained typed view, so these pins
cannot constrain an ordinary non-doomed member of the same pool.

### The original attempt stopping lemma

Fix a genuine active commitment information set I of j. Let [a,b) be its
maximal commitment block, r its current source rank, E_0 the exclusions at
this attempt's saved entry, and g its generation. Retain the actual processed
prefix of this attempt. Suppose every own commitment already present at its
saved entry holds a typed value; guard acceptance is not needed for this
lemma. Write Y_v for the ORIGINAL terminal payoff after forcing current
domain value v and then using the selected E/F-shared continuation. All
random variables below are realized using the same initialized occurrence
flags, domain table, setup and Nature draws.

The first exit from the full attempt identifier (a,g) is exactly b-r source
transitions away. Before the last slot, a supported step advances the cursor
by one, keeps the saved cursor a and generation g, and has no reveal or
sample. The final slot applies the real close in that same transition.
Clean close changes the saved cursor to b; retry changes the generation to
g+1; exhausted close changes the saved cursor to b even though g is unchanged.
Thus none of these cases can be confused with an interior step. This proves
the claim by induction on b-r, directly from the original transition rule.
In particular the stopped window contains no action from a retry. One may
instead stop earlier at j's exclusion: its terminal payoff is already fixed
at a_j, and the success indicator below is false there.

Concatenate the retained processed prefix with these remaining commitment
steps. Induction over the block gives its actual typed attempt: at each slot
an excluded owner takes the automatic transition; an active owner contributes
its actual typed result and its separate omission bit. Deferred guard
rejection is not an omission or an accepted failed typed result. This
extracts the attempt from the supported run; it does not posit a separate
attempt with a matching endpoint.

Let X be a remaining focal omission, F any foreign omission in this original
attempt, including its processed prefix, and B an own accepted failed typed
result in its processed prefix or strictly AFTER the forced current choice.
Set D = X^c intersect F^c intersect B^c. Under a forced domain choice,

    1_D = 1{E_stop = E_0 and every own commitment at stop holds a value}.

Indeed, the growing exclusion set is E_0 union the owners who actually omit.
If it grows, the right side is false through clean, retry and exhausted
readback alike: close never removes an exclusion. If it does not grow, close
leaves the completed typed store unchanged. An own failed typed cell then
persists throughout the block, whereas every own nonfailed result appends a
value; freshness prevents overwriting an earlier failure. The assumed saved
own cells supply the base case. This proves both directions. The right side
uses the ORIGINAL E_0, not the new saved exclusions after restore. It is a
function of the erased stopped state and therefore survives private-word
erasure. A guard-rejecting domain value still counts as a value here.
For the comparison with current accepted failure, D continues to mean this
same event of the OTHER occurrence flags, defined in the forced-domain
experiment. In the accepted-failure experiment the current failed cell makes
its stopped-state success readout false; the displayed readout identity is
not asserted for that experiment.

Now compare any two forced nonmissing current choices, including accepted
failure. Couple their O/B occurrence flags. Until the end of this original
block the public exclusion scan is the same: it reads omission flags, never
private values. Every nonfocal full observation is the same, so couple its
actual choices identically. Later focal domain choices may differ; nothing
requires equality of draws at those different private queries. If X occurs,
both payoffs are a_j. Otherwise j survives. If F occurs, the real close must
be a retry, since the block contains surviving owner j. It restores the same
entire saved semantic state, retains the same full public signal word, and
voids all changed bindings and obligations. The remaining private differences
are exactly retired own words. E removes them, and the chosen continuation
has the same erased query and terminal kernel. Denote this common payoff by
R. This is an equality under the original experiment, including the entire
post-retry continuation, not a freshly drawn entry law.

This also proves the known-failed attachment claim. At such a member F has
already occurred. Every current nonmissing action is consequently indifferent:
either X pays a_j or retry gives the same R. This argument holds for each
history of its own genuine information fiber, so integrating its ACTUAL
belief suffices. No Bayes identification with its no-new-miss representative
is asserted. Current omission is compared separately with the payoff floor.

For ordinary members with equal E keys, use the original information-fiber
bijection and its normalized Bayes cancellation. Under corresponding forced
values their complete erased stopped states and terminal payoff laws agree.
The displayed erased-state readout therefore gives equality of the JOINT
law (1_D,Y_v). Normalizing its D component proves common H_K whenever its
mass is positive. Equality of the unconditional Y_v laws alone would not
justify this conditioning. A member with an own failed prefix has D empty;
its no-reset payoff is a_j and its reset branch is still common.

The exact decomposition uses the initialized occurrence coins, not assumed
equality of draws at different private keys. Condition on a genuine source
information I and force a current DOMAIN value v. Let X mean a future own
omission in this attempt, F mean a foreign omission in this attempt
(including one already observed), and B mean an own accepted failure in its
processed prefix or after the current choice. Define
D=X^c intersect F^c intersect B^c. On X the owner is excluded
and receives a_j. On X^c intersect F, j survives the real close, so it is a
retry: all changed new values and obligations are erased, the same actual
public signal/failure word is retained, and the erased continuation is R.
An exhausted restore cannot be in this branch since j survives. On
X^c intersect F^c intersect B the failed binding stands and payoff is a_j.
On D let H_v include the entire later continuation, with its later resets
and failure trembles unconditioned. Then

    C_I = a_j Pr(X) + E[1{X^c intersect F} R]
          + a_j Pr(X^c intersect F^c intersect B),
    lambda_I = Pr(D),
    U_I(v) = C_I + lambda_I E[H_v | D].

Interpret the last term as zero when lambda_I=0. C_I and lambda_I are
independent of v. For a CURRENT accepted-failure choice b, the same coupling
gives U_I(b)=C_I+lambda_I a_j; a current omission gives a_j. In particular,
future accepted failures that a retry rescues are inside R, not the
payoff-a_j branch. At a known-foreign-failed attachment lambda_I=0, so all
nonmissing current choices are exactly indifferent. If a current-attempt own
bad binding is already present, D is empty and the no-reset payoff is a_j
for every subsequent domain v; no conditional expectation on D is needed.
If an earlier retained phase contains the bad binding, every branch gives a_j.

This identity holds for every admissible E/F-shared continuation profile
with fixed failure rates. It does not hold for arbitrary full-information
continuations that remember voided values. It is established before taking
the pooled fixed point or using future optimality. Since every source
terminal payoff is either a_j or at least m_j>a_j, R>=a_j pointwise.

For source sequential rationality alone there is a shorter failure comparison.
The same terminal floor gives H_v>=a_j under ANY continuation, even if a
domain value or a later domain choice violates a guard. Therefore
U_I(v)-U_I(b)=lambda_I*(E[H_v | D]-a_j)>=0 whenever lambda_I>0;
when lambda_I=0 both nonmissing choices have the same reset value. Current
omission and reveal withholding pay a_j and cannot improve on any legal
continuation either. Thus the failure-action part of source optimality uses
the terminal floor and the exact common-reset identity, without assuming
future SE or a guard-safe continuation. The ordinary domain-gain equality,
attachment pins and honest-pin preservation are still required. The stronger
conditional successful-phase ranking used by native transport additionally
requires the D identity; unconditional gain equality does not replace it.

### Honest pins and successful-phase conditioning

Here is the honest-limit argument before conditioning on D. Let sigma^H_n
be the GIVEN honest consistency sequence. At each embedded honest site,
use the already prescribed omission and accepted-failure branches, with
their fixed rates alpha_n and beta_n, and the domain-floor mixture of its
lifted honest law. These give a retained honest coefficient at least
q_n=(1-alpha_n)(1-beta_n)(1-floor_n); they do not redistribute the fixed
failure masses. These are legal coherent pins because the reduced key
reconstructs the original honest full information. They do not depend on
the later optimized free laws.

For every honest raw atom, its pinned probability is at least q_n times
its honest probability. With p players and a fixed horizon T, multiplying
the actual initialized transition factors gives domination of the ENTIRE
mapped honest-history law at every time t<=T by c_n=q_n^(p*T). The original
setup and chance kernels are identical, and c_n tends to one.
Taking limits in each current-law inequality shows that every retained
limit atom is at least its given honest limit atom. Both laws have mass
one, so equality holds on the honest menu and all extra limit mass is zero.

Fix an original honest information value i and its embedded full-information
value I. Its full signal-word length fixes the decision time. Let h_n(i)>0
be its mass at that time in the given honest sequence, and let
delta_n=1-c_n. The domination splits the actual history measure into
c_n times the mapped honest measure plus a nonnegative residual of total
mass delta_n. Inside I the residual is at most delta_n, whereas its honest
component has mass c_n*h_n(i). Hence the L1 distance between the actual
Bayes belief at I and the mapped honest Bayes belief is at most

    2 delta_n / (c_n*h_n(i)).

The source scales were chosen to make this tend to zero for every honest
i, before the free completion. Here h_n(i) is an ORIGINAL honest reach,
not a reach probability of the optimized extended game. This retains the
given honest belief even where its limiting reach is zero.

At the limit, forcing a legal honest current law and following the pinned
continuation has precisely its original honest continuation value. Honest
sequential rationality therefore compares all these laws at the retained
belief. An extra current binding action either is omission or leaves a
failed or rejected obligation; with foreign omission rates zero in the
limit, there is no foreign reset to remove it. It eventually pays a_j.
Reveal withholding likewise pays a_j. Every honest terminal continuation
pays at least a_j, so each extra action is weakly dominated by an honest
comparator. Linearity now gives the local best-response inequality on the
entire raw menu. This establishes honest-pin optimality without assuming
that the fully mixed honest approximants themselves are best responses.

At an ordinary honest-compatible site there is neither a processed foreign
miss nor an own failed typed prefix. After forcing the current DOMAIN choice,
D concerns only unused occurrence flags: O at each remaining entry-active
slot strictly after the forced current action, and B at each remaining focal
slot strictly after it. On D the active roster never
changes, so these sets of coordinates are fixed by the public occurrence.
Their independence from the entire genuine past gives, with r_O and r_B
the respective numbers of remaining slots,

    lambda_I = (1-alpha_n)^r_O (1-beta_n)^r_B,
    1-lambda_I <= T(alpha_n+beta_n) -> 0.

This is a source-attempt statement, not a bound on native Phi. If Y has
payoff range of width S_j, the elementary mixture identity gives

    |E[Y | D] - E[Y]| <= S_j(1-lambda_I).

Consequently the conditional domain regret of an honest pin is at most its
unconditional domain regret plus 2 S_j(1-lambda_I). The relative departure
bound above makes the latter converge to the given honest assessment's
regret for honest legal choices. A current violating value either is voided
by a foreign miss, whose probability tends to zero, or leaves a retained
invalid obligation and payoff a_j; it cannot improve on honest play. This
proves the required honest conditional-success comparison without dividing
by a rare probability or assuming that the honest consistency approximants
are themselves best responses. Known-foreign-failed attachments have D empty
and use indifference instead. Native Phi may remain arbitrarily rare and
still requires the separate relative transport argument.

### Concluding source sequential rationality

Let S_j bound the full terminal payoff range and d bound the domain menu.
At a free ordinary member, exact pooled optimality gives conditional-D
domain regret at most d gamma_n S_j; multiplication by lambda_I<=1 gives
the same bound for unconditional domain regret. This holds equally for the
implemented sum of CONDITIONAL member utilities: its coefficient is
pi_K sum_I lambda_I, with no reach weights. Its exact positive coefficient
cancels before taking a limit. A zero coefficient and known-failed or
own-doomed pinned members use the action-independent branches proved above.
Honest members use the preceding preservation and conditional-success bound;
their finitely many domain regrets tend to zero.

For any of these members let U_tau be its conditional domain-mixture value.
The terminal floor and common reset give U_tau>=U_b>=a_j, where U_b is the
value of current accepted failure. The actual current mixture differs from
the domain mixture only through omission mass alpha_n and accepted-failure
mass at most beta_n. Thus its value is at least
U_tau-S_j(alpha_n+beta_n). Every current raw action consequently has gain
at most the domain regret plus S_j(alpha_n+beta_n). Reveal withholding has
value a_j, so its fixed-rate mixture has regret at most S_j alpha_n as well.
These inequalities concern the actual original full-information beliefs
and continuation values; no quotient-player rationality is substituted.

Take one convergent subsequence of the finite collection of source profiles
and their Bayes beliefs. Full mixing supplies consistency. Finite terminal
expectations are continuous in the behavioral profile and the beliefs, so
the vanishing one-shot regrets give sequential rationality at every original
information set. Perfect recall upgrades this to all continuation deviations.
Honest-pin preservation identifies the requested honest joint law on paths.
This completes the mathematical source selection argument; its formal
stopped-window, attachment and honest-pin consumers are still obligations.

### The stronger guard-safe continuation bound

The following stronger m_j-o(1) bound uses guard viability; the weaker
terminal floor and common reset already suffice for the failure-action
part of source sequential rationality.

At a non-doomed information set, omission gives a_j. For accepted failure,
the no-reset branch gives a_j and the reset branch has the common erased
continuation. A guard-safe domain value has that same reset branch and
keeps the owner non-doomed on the no-reset branch. Establish this STRUCTURAL
decomposition first for every admissible constrained profile. Exact free
domain best responses then cancel the common reset term and the common
positive no-reset/own-survival coefficient in payoff DIFFERENCES. Backward
induction on the remaining own decisions gives conditional no-reset value
at least m_j-o(1): honest pins are guard-safe, free members maximize that
conditional ranking, and the total conditional forced-draw error is
O(T(alpha_n+beta_n+C gamma_n)). No-reset conditions only fixed foreign
omission coins; future phases are unconditioned and use the ordinary
finite-horizon induction. Own-doomed pins are outside this lower-bound
induction. Thus accepted failure cannot improve the limit payoff.
At an already-known foreign-failed
attachment every current nonmissing choice is voided, including accepted
failure, so it is indifferent; its coefficient is zero and is never divided
out. Together these comparisons justify taking
beta_n->0 in a sequentially rational limit of the full-menu construction.

For clarity, the induction's safe action requires more than a typed
nonfailure menu entry. Here non-doomed means that no retained own obligation
is already invalid. The standing guard-satisfiability assumption supplies
an owner-observable accepted value at every relevant reachable commit;
choosing it preserves own validity. Correctly opening then satisfies every
completed own obligation. Preservation uses the guard's read scope: every
read was already available at its commit, existing bindings are immutable,
and the reveal completing the obligation belongs to the same owner. Fresh
bindings cannot change an earlier accepting assignment; failed inputs make
the corresponding compatibility test vacuous. A restore drops the new
obligations together with their cells and retains the valid saved ones.
Thus arbitrary foreign moves do not invalidate a safely retained own
obligation. A typed domain action with a deferred rejecting
guard is not a safe action. Satisfiability only on intended-reachable
histories would not by itself justify this use after exclusions.

The conditional induction also keeps the right beliefs. If J is a later
full-information set of this owner after forcing a current own action,
perfect recall fixes that action and its earlier information throughout J.
Its positive likelihood factor is therefore common to every history of J
and cancels from its Bayes posterior. Already processed omission flags are
in the genuine sequential public scan; already processed own failure flags
are in own recall. Remaining success conditions fix UNUSED occurrence
coins, whose laws are independent of the hidden world. At J, the same
conditional-ranking argument applies with the same prescribed domain law.
Induct over remaining own decisions within the block, and use the ordinary
unconditioned induction after a successful close or retry. A safe action
preserves validity; the floor draw, omission and accepted-failure branches
cost at most S_j*O(T(alpha_n+beta_n+C*gamma_n)). This proves the stated
m_j-o(1) bound without conditioning a previously obtained error estimate
on a rare success event.

The induction parameter is the remaining height of the bounded ORIGINAL
source tree, including retries, rather than the static instruction rank.
Every successor, including a retry, has smaller height. At height zero a
non-doomed surviving owner receives at least m_j. For the induction step,
compare the exact conditional domain optimum with a guard-safe value.
On successful progress the next non-doomed query has the induction bound;
on retry the saved non-doomed state has that bound. Only the forced floor
and failure branches incur the bounded payoff-spread loss. Within a block,
condition on its remaining occurrence coins before making this comparison.
They fix neither hidden values nor unused future domain answers; at a later
own query, already processed coins are known and the unused ones retain
their fixed laws. The no-new-miss pins ensure that the selected domain law
is unchanged if a sequential presentation reveals a foreign miss earlier.
Thus the very same conditional comparison is available at every successor.
This proves the induction estimate directly under the required conditioning;
an unconditional error estimate subsequently divided by success probability
would not prove it.

There is also a separate RELATIVE deletion argument for transport. Consider
foreign owners active at I and paths satisfying Phi through the original
commitment attempt. Any earlier accepted-failure binding of such an owner
was either voided or has not been revealed: revealing it would already
have excluded that owner. Replace ALL of these bindings by fixed domain
values, leaving original inputs, other domain choices, omissions, public
samples and source occurrences unchanged. A guard reading a changed
binding cannot have completed: guard evaluation waits until its subject
and every commitment read are revealed. A voided guard was discarded.
Thus the same public record, focal information and Phi are retained.
The replaced owner's later private queries and doom status MAY change.

Do not equate its kernels at those different queries. Instead lower-bound
the WHOLE repaired domain trajectory by its uniform floor. Omission and
opening factors cancel because their rates depend only on fixed old-entry
control; other owners' information and factors are unchanged. There are
at most T affected domain factors, and the first accepted-failure atom in
the original path contributes beta_n. Eventually the path ratio is at most

    2^T beta_n gamma_n^(-T).

The deterministic repair has finite multiplicity. Summing within the SAME
I-and-Phi event proves a relative bad/regular mass bound tending to zero,
since beta_n/gamma_n^T=gamma_n/(n+1)->0. This repairs foreign active owners;
it is not a deletion of the focal owner's known bad binding. Excluded-owner
choices keep their actual weights. Exhausted restore does not invalidate
the argument: its exclusions/branch are retained and no additional reveal
is inserted before the measured old attempt exits.

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

The reduced-coordinate original plan and its full source history law are
checked by `Vegas.SourceProgram.Setup.commitRecoveryErasedPolicyPlan_run`.
`Vegas.SourceProgram.Setup.commitRecoveryErasedPolicyPosterior_split` checks
the current-coordinate/entire-original-remainder split after genuine records;
those records correspond to the original full-information own play. Genuine
no-miss replay and erasure of instruction/retry/exhausted closure are also
checked. These results do not yet construct the pooled source equilibrium or
identify native observations with the reduced source query.
`Vegas.SourceProgram.Setup.commitRecoveryErasedProfile_terminal_joint_eq`
also proves the actual joint terminal typed-readout and payoff-vector law for
the concrete erased prescription from two genuine histories with equal erased
semantic/information summaries.
`Vegas.SourceProgram.Setup.commitRecovery_failed_attempt_erased_eq` derives
the required summary equality for two genuine failed source attempts from the
same literal prior and omission word, through retry or exhausted close.
`Vegas.SourceProgram.Setup.commitRecoveryErasedProfile_failed_attempt_terminal_joint_eq`
then gives their actual joint terminal law. The corresponding physical native
relation remains open.

`Vegas.SourceProgram.Setup.commitRecovery_info_eq_of_public_and_coordinate`
now reconstructs complete original owner information from the literal setup
prefix, full public chronology and the owner's raw coordinate word.
`Vegas.SourceProgram.Setup.commitRecovery_history_eq_of_public_and_joints`
gives original history uniqueness from those public and complete joint records.
`Vegas.SourceProgram.Setup.commitRecovery_metadata_of_publicRecall` derives
the current/saved registry, revelation and control agreement from actual
public recall, allowing distinct original supported setup draws.
`Vegas.SourceProgram.Setup.commitRecovery_counterfactual_reach_eq_of_public_and_coordinates`
and `Vegas.SourceProgram.Setup.commitRecovery_reach_cross_mul_eq_of_public_and_coordinates`
give the global paired reach identities, retaining original Nature atoms.
`Vegas.SourceProgram.ProtocolState.recoveryStep_splice_support` constructs
the raw supported owner-spliced successor.
`Vegas.SourceProgram.Setup.commitRecovery_step_splice_support` composes that
support with the actual real close, without a supplied raw-result equality.
`Vegas.SourceProgram.Setup.commitRecovery_hybrid_of_initial_inputs` constructs
a UNIQUE original supported hybrid history from two actual initialized source
prefixes with matching public records and focal hidden tuple. It preserves
the focal full information of one trace, every nonfocal full information of
the other, the latter's literal setup draw and its exact counterfactual reach.
`Vegas.SourceProgram.Setup.commitRecovery_initial_hiddenAgree_of_query_eq`
derives that original hidden tuple agreement from actual combined query
equality at literal initialized prefixes; no independent prior is introduced.
`Vegas.SourceProgram.Setup.attemptPublicRecall_eq_for_observer` transfers
the entire public record between observers.
`Vegas.SourceProgram.Setup.commitRecovery_information_fiber_equiv` gives an
actual bijection of original information histories at equal erased keys.
`Vegas.SourceProgram.Setup.commitRecovery_bayes_eq_of_erasedInformation_eq`
then transports the actual normalized Bayes belief exactly, using positive
constant own reach and unchanged counterfactual reach. The original joint
setup law may be correlated. Combined-key known-failed attachments do not
use this bijection. Actual ordinary-copy continuation values and gains are
checked in `Vegas/Game/CommitRecoveryAncillaryGains.lean`, retaining the joint
stopped mark and terminal readout/payoffs. The conditional-success
specialization and individual source optimality remain open in Lean.

`Vegas.SourceProgram.Setup.commitRecovery_stopped_attempt_success` now extracts
the literal typed attempt from the actual first-full-identifier stopped source
word and proves its original-entry exclusion/own-value success marker. It uses
fresh context names and valued current own-prefix cells. The marker is stated
for domain forcing; it does not reinterpret a forced current accepted failure
as a successful typed boundary.
`Vegas/Game/CommitRecoveryHonestPins.lean` derives honest pin coherence from
actual query equality. The actual prescription and initialized-run domination
in `Vegas/Game/CommitRecoveryHonestDomination.lean` give honest Bayes convergence
in `Vegas/Game/CommitRecoveryHonestBeliefs.lean`, at scales tied to the original
honest sequence before free completion. These do not yet prove the full source SE.

`Vegas.SourceProgram.CommitRecoveryState.step_preserves_intendedFor` keeps a
surviving player's existing validity predicate in current and saved states
through actual recovery and close, with arbitrary foreign actions. Its
current guard-satisfiability hypothesis is explicit; it does not derive
all-reachable viability from intended-only setup well-formedness.
`Vegas.phaseCountServiceTapePolicy_foreign_survivors_law` compares the actual
first-exit survivor-vector laws under arbitrary focal policies with the same
supported original zero-RAW timing table and foreign seeds. This supplies
proper-reference scalar survival. `Vegas/Game/PhaseCountServiceGood.lean` gives
the positive-RAW joint good event for the same original supported tables;
`Vegas/Game/PhaseCountServiceTableGood.lean` averages the literal original table
posterior and retains the entire table vector. Typed-word transport and the
original full native information-fiber posterior remain open.
`Vegas.compiled_reveal_public_exclusions` reads the source public exclusion
update from the actual immutable native publication at its original compiled
suffix. The full native observable query remains open.

`Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_genuine_history`
gives a genuine source witness for the no-new-miss transformation of every
original query, preserving nonterminality. Its idempotence, erasure commutation,
menu transport and combined-query clock preservation are checked in
`Vegas/Source/CommitRecoveryNoMissRepresentative.lean`.
`Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_failed_attempt_terminal_joint_eq`
establishes the same actual reset continuation law for the legal profile reading
that combined query. These are source constructions, not a native decoder.

`Vegas.SourceProgram.Setup.commitRecoveryValueTremble_fullSupport` checks the
all-query legal three-case perturbation, including reveal withholding;
`Vegas.SourceProgram.Setup.commitRecoveryTrembledProfile_plan_run` checks its
entire full-information source run law. The separate domain table is realized
by `Vegas.SourceProgram.Setup.commitRecoveryDomainPlan_run`. Its native
posterior adapter, `Vegas.SourceProgram.Setup.commitRecoveryDomainPlan_posterior_split`,
retains the actual entire remainder but requires an actual-response non-reading
proof. These are erased-coordinate results: the final no-new-miss sharing
and the native response premise are not supplied by those run-law identities.
`Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_run` separately realizes the
entire original source law from ONE initialized public-occurrence flag array
and independent erased-query domain table. Its genuine-record posterior leaves
the current three-class choice unchanged.
`Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPlan_run` reads that
SAME initialized prior at the combined key E(F(info)) and proves its entire
ORIGINAL source run law. Genuine combined-query membership and logical-clock
preservation give the exact current/whole-record product and original-record
posterior. The original game's perfect recall is used; no recursively defined
normalized signal model or entry refresh is introduced. No equality with the
independent full-choice private-table joint is asserted.

`Vegas.SourceProgram.Setup.exists_consistent_commitRecovery_normalized_pool`
selects shared query weights using the existing component completion. Its
actual source assessments are fully mixed and Bayes consistent, converge to
a consistent limit, and satisfy the summed actual conditional gain bounds.
The SAME initialized normalized flag sampler realizes their complete source
runners. The honest pins and their Bayes convergence are now constructed as
described above; each member's individual source optimality is still separate
from this pooled existence theorem.
The owning completion sums conditional member gains. After the same ancillary
and reset identities, its domain comparison has coefficient
pi_K*sum_I lambda_I, rather than the ex-ante coefficient
pi_K*sum_I r_I*lambda_I above. Both are nonnegative and vanish only when all
positive-reach ordinary members have zero success coefficient. Exact
cancellation therefore gives the same individual conditional bound; no new
fixed-point machinery is needed for the different normalization.
`Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_failed_attempt_terminal_joint_eq`
derives the whole omission word from actual complete pure-member records and
the SAME sampled flags before consuming the genuine failed-attempt close.
It proves the joint terminal readout/all-player-payoff equality through retry
and exhausted restore without assuming equal omission words. The global
history paste supplies original support and its inverse uniqueness; actual
information-fiber Bayes cancellation is checked as described above. The
original local stopped window and its raw typed success readout are now checked.
Its joint conditional-D/payoff specialization and individual source optimality
remain open in Lean.

The existing broad post-exclusion native completion is not the pinned
construction above:
a focal expiry can change another owner's still-pending old-phase value
before reset. Nor does its ordinary source-policy carrier automatically
identify distinct recovery occurrences. The arbitrary controller contract
also does not enforce the strong service packet quotient used above. These
differences must be resolved before an implementation of the mathematical
construction is reported as full SE preservation.

The formal accepted-failure tier requires the enlarged pooled construction
and WHOLE-owner relative repair above. Conditioning merely on no omission,
or using the continuing menu, is insufficient. Its beta_n must stay distinct
from native zeta_n^3. The full source minimum rho_n includes beta_n and
cannot replace gamma_n in the source repair bound. Individual rationality of
the enlarged source construction, owner-density cancellation, native
chronological readback and the whole-phase service induction still require
checked Lean realizations.

The safe-value induction also requires a formal guard-viability adapter at
every non-doomed recovery view it uses. Mere domain-menu nonemptiness, or
satisfiability only at intended-reachable histories, does not supply that
scope. The mathematical argument uses the standing all-reachable-history
guard-satisfiability assumption and owner-observable guard predictions.
