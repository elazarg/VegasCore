# Finite causal transport of a common equilibrium sequence

This document proves the probability and incentive transfer used by the
[publication-barrier route](se-private-mempool-proof-routes.md). It separates
three claims that require different hypotheses:

1. the projected physical runner has the same law;
2. an actual information-set posterior is a mixture of the correct fine
   posteriors;
3. every literal one-step deviation has the corresponding projected continuation
   law.

The second and third claims are necessary for equilibrium. The first alone is
insufficient. All results here are mathematical derivations, not newly checked
Lean declarations. The runtime-specific candidate mask is the subject of
[the native adapter](se-publication-native-adapter.md); its required contract
is stated explicitly below rather than assumed from equality of emitted packets.

## 1. Fixed finite games and notation

A probability distribution on a finite set X is written as a nonnegative
function of total mass one. Every sum below is finite. A finitely branching bounded initialized model has
a finite reachable tree; its finitely many reachable observation alphabets can
be replaced by their finite union without changing the game. Global finiteness
of an unused ambient packet type is unnecessary. Use arbitrary real
terminal utilities; finiteness makes every expectation finite.

The player set is finite. The physical game is a finite rooted tree H with
terminal set Z and height at most D. A nonterminal history is either a Nature
history or a history with one acting player. This single-mover formulation
matches the reactive runtime: a callback has one responding owner. It does not
assert a new theorem about simultaneous moves with signals between their
components.

At a Nature history h, the fixed kernel kappa_h is a distribution on its
immediate children. At a history h where i acts, the legal effective action
set is C_i(t_i(F_i(h))). After action c, the fixed kernel kappa_{h,c} is a
distribution on children labelled by that chosen action. Thus the physical
history remembers effective own actions even when their wire representation is
opaque to other players. An arbitrary correlated prior is represented by the
initial Nature branch. A correlated service tape may be included in that branch
and retained in the hidden physical state. No factorization between players'
types, or between different service times, is assumed.

For the runtime scheduler mixture, one can simply retain the environment
recall in h and use its actual history-dependent command kernel. Complete and
private reception then give that kernel the same retained public arguments.
Alternatively, use the existing latent-tape realization before introducing a
hidden initial tape. Neither presentation resamples the tape, replaces its
posterior by its prior, or asserts independence of future service after
conditioning on a private information set. The separate complete-reception
compiler theorem may impose an exogenous-tape premise; this transfer theorem
does not remove that premise from the application.

For each player i:

* F_i is its finite set of fine decision-information values, and F_i(h) is
  defined when i acts at h.
* T_i is a finite set of menu/policy labels; t_i:F_i->T_i.
* C_i(t) is a finite nonempty set for each reachable t. These are dependent
  menus, not one universal action set silently available everywhere.

Fine information has decision recall: if F_i(h)=F_i(h'), the ordered list of
previous own decision-information values and selected effective actions is the
same. Denote that list by

    spine_i(F) = [(F_0,c_0),...,(F_{m-1},c_{m-1})].                 (1)

Each c_k belongs to C_i(t_i(F_k)). The current F is not on its own earlier
spine. Consequently each fine information set is an antichain. The actual game
will also have decision recall and antichain information sets.

A terminal observation O:Z->Omega and utility u_i:Omega->R are fixed. Omega may
retain the original initial draw, complete typed terminal state and payoff
vector. Equality of O-laws will therefore preserve that initialized joint law,
not just an expected scalar payoff.

All physical kernels, observation kernels, information maps, menus, menu
labels, class projections and terminal readouts are fixed throughout a
perturbation sequence. Only the behavioral policies described in Section 3 may
vary with n. Allowing the game or the reception kernel to vary with n would not
construct a consistency witness for one fixed game.

Zero-probability Nature edges may be removed. If retained in the notation,
identities of unnormalized masses still apply, but beliefs are normalized only
at positive-mass sites. A legal history means one supported by the fixed Nature
kernels and legal strategic choices. Inactive players have the unique null
choice; there is no strategic condition to check at terminal or Nature nodes.

## 2. A causal observation-and-alias expansion

The following gives a constructive producer for the reach factorization. It is
stronger and more useful than assuming the desired posterior identity.

For player i let S_i be a finite alphabet of actual local observations. Let R_i
be the finite set of possible records of at most D pairs (z,a), with dependent
literal actions a as defined below. A current actual information value is

    I = (r,z),   where r=[(z_0,a_0),...,(z_{m-1},a_{m-1})].       (2)

The dependent record family can be constructed by length: R_i^0 contains only
the empty record; a current observation z gives I=(r,z); its given actual menu
A_i(I) supplies the next pairs (z,a). Taking the finite union through length D
defines R_i. This is a well-founded finite construction, not a recursive
assumption about an infinite universal action alphabet.

It retains every earlier actual observation and literal own response. The
current observation z includes any ordinary public/own observation required
by the actual game. In particular, this construction does not make an actor
forget its candidate catalogue or its earlier response syntax.

### Definition 1: the channel

For each fine information value F and earlier actual record r, a fixed kernel

    Lambda_i(F,r) in Delta(S_i)                                (3)

generates the next actual observation. Its meaning is conditional: at every
complete underlying history represented by F and r, the distribution of that
next observation is exactly (3). It is not merely an equality after averaging
over underlying histories.

Equivalently, the actual observation can be generated from F, r and a fresh
private coin. The coin is fresh in this conditional-kernel sense. The symbol z
can depend strongly on the physical state through F. No independence of z from
the state is being asserted. The current stateless pending-observation API
fits after the ordered pending list has been reconstructed from fine recall.

The model samples channels at their owners' callbacks. At a given callback,
other players' records do not change. Ordinary public events that affect future
local observations are already in physical history and hence in the later
fine information value. If an application emits additional private signals
between callbacks, their complete conditional kernel and retained record must
be included in this construction; they cannot be silently omitted.

### Definition 2: dependent actual menus and classes

For each reachable actual information value I, let A_i(I) be its finite
nonempty literal action set and let t'_i(I) be its menu/policy label. Require

    t'_i(I) = t_i(F)                                            (4)

at every compatible pair (F,I). Compatibility means that I can be generated
along a legal fine own spine using the fixed channel and legal earlier aliases.
The requirement is over all legal such histories, including histories after
one-step alternatives; it is not restricted to the limiting equilibrium path.

There is a surjection

    pi_{i,I}: A_i(I) -> C_i(t'_i(I)).                            (5)

Equation (4) transports the dependent type of pi_{i,I}(a) to the fine menu at F.
In formulas below this explicit equality is the only identification of menus.
There is no requirement that literal menus have the same size. Receiving a
certificate may add forwarding aliases while leaving the effective menu fixed.

The actual response a appends (z,a) to r. Its effective physical response is
c=pi_{i,I}(a), and the physical successor is sampled from kappa_{h,c}. Nature
steps use kappa_h. No transition or terminal observation depends on discarded
literal syntax except through the retained record and this effective class.
Future literal menus and channel outputs may depend on that retained own record.

### Definition 3: the native implementation contract

An existing implementation need not literally be presented in the preceding
normal form. To instantiate it, supply a history projection to H and a local
record extraction, and prove the following conditional statements:

1. At aligned response stages, actor and effective menu label agree under the
   projection; aligned terminal stages have the same terminal readout. Auxiliary
   reception stages are Nature-only and introduce no new strategic choice.
2. At a callback, conditional on the entire actual prefix, the extracted next
   observation has kernel Lambda_i(F,r). Any discarded private observation is
   causally reconstructible from F, r and the channel/alias coins.
3. For every available literal response a, the projected physical successor
   kernel is kappa_{h,pi(a)}. Physical Nature successors project to kappa_h;
   the auxiliary reception successors are governed separately by clause 2.
4. The next extracted own record is exactly the append operation in (2).
   Other actors' records are unchanged at this response. Any additional
   implementation state continues to satisfy clauses 1--3.

A probability-preserving bisimulation with these clauses is enough. Matching
only terminal laws, or matching the physical successor while leaving an
unmodelled private signal, is not enough. Clause 3 must hold after every counted
one-step alternative. For the candidate mask, wrong-typed bytes can remain in
literal own memory because they are reconstructible from its earlier own
preparations; they must not create an unmodelled future effective action.

These are transition and observation equations, not an assumption of local
optimality. They permit a different actual alias catalogue at every compatible
history.

### Aligned history fibers

Sampling an auxiliary reception symbol introduces a Nature prefix that does not
advance the physical history. Do not sum all expanded prefixes with the same
projection: that would count both sides of this auxiliary step. Define L^0(h)
as the expanded prefixes at physical h immediately before its next reception
branch, if h is a player node, and at its ordinary aligned stage if h is Nature
or terminal. At a player node define L^1(h) as the prefixes immediately after
that one reception branch and before the response. These are separate cuts.
Each expanded play visiting h crosses L^0(h) once and L^1(h) once. The actual
information value I is read on L^1(h). Terminal comparisons use L^0(z).

A native implementation adapter must give these stage maps, or an equivalent
alignment that directly identifies its active decision prefixes. A many-to-one
history projection without a stage convention is insufficient for a reach sum.

## 3. One fully mixed sequence in the actual game

For every n and player i, let

    b_{n,i}(t) in Delta(C_i(t))                                 (6)

have full support. This is the prescribed effective law. It is available from
fine information through t_i(F) and from actual information through t'_i(I).
This equality is required at every n, including vanishing-probability actions.

For each I and c in C_i(t'_i(I)), choose a splitting kernel Q_{n,i}(I,c) on
A_i(I) such that

    Q_{n,i}(I,c)(a)=0                    if pi_{i,I}(a) != c,
    Q_{n,i}(I,c)(a)>0                    if pi_{i,I}(a) = c,
    sum_{a in A_i(I)} Q_{n,i}(I,c)(a)=1.                         (7)

Surjectivity makes these kernels possible. They can depend on n, on private
receipts, and on literal own memory. Define the actual behavioral profile by

    sigma_{n,i}(I)(a)
      = b_{n,i}(t'_i(I))(pi_{i,I}(a))
          Q_{n,i}(I,pi_{i,I}(a))(a).                           (8)

This is a probability distribution: regroup the sum over a by its class and
use (7). It assigns positive mass to every legal literal action. Moreover,

    (pi_{i,I})_* sigma_{n,i}(I) = b_{n,i}(t'_i(I)).              (9)

The fine effective profile beta_n uses b_{n,i}(t_i(F)) at F. Nothing in (8)
restricts the player's possible deviations. It defines the proposed sequence;
every literal action in A_i(I) remains an alternative to be tested.

## 4. Exact reach weights: no posterior assumption

Write r_n(h) for the physical reach weight under beta_n. It is the product of
initial/chance factors and effective action factors along h. Write
rtilde_n(htilde) for the actual reach weight under sigma_n, including the channel
branches. The current observation branch is included before an actual decision.

### Lemma 1: the local channel kernel given a fine own spine

For F with spine (1), generate a private record without resampling any effective
action:

* set r_0=[];
* for k=0,...,m-1, sample z_k from Lambda_i(F_k,r_k), let
  I_k=(r_k,z_k), sample a_k from Q_{n,i}(I_k,c_k), and set
  r_{k+1}=r_k++[(z_k,a_k)];
* sample z from Lambda_i(F,r_m) and return I=(r_m,z).

Call its distribution K_{n,i}(F) on actual information values. It is normalized
by iterated finite summation of normalized kernels. This definition uses only
F: decision recall reconstructs every earlier F_k and c_k. Compatibility (4)
makes every dependent invocation of Q well typed.

For a specified I=(r,z), K_{n,i}(F)(I) is zero unless r has length m and each
remembered alias projects to the corresponding c_k using the compatible
prefix menu equalities (4). If any required prefix pair is incompatible its
mass is zero; no dependent kernel is evaluated at an ill-typed class. On the
compatible case the mass is exactly

    product_{k=0}^{m-1}
      [Lambda_i(F_k,r_k)(z_k) Q_{n,i}(I_k,c_k)(a_k)]
        * Lambda_i(F,r)(z).                                   (10)

All prefixes r_k and observations z_k are read from I. Thus (10) is constant
on all hidden physical histories h with F_i(h)=F. This constancy is proved
from the channel contract and recall; it is not a conditional-independence
premise about source types.

### Lemma 2: projected path law and focal joint reach

For every physical history h, use the aligned cuts just defined:

    sum_{htilde in L^0(h)} rtilde_n(htilde) = r_n(h).           (11)

At a player node the same identity holds with L^1(h), by normalization of its
one current reception kernel. These two sums are not added together.

At a player-i decision, after its current observation branch,

    R_{n,i}(h,I)
      := sum_{htilde in L^1(h): actualInfo_i(htilde)=I}
           rtilde_n(htilde)
       = r_n(h) K_{n,i}(F_i(h))(I).                           (12)

**Proof.** In the canonical expansion, for an individual aligned expanded
history the multiplication rule is

    rtilde_n(htilde) = r_n(h)
      * product_{completed own decisions (j,F,r,z,a) along htilde}
          [Lambda_j(F,r)(z) Q_{n,j}((r,z),pi(a))(a)],           (11a)

with one extra factor Lambda_i(F_i(h),r)(z) at an L^1(h) prefix.
Here pi(a) is the effective action already recorded on h. An inconsistent
projection has no such lift and contributes zero. Formula (11a) follows by
induction over the actual steps: a reception appends its Lambda factor; a
response uses sigma=b*Q from (8); a physical Nature successor appends its
kappa factor. Thus all b and kappa factors together are precisely r_n(h).
The remaining factors are the channel and alias probabilities. Group them by
player and its own decision order. The focal player's factors are exactly
(10). Every other player's factors sum to one by iterated summation in temporal
order, because its effective actions are fixed by the chosen physical path and
its alias kernel is normalized for that fixed class. The common class law (6)
is independent of its private channel/alias realization; otherwise those
factors could not be pulled into r_n(h).

The same summation over the focal private record gives (11). At Nature nodes
there is no channel factor; at a terminal node all existing private factors
sum out. Alternatively prove (11) inductively using (9), the native kernel
contract and finite distributivity. For a bisimulation presentation, first
sum auxiliary native transitions within each projected successor fiber using
Definition 3; the same products remain. No division is used in this proof, so
zero-probability branches satisfy the identities as well. QED.

Equation (12) is a reach-weight identity. Information sets can contain histories
at different physical depths. One must sum their reach weights on their
antichain, not pretend they are a single fixed-time state distribution.

### Lemma 3: exact conditional posterior mixture

For a fine decision value F define

    m_n(F) = sum_{h:F_i(h)=F} r_n(h),
    mu_n^F(h) = r_n(h)/m_n(F)  for h in F.                     (13)

For an actual information value I define

    M_n(I) = sum_h R_{n,i}(h,I)
           = sum_F m_n(F) K_{n,i}(F)(I).                     (14)

At a supported actual site M_n(I)>0. Define

    alpha_{n,I}(F) = m_n(F) K_{n,i}(F)(I)/M_n(I).              (15)

These weights are nonnegative and sum to one. For F of positive weight, m_n(F)>0
and K_{n,i}(F)(I)>0. The pair (F,I) here is a mathematical partition of histories, not information
given to the actual player. The actual Bayes belief, pushed to physical histories, is

    mutilde_{n,I}(h)
       = alpha_{n,I}(F_i(h)) mu_n^{F_i(h)}(h).                (16)

Equivalently, conditional on the pair (F,I), its physical posterior is mu_n^F.

**Proof.** Divide (12) by (14). For h in F, insert and cancel m_n(F), which is
positive whenever the corresponding weight is positive. Terms with zero weight
are zero and require no belief choice. Equation (14) proves normalization of
(15). QED.

An actual I may mix several fine F. A map from I to one source information set
is not required. Conversely, equality of a source query alone does not prove
(12); the channel and reference-policy factorization is doing that work.

## 5. Every literal one-step deviation

Define the physical continuation law D_n(h) on terminal observations by finite
backward recursion:

    D_n(z) = pointMass(O(z))                                  for terminal z;
    D_n(h) = sum_y kappa_h(y) D_n(y)                          at Nature h;
    W_n(h,c) = sum_y kappa_{h,c}(y) D_n(y)                    at player h;
    D_n(h) = sum_c b_{n,i}(t_i(F_i(h)))(c) W_n(h,c).           (17)

A sum of weighted distributions denotes their mixture. Let
V_{n,i}(h)=E[D_n(h),u_i] and w_{n,i}(h,c)=E[W_n(h,c),u_i].

### Lemma 4: controlled continuation equality

At every actual history projecting to h, its prescribed continuation has
terminal-observation law D_n(h), independently of its retained private record.
At an actual decision I and every legal literal a, forcing a now and then
following sigma_n has terminal-observation law

    W_n(h,pi_{i,I}(a)).                                      (18)

**Proof.** Induct backwards on the remaining physical height. The terminal case
is the readout contract. A Nature step uses the common projected Nature kernel.
At a response, apply the controlled successor clause to the chosen literal
class and the induction hypothesis at every resulting actual successor. For
the prescribed response, sum over aliases using (9), giving exactly the last
line of (17). For a forced literal response, use its single class, giving (18).
All hypotheses hold at every legal continuation, including the successors of
a one-step deviation. This is why agreement only on a prescribed path would
not suffice. QED.

The actual and fine information sets are antichains. Therefore forcing the
current response and following the profile is the same continuation as changing
the behavioral law at this information set: that information value cannot recur
later. This identifies (18) with the library's one-information-set
`GameTheory.Protocol.InformationModel.BehavioralPolicy.withLaw` deviation. The result would be false in an absentminded model without this
qualification.

### Lemma 5: exact gain identity, including dependent menus

For a fine F and c in C_i(t_i(F)), define

    G_n^fine(F,c)
      = sum_{h in F} mu_n^F(h)
          [w_{n,i}(h,c)-V_{n,i}(h)].                         (19)

For actual I and literal a in A_i(I), let G_n^actual(I,a) be the conditional
payoff gain from forcing a instead of its prescribed mixed response. Then

    G_n^actual(I,a)
      = sum_F alpha_{n,I}(F)
          G_n^fine(F, transport(pi_{i,I}(a))).               (20)

The transport uses t'_i(I)=t_i(F), which holds at every positive-weight pair.
Terms with zero weight are omitted; no action is coerced into an incompatible
menu.

**Proof.** By Lemma 4 the history-wise actual gain is
w_{n,i}(h,pi_{i,I}(a))-V_{n,i}(h). Average it with (16), group by F and use
(19). Baseline mixing is identical on the two sides by (6) and (9). Finite
sums permit changing their order. QED.

For a mixed actual alternative nu in Delta(A_i(I)), the corresponding formula
is obtained by additionally averaging (20) over a~nu. Thus mixtures do not
create an untested deviation. The class can depend on I, including its private
receipts; the argument fixes that actual site before testing a. There is no
requirement that a deviation ignore the private signal.

### Lemma 6: fine literal aliases may be removed first

Sometimes the existing fine construction itself uses literal actions and
private alias memory. Suppose it admits the same controlled physical quotient,
its masked fine information F is a function of its literal own information J,
and its prescribed effective policy is b_n(t_i(F)). Assume its local gain is
at most epsilon_n at every literal fine site J and literal alternative.
Then every gain (19) is at most epsilon_n.

**Proof.** At each J projecting to F and each requested class c, choose a legal
representative a(J,c); surjectivity provides it. The controlled continuation
lemma makes its history-wise gain the class gain, independently of alias
memory. Decompose the conditional belief at F over the actual fine J:

    G_n^fine(F,c)
      = sum_{J projecting to F} Pr_n(J|F)
          G_n^literal-fine(J,a(J,c)) <= epsilon_n.             (21)

Here Pr_n(J|F) uses the original fine reach law. Projected physical marginals
and the own-information projection give the belief pushforward; no independence
of the old alias and the hidden physical history is needed for this averaging.
The representative may vary with J. This is an argument about the already
available uniform local bound, not a claim that arbitrary fine strategies
descend. QED.

## 6. Sequential equilibrium and the common witness

### Theorem 1: finite controlled causal transport

Assume Definitions 1--3, fixed finite games, decision recall, (4)--(8), and
numbers epsilon_n>=0 tending to zero such that

    G_n^fine(F,c) <= epsilon_n

for every n, player, fine information set and legal effective alternative.
Then:

1. sigma_n is a fully mixed behavioral profile in the actual fixed game.
2. Its actual Bayesian assessment has every pure or mixed one-information-set
   gain at most epsilon_n.
3. A single subsequence of these actual Bayesian assessments converges to an
   actual sequential equilibrium.
4. For every n, its projected initialized terminal-observation law is exactly
   the fine beta_n law. If those laws converge to a prescribed law L, the SE
   in item 3 has terminal-observation law L.

**Proof.** Full mixing follows from (7)--(8). Every legally reachable actual
site has positive reach at each n: its supported chance/channel factors are
positive and all its legal strategic action probabilities are positive.
Bayes beliefs therefore exist at every actual decision site. Synthetic unused
information labels require no Bayes normalization; any extra policy coordinates
demanded by an API can be filled by a positive legal local law. This is not a
license to totalize differently at a reachable decision site. Lemmas 3--5 give
the local bound, including at information sets whose limiting reach is zero.

There are finitely many actual information sites, finite action menus and
finite sets of history witnesses. The product of their probability simplices
is compact. Extract one subsequence on which every strategy coordinate and
every Bayesian belief coordinate converges. It is a single subsequence for
all players and sites. By definition it witnesses consistency of the limiting
assessment. Each finite local gain is a finite polynomial in continuation
strategy probabilities and an affine function of the belief, hence continuous.
Its limit is nonpositive. Convexity gives nonpositive gains for all mixed local
laws. Under decision recall, the one-step characterization of sequential
rationality applies to this consistent assessment, so it is an SE. The exact
terminal-law identity follows from Lemma 2 or Lemma 4 at the initial history;
finite continuity passes it to the same subsequence. QED.

No uniform lower bound on information-set probabilities is used. The factor
in (12) cancels exactly before taking limits. The theorem does require exact
common effective policies at each positive index. Equality only of their
limits does not control the ratios of trembles that determine off-path beliefs.

If the fine Bayesian assessments already converge to a fine SE, finiteness
supplies the required bound automatically:

    epsilon_n = max(0, max_{i,F,c} G_n^fine(F,c)) -> 0.

If a checked source comparison bounds each fine gain by a mixed source gain
plus a vanishing error, maximize the finitely many source pure gains and add
that error. Convexity covers the mixed source alternatives. This is the form
used by the concurrent counted construction.

## 7. Boundaries and counterexamples

### Counterexample 1: the channel must be simulable from fine information

Nature chooses theta uniformly in {0,1}. A player guesses it and earns one for
a correct guess. The fine player receives no signal, so every pure guess has
conditional value 1/2. A proposed actual channel reveals theta. At the actual
site theta=1, always guessing 0 has a deviation gain of one, although in the
fine game that guess has zero regret. The same failure holds for the fully mixed
sequence guessing 1 with probability epsilon_n: fine regret stays zero and the
actual gain at theta=1 is 1-epsilon_n. The channel cannot be Lambda(F,r): its
law differs between two hidden histories with the same F,r. The physical tree
and menu alone do not prevent this failure.

### Counterexample 2: the whole sequence must have a common class law

Fix 0<p<1/2. Nature chooses theta=0 with probability p. Player 1 observes theta
in the fine game and chooses Out or In. Out pays both zero. After In, an
uninformed player 2 guesses A=0 or B=1 and earns one for correctness. Player 1
gets -1 after A and +1 after B.

The fine limit Out at both types and A after In is an SE. A fully mixed witness
uses P(In|theta=0)=epsilon, P(In|theta=1)=epsilon^2 and P(A|In)=1-epsilon.
Player 2's posterior is p/[p+(1-p)epsilon], tending to one. The limiting
strategy ignores player 1's signal, but its trembles do not.

Remove player 1's theta observation. Every fully mixed profile now has one In
probability x>0, giving posterior p after In. Every consistent assessment makes
player 2 strictly prefer B; player 1 then strictly prefers In. No coarse SE
preserves the Out law. Thus limit measurability cannot replace (6) at every n.
An input-preserving signalling version is given in the
[coarsening analysis](se-private-mempool-mathematics.md).

### Counterexample 3: initialized laws do not control deviations

In a one-player game, the prescribed action is L and pays zero. Let R pay -1
in a fine game but +1 in a proposed actual game. The initialized prescribed law
is identical in the two games, but the deviation gains are -1 and +1. A common
baseline law is no replacement for the controlled successor equation in
Definition 3.

### Counterexample 4: identical emitted packets need not make aliases inert

Two literal responses emit the same packet. The second additionally sets a
private flag. A later prescribed response reads that flag, and a terminal
payment is one precisely when it is set. Quotienting only by the emitted packet
would erase a profitable alternative. One must retain the flag in the physical
class/state or prove that the actual prescribed continuation and payoffs are
insensitive to it. Reconstructibility of a private flag alone does not make it
payoff-irrelevant; it supplies the observation part of Definition 3, not its
transition and continuation clauses.

### Counterexample 5: forgetting a previous visit changes the deviation

An absentminded player encounters the same information value at two successive
nodes. At the first, Stop pays 0; Continue reaches the second, where Stop pays
4 and Continue pays 1. With Continue probability 1/2 at the shared information
value, the initial value is 5/4. Forcing Continue only at the current first node
and then resuming the profile gives 5/2. Replacing the law at the shared
information value by Continue also changes the second visit and gives 1.
Thus the two supposed one-step gains are 5/4 and -1/4. The antichain/recall
hypothesis is necessary when identifying (18) with a one-site behavioral update.

### What is not an extra independence hypothesis

The theorem permits correlated private inputs, an arbitrary fixed finite
service-tape prior, outcome-dependent public records and history-dependent
private reception. It requires the exact channel equation (3) and class-law
equality (6) at their actual fine/actual information values. It does not infer
these equations from the slogan that commitments are opaque, from marginal
independence of some seed, or from honesty only on the limiting path.

The theorem also does not descend arbitrary raw continuations. Its application
to Vegas is to the counted reference sequence. The existing raw audit extension
is applied afterward in the actual private-observation game.

## 8. Existing Lean APIs and the smallest missing adapters

The correspondence below identifies existing owners. No new Lean definitions
are introduced by this document. The formulation uses their existing dependent menus, histories and continuation
runners.

| Mathematical object or step | Existing owning API | Use and boundary |
| --- | --- | --- |
| Fine/actual trees and histories | `GameTheory.Protocol.ExecutionProtocol`, `GameTheory.Protocol.InformationModel` in [Information](../GameTheory/GameTheory/Protocol/Information.lean) | Use the existing models; the finite-tree notation above is their bounded single-mover specialization. |
| Dependent legal menu | `GameTheory.Protocol.InformationModel.Choice` and `GameTheory.Protocol.InformationModel.BehavioralPolicy` | Keep the menu subtype; transports in (4) must be explicit. |
| Recalled own spine | `GameTheory.Protocol.InfoSignals.ownPlay`, `GameTheory.Protocol.InfoSignals.PerfectRecall`, and `GameTheory.Protocol.InformationModel.DecisionRecall` | Supply (1), information antichains and no-revisit facts. Do not replace literal information by an unproved quotient. |
| Reach weights and Bayes normalization | `GameTheory.Protocol.InformationModel.historyReachWeight`, `GameTheory.Protocol.InformationModel.informationMass`, `GameTheory.Protocol.InformationModel.bayesBelief_apply` in [BehavioralBayes](../GameTheory/GameTheory/Protocol/BehavioralBayes.lean) | Equations (12)--(16) are finite proportional-reach identities. |
| One-fiber belief transport | `GameTheory.Protocol.InformationModel.bayesBelief_projection_of_proportional_reach` in [ProportionalBeliefTransport](../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean) | Use when a genuine single-source-site map or a separately established refinement is available. A coarse I mixing several F does not satisfy that premise; use finite disintegration for the general case. |
| PMF conditioning and readout | `GameTheory.Math.Probability.fiberPosterior_map_readout` and `GameTheory.Math.Probability.mul_fiberPosterior_map_snd_apply` in [NestedPosterior](../GameTheoryExtensions/Math/Probability/NestedPosterior.lean) | Package the disintegration over F without manufacturing a false site map. |
| Constant likelihood | `GameTheory.Math.Probability.kernelPosterior_eq_of_constant_likelihood` in [KernelPosteriorGain](../GameTheoryExtensions/Math/Probability/KernelPosteriorGain.lean) | Once (10) is derived, this supplies the conditional equality inside F. It does not derive the native channel factor. |
| Private transcript products | `GameTheory.Protocol.PrivateStrategy.transcriptFactor` and `GameTheory.Protocol.PrivateStrategy.expect_initial_runBehavioral_transcriptScore` in [PrivateTranscriptWeights](../GameTheoryExtensions/Analysis/PrivateTranscriptWeights.lean) | Reuse for the ordered channel/alias word. The callback schedule and dependent class typing still need adapters. |
| Alias splitting | `Vegas.EventGraphRuntime.PhaseProposal.splitResponseLaw_project` in [PhaseProposalResponseAliases](../Vegas/Pending/PhaseProposalResponseAliases.lean) | Gives (9). It does not by itself prove controlled candidate-state lumpability. |
| History-wise to site-wise gain | `GameTheory.Protocol.InformationModel.gain_eq_expect_historyGain` in [SourceGainTransport](../GameTheoryExtensions/Analysis/Protocol/SourceGainTransport.lean) | Supplies the expectation step in Lemma 5 after the two continuation laws are proved. |
| One-site update and continuation | `GameTheory.Protocol.InformationModel.BehavioralPolicy.withLaw`, `GameTheory.Protocol.InformationModel.assessmentComparisonWith`, `GameTheory.Protocol.InformationModel.runBehavioralFrom` | Instantiate existing continuation runners; use bounded fuel or the existing well-founded terminal runner. |
| Consistent local optimality implies SE | `GameTheory.Protocol.InformationModel.BehavioralAssessment.isSequentialEquilibrium_iff_locallyOptimal` in [SequentialOneShot](../GameTheory/GameTheory/Analysis/Protocol/SequentialOneShot.lean) | Converts the limiting local inequalities; consistency and decision recall are explicit premises. |
| Limit and exact outcome law | `GameTheory.Protocol.InformationModel.exists_sequentialEquilibrium_limit_of_local_comparisons` in [LocalSimulationLimit](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean) | Lemma 5 supplies its mixture of source deviations with zero transport error. If only uniform fine regret is retained, compactness plus the existing local-optimality theorem gives Theorem 1 directly. |

For a direct transcript-product instantiation, combine a completed own step into
the finite kernel

    P_{n,i}(r,(F,c))(z,a)
       = Lambda_i(F,r)(z) Q_{n,i}((r,z),c)(a).

Use a tagged dependent sum for inputs (F,c) and outputs (z,a), and keep the
current incomplete callback as its final Lambda factor. The existing transcript
factor is then precisely the product in (10). Equality of fine own spines
supplies identical input words. This avoids introducing another generic
probability-runner abstraction merely to multiply the same finite kernels.
The new reusable content is a narrow causal-kernel producer for (12), together
with the dependent action-class version of the one-step continuation equation.
There is no need to replace the library's information models, Bayes beliefs,
continuation runners, equilibrium limits or enforcement machinery.

For the publication application, the remaining native instantiations are exact:

* the source-query and actual effective-menu label agree after the ledger
  barrier at every counted history;
* the selected reference class law is (6), with full class coverage eliminating
  its totalization branch;
* the candidate mask proves Definition 3, including wrong-typed own memory;
* complete recall reconstructs the ordered pending list, so the current
  observation API has the causal kernel (3);
* the existing complete-pending construction supplies a single uniformly
  approximately rational fine counted sequence.

Compiler timing, source stuttering, expanded resource bounds and the raw audit
composition are separate from this probability theorem. This document does not
close those obligations merely by restating them as a gain premise.
