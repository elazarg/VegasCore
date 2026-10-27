# Publication padding: compiler, timing and preservation specification

This document specifies the mathematical adapters needed to implement the
[publication-padding proof](se-private-mempool-proof-routes.md). It changes no
Lean code, source semantics, theorem contract or preservation checklist.
Statements identified as new lemmas are mathematical proofs to formalize,
not declarations already checked in the repository.

The target is the original intended commit–reveal game. The compiler may add
deterministic public steps and the target observation erases their fresh cells.
No original commitment block is split. Utilities, initial private inputs,
failure payoffs and the original public result are preserved.

There are three distinct games in the composition:

1. The original intended source game.
2. The padded program on the existing concurrent runtime, first with complete
   reception as a mathematical reference and then with actual private reception.
3. The actual bounded raw game with its funded audit.

The complete-reception reference is used only inside the proof. Actual players
never acquire its additional observations.

## Fixed data and quantifier order

Fix a finite player type with cardinality \(m\), an expression language \(L\),
and a source setup \(S\). The original instruction count is \(n\); terminal
return is not counted as an event. Assume the existing setup hypotheses:
finite support of the joint initial law, finite binding value types and source
well-formedness. Initial commitments hold successful values on the prior's
support. The joint initial law need not factor across players.

Fix natural activation and processing gap bounds \(a,p\). Set
\[
                              k=p+2.
\]
The compiler depends on this service specification, not on the selected source
equilibrium. Construct the padded program and its graph, then fix deadlines,
message bounds, candidate reserve, a supported finite reserved-tape prior,
the actual observation rule, utility bounds and the funded audit. Only after
these objects are fixed is the intended source SE quantified.

The reserved tape is sampled separately from the source initial draw, as in
the current construction. Its coordinates may be arbitrarily correlated.
The private-reception transfer does not require independent player types;
it also does not remove the exogenous-tape premise inherited from the fine
reference theorem.

The statement concerns the current observation API: at activation, the
observer and ordered pending list determine a finite reception kernel.
Persistent received-message memory remains present. An additional hidden
gossip state would need its own causal simulation argument.

## Expression and context transport

### Required capability

An inhabited value type is not enough to insert source samples. Require:

* A type \(b\), a value \(v_\star:L.Val(b)\), and, for every public context
  \(\Gamma\), distribution syntax \(d_\Gamma\) whose exact law is the point
  mass at \(v_\star\). Its dependency set is empty.
* Transport of expressions and distributions along label-preserving,
  type-preserving context inclusions, with evaluation commuting with restriction
  of environments. Require equality of dependency sets, so no fresh padding
  name becomes a spurious dependency.

Write \(\iota:\Gamma\hookrightarrow\Gamma'\) for an order-preserving embedding
of typed variable occurrences, and \(e_\iota\) for environment restriction.
The equations required are
\[
\begin{aligned}
 \operatorname{eval}(\operatorname{liftExpr}_\iota(e),\rho')
   &=\operatorname{eval}(e,e_\iota\rho'),\\
 \operatorname{evalLaw}(\operatorname{liftDist}_\iota(d),\rho')
   &=\operatorname{evalLaw}(d,e_\iota\rho'),\\
 \operatorname{exprDeps}(\operatorname{liftExpr}_\iota(e))
   &=\operatorname{exprDeps}(e),\\
 \operatorname{distDeps}(\operatorname{liftDist}_\iota(d))
   &=\operatorname{distDeps}(d).
\end{aligned}
\]
Identity/composition laws for the lifts are convenient but are not needed as
extra axioms if the compiler carries its chosen embeddings explicitly.

For the concrete language in [Simple](../Vegas/Expr/Simple.lean), take the
existing Boolean type, value false and the weighted rational point mass.
Expression transport changes only the membership witness of a variable
constructor; it preserves each constructor and recursively transports its
arguments. Distribution transport preserves weighted tables and recursively
transports the conditional expression and branches of a conditional law.
Structural induction proves all four equations. The weighted point mass
has empty dependencies and singleton support.

Source guards need less expression machinery. A
`Vegas.SourceGuard` has its own fixed expression schema and a map of reads
into the source context. Transport the reads through the source embedding
and keep the guard code/schema unchanged. For a newly consed cell this is
already `Vegas.SourceGuard.weaken` in
[Basic](../Vegas/Source/Basic.lean). Transport publication references and
retained obligations through the same occurrence embedding.

### Source state and observation identities

For a source context embedding define \(E_\iota(s')\) by restricting the
heterogeneous state to original occurrences. Extend the occurrence map through
public-data and publication cells to obtain the corresponding public-context
embedding. Then
\[
\begin{aligned}
 \operatorname{sourcePublicEnv}(E_\iota s')
   &=e_{\iota_{\rm public}}(\operatorname{sourcePublicEnv}(s')),\\
 \operatorname{sourceObserve}_i(E_\iota s')
   &=e_{\iota_{\rm observation}}(\operatorname{sourceObserve}_i(s')).
\end{aligned}
\]
These are cellwise equalities. Public cells preserve their value; own private
cells preserve their visible value; foreign private cells remain hidden.
They do not use independence of any random variables.

Guard prediction and later guard acceptance commute with this restriction:
each read refers to the same original cell, and the retained guard code is
identical. Revelation references commute by transporting their occurrence
witnesses. The source successor identities therefore hold for every original
sample, commitment result and reveal action, including failure-valued results.
They are not restricted to equilibrium histories.

## A concrete, capture-free source transformation

Extract the static instruction-kind word
\(\kappa_0,\ldots,\kappa_{n-1}\). This is possible because the source syntax is
straight-line: every nonterminal constructor has one syntactic continuation.
Expression conditionals do not branch the source instruction tree.

Let \(B\subseteq\{1,\ldots,n\}\) contain the end positions of maximal reveal
blocks that have a commitment instruction later in the program. Thus
\[
 b\in B\Longrightarrow
 \kappa_{b-1}=\mathrm{reveal},\quad
 (b=n\ \lor\ \kappa_b\ne\mathrm{reveal}),\quad
 \exists j\ge b,\ \kappa_j=\mathrm{commit}.
\]
The last condition implies \(b<n\). Insert \(k\) constant samples at each
boundary \(b\). Let \(r=|B|\) and
\[
                              N=n+kr.
\]
Padding after a reveal block with no later commitment would also be sound,
but is unnecessary for the publication invariant.

All original binders and initial context names form a finite set \(V\).
Choose \(M=1+\max(\{0\}\cup V)\). For the \(j\)-th boundary in increasing order,
use names \(M+jk,\ldots,M+jk+k-1\). They are mutually distinct and outside \(V\).
No original name changes, so no original guard subject or opening obligation
changes identity.

The event embedding and padding positions are
\[
\begin{aligned}
 \phi(t)&=t+k\,|\{b\in B:b\le t\}| &&(0\le t<n),\\
 \psi(b,s)&=b+k\,|\{b'\in B:b'<b\}|+s &&(0\le s<k).
\end{aligned}
\]
These images are disjoint, cover \(\{0,\ldots,N-1\}\), and \(\phi\) is strictly
increasing. At boundary \(b\), the first inserted sample is immediately after
the image of event \(b-1\), and the last is immediately before the image of
event \(b\).

Implement the mathematical recursion with an explicit context embedding:

* At an original sample, lift its distribution through the current public
  context embedding, copy the original binder and recurse under the extended
  embedding.
* At an original commitment, transport the guard reads, copy owner, name and
  type, and recurse. The opening-obligation set changes exactly as before.
* At an original reveal, transport its source occurrence, copy the public
  binder and recurse. Remove the same original obligation.
* At a padding boundary, cons each fresh public constant sample and extend the
  target context embedding. No opening obligation is added or removed.
* At return, lift the payoff expressions through the final public-context
  embedding.

Freshness for every original binder follows from original freshness and the
disjoint padding names. Freshness for every padding binder follows from the
chosen enumeration. Original samples and payoffs have the same dependencies.
No guard reads a new padding cell.

The setup's initial context, initial law, account obligation equation and
exit transfers are unchanged. The terminal context gains only the fresh public
cells. Let \(E_{\rm term}\) erase them.

## Source invariants and SE preservation

### Configuration correspondence

At a copied control position, relate a padded configuration to an original one
when source-state restriction agrees, old guard obligations and revelation
references agree under the embedding, and all completed padding cells equal
\(v_\star\). No condition is imposed on unused future cells.

Each copied instruction preserves this relation by the successor identities.
A padding sample has exactly one supported successor and merely adds a public
cell with value \(v_\star\). It does not discharge or change an original guard.
Induction over source control positions gives:

1. Every original intended history has a unique padded expansion at copied
   control positions.
2. Every supported padded intended history ending at a copied position is such
   an expansion.
3. Original initial parameters and the terminal erasure agree.

During a padding block several nondecision prefixes erase to the same original
prefix. Do not assert a bijection on *all* prefixes. The bijection is on
decision histories at copied player positions and on completed histories.
Padding positions have no active player.

### Preserved hypotheses

Initial commitment validity is unchanged. Guard satisfiability follows by
induction on the source well-formedness predicate: an inserted point mass has
one successor; an original sample has the same law; an original commitment
has the same predicted admitted values; a reveal transports the same retained
obligation. Hence the padded setup is well formed.

Finite binding types are unchanged because no new commitment is added.
The joint initial support is unchanged. New sample supports are singletons.
The existing finite-history construction therefore applies to the padded
source. Original declared payoff expressions evaluate identically after
restriction.

### Decision information and policy maps

Let \(h\mapsto h^+\) be the expansion on decision histories. For every player,
\[
 \operatorname{info}_i(h)=\operatorname{info}_i(g)
 \quad\Longleftrightarrow\quad
 \operatorname{info}_i(h^+)=\operatorname{info}_i(g^+).
\]
The forward implication inserts the same constants at the same static
positions. The reverse implication erases them. Own actions and visible
original cells are retained. The known number and locations of padding steps
disclose no hidden branch.

Available original intended actions correspond exactly. In particular the
fallback definition of intended values at a context with no predicted value
is transported, even though well-formedness excludes that case on intended
supported histories. Singleton intended opening actions also correspond.

Lift a behavioral profile by this information/action correspondence. At padding
steps the joint player action is the forced inactive action. For every original
decision history \(h\),
\[
                          w_{\beta^+}(h^+)=w_\beta(h).
\]
Proof: multiply identical original initial, chance and behavior factors;
every inserted factor is one. Therefore corresponding information-set reach
masses and Bayesian posterior probabilities agree whenever their denominator
is positive.

Use the same correspondence after forcing any current legal action.
Terminal erasure commutes with the continuation law, so every conditional local
gain agrees. A fully mixed original profile lifts to a fully mixed padded
profile on the actual menus. Lift the whole source consistency sequence and
its beliefs through these fixed finite maps. Limits and local inequalities
are preserved, giving a padded intended SE.

For any terminal utility \(u_i\), define
\[
                         u_i^+(s')=u_i(E_{\rm term}(s')).
\]
This definition is on every terminal state, not just reachable ones. Thus
global lower/upper bounds and the exclusion floor remain valid everywhere.
Retain the existing bounded-payoff configuration, including its bounds on
default payoffs and excluded-player payoffs; the utility pullback does not
establish those separate inequalities. Their values are unchanged by padding.
The padded observable is the original initialized terminal/public/payoff
observable after erasure; it is not the padded public record with additional
constant fields.

## Resource bounds for the expanded graph

Recompile the padded source with the existing concurrent mode and its maximal
phase plan. The existing compiled barrier-order theorem applies to this ordinary
source program. In particular, an ownerless public sample blocks later events
even if their expression dependencies do not read its constant output.
Consecutive commitments remain one maximal commitment block.

Copy each original owned event's deadline to its image under \(\phi\).
New samples can have deadline zero: the timeliness predicate applies only to
owned events, and sample expiry does not perform their chance step.
Using any larger fixed sample deadline is also sound but enlarges the derived
execution bound.

Let \(D_{\max}\) be the maximum deadline of the expanded graph, including any
chosen sample deadlines. The existing resource definitions give
\[
\begin{aligned}
 W&=(N+m)(N+1)+N,\\
 C&=(W+1)(D_{\max}+2),\\
 Q&=Cm,\\
 w&=Q+m+N+2,\\
 H&=Cw.
\end{aligned}
\]
Here \(C\) is the number of reserved cycles, \(Q\) the packet processing
capacity per enabled cycle, \(w\) the number of environment commands per cycle,
and \(H\) the environment-command horizon. The corresponding protocol-history
bound used by the native gain theorem is \(H_{\rm nat}=2H+1\).

These definitions are in
[ReservedEpochProgress](../Vegas/Pending/ReservedEpochProgress.lean),
[ReservedEpochExhaustion](../Vegas/Pending/ReservedEpochExhaustion.lean),
[ReservedEpochTraceDelivery](../Vegas/Pending/ReservedEpochTraceDelivery.lean)
and [ReservedEpochCompletion](../Vegas/Pending/ReservedEpochCompletion.lean).
The order is noncircular: logical events and deadlines determine \(C\);
then \(Q,w,H\) are computed. Choose the prepared-candidate reserve at least
\(H\), as required by the current compiler theorem.

Each cycle has at most \(m\) owner callbacks. Each callback emits at most one
envelope, even for raw strategies. Hence the entire raw history contains at
most \(Cm=Q\) envelopes, and every pending prefix has length at most \(Q\).
The argument does not assume honest play, silence during padding or a
counted-message bound. Enlarging the physical command horizon by its processing
slots adds no extra owner callbacks inside those slots.

Require every tape in the fixed prior's support to satisfy bounded gaps
through the new \(C\), not merely the old program's cycle bound. The finite tape
is periodically extended by its definition; a larger prefix length is one
possible configuration, not a premise that follows from the original tape.
For each owned event the old strict margin remains
\[
                            a+p+2<\operatorname{deadline}(e).
\]
The source transformation does not shorten that event's interval from its own
readiness. All finite-message and genuine output-value coverage hypotheses
are instantiated for the expanded graph. Public sample output types do not add
new binding-value coverage obligations.

## Exact timing and publication

### Cycle and slot facts

The physical cursor is the environment-recall length. At cursor \(z\), cycle
and slot are \(z\div w\) and \(z\bmod w\). The reserved order is:

1. \(Q\) processing commands;
2. \(m\) possible owner activations;
3. one sample command;
4. \(N\) expiry commands;
5. one clock advance.

Responses do not move the environment cursor, and only the last command
advances the public clock. Starting from clock zero, the clock at a command's
pre-state equals its cycle index. The actual clock/cursor induction is in
[ReservedEpochClock](../Vegas/Pending/ReservedEpochClock.lean).

The sample phases are singleton phases. Automatic draining requires an
excluded *owned* event, so it cannot execute a sample. Expiry also cannot
execute it. One sample command executes at most one sample and then normalizes;
normalization cannot execute the next sample. Consequently consecutive inserted
samples require distinct cycles.

### Delay lemma

Fix an actual counted history that reaches a later binding callback. Let \(c\)
be the clock when the preceding maximal reveal block closes, and let
\(t_0<\cdots<t_{k-1}\) be the cycles of its inserted sample executions.
The first sample cannot execute before closure, so \(t_0\ge c\).
One-per-cycle execution gives
\[
                  t_s\ge c+s,\qquad t_{k-1}\ge c+p+1.
\]
Owner activation slots precede the sample slot. Thus no callback for a binding
enabled by the last sample occurs in that same cycle. If \(d\) is the later
binding callback's cycle,
\[
                              d\ge c+p+2.
\]
Intervening original source instructions can only increase this lower bound.
This argument conditions on a history reaching the binding; it does not
assume that all plays reach that event.

### Existence of a clearing epoch within the actual horizon

Since the callback exists, \(d<C\). Therefore \(c+1<C\).
Apply the tape processing-gap condition at \(c+1\). It gives an enabled cycle
\(q\) with
\[
                  c+1\le q<c+1+p,\qquad q\le c+p<d.
\]
In particular \(q<C\). This avoids assuming a future processing epoch beyond
the bounded run. The premises imply \(p>0\): a zero processing gap cannot
satisfy the stated strict interval condition when \(C>0\).

Every counted opening of that closed block was submitted no later than closure.
Until inclusion it remains in pending traffic. At cycle \(q\)'s processing
prefix, at most \(Q\) envelopes are pending and no player callback interleaves
with those \(Q\) commands. The existing
`Vegas.EventGraphRuntime.ReservedEpoch.full_processing_epoch_clears` gives
\[
 P_{\rm after}=[],
 \qquad L_{\rm after}=L_{\rm before}\mathbin{+\!\!+}P_{\rm before}.
\]
Semantic rejection does not remove a packet from this appended ledger.
Every opening from the closed block is consequently ledgered before callback
cycle \(d\). This includes an opening submitted just before expiry that was
never accepted as a game action.

### No new counted old-phase openings

During a sample phase no source event owned by a player is currently authorized.
In the existing emission interface, an out-of-phase call receives no valid
phase token. The counted menu at a genuine no-request callback is the singleton
silent response. After entry to the next commitment block its only submitted
counted packets are opaque commitments.

This is a statement about the current interface, not a general claim that
real senders cannot replay previously signed transactions. The separate
[audit-boundary analysis](se-publication-audit-boundary.md) distinguishes that
backend question.

### Archive equality at every counted binding information set

Let \(A(h)\) be the set of typed opening proposals extracted from all submitted
envelopes of a history \(h\), and let \(A_i(h)\) be the same extraction from
the player's own outputs, retained private receipts and current ledger.
At every counted binding callback,
\[
                                  A_i(h)=A(h).
\]

The inclusion \(A_i(h)\subseteq A(h)\) is ordinary packet provenance.
For the reverse inclusion, locate the earlier reveal block that authorized
the submitted opening. If a later binding exists, that block has a padding
boundary. Its clearing epoch puts this envelope in the ledger before the
binding. All earlier blocks are covered in the same way.
No opening can have been submitted from a future reveal block on a counted
history. Initial traffic is empty, so a binding before the first reveal has
empty opening archive. A retry of the current commitment block adds no opening
proposal; the same invariant persists through every such retry.

Thus the equality is pointwise on counted histories, independent of profiles
or reception probabilities. It is constant on actual information fibers:
the right-hand archive is computed by the actual local reader on the left.
It is not an all-raw-history decoder theorem.

## Recovering the fine common sequence

Apply the existing complete-observation construction to the padded setup.
This is the same runtime and the same theorem family on a different ordinary
source program, not a modified scheduler theorem. In particular the existing
Send/Wait and rollback payoff comparisons remain the comparisons of their
specified source-query continuations.

Use the actual counted sequence from
[PhaseProposalConsistentSequence](../Vegas/Game/PhaseProposalConsistentSequence.lean)
and [ConcurrentRawEquilibrium](../Vegas/Game/ConcurrentRawEquilibrium.lean),
not merely the existential raw capstone. Pass to the strict subsequence supplied
there and relabel it once.

Let \(\alpha_j\) be the fine counted native assessments and \(\zeta_j\) the
finite proposal-recovery source assessments. They are fully mixed and Bayesian;
\(\zeta_j\) converges to a source SE, and their prescribed value/class laws use
the same positive perturbation parameters. Let \(s_j\to0\) be the scale.

For the padded program the source history bound is
\(H_{\rm src}=(m+1)(N+1)\). Set
\[
\begin{aligned}
 U&=\sum_i(|\ell_i|+|u_i^{\max}|+|F_i|),\\
 e_j&=U(14+16mH_{\rm nat}+12mH_{\rm src})s_j,\\
 R_j&=\max\bigl(\{0\}\cup
      \{G_{\zeta_j}(i,J,a):i,J,a\text{ a legal source pure deviation}\}\bigr),\\
 \epsilon_j&=R_j+e_j.
\end{aligned}
\]
The index set of the maximum is finite and fixed. Each source gain is continuous
in strategy and beliefs, and has nonpositive limit at the source SE.
Thus \(R_j\to0\); also \(e_j\to0\) and \(\epsilon_j\to0\).
The explicit local comparison
`Vegas.concurrentRaw_local_gain_le` bounds a fine counted local gain by either
\(e_j\) or a source mixed-action local gain plus \(e_j\).
Linearity in the alternative lottery bounds that source gain by \(R_j\).
Therefore every fine counted information set and every literal one-step
alternative has gain at most \(\epsilon_j\).

This argument does not divide by a limiting information-set reach probability.
It uses the already constructed Bayesian assessments at each positive index.
The initialized joint-law error also tends to zero along this same sequence.
Its terminal observables include original inputs, typed terminal state,
exclusions and base payoff vector.

## Composition with private observations and raw actions

The [native adapter](se-publication-native-adapter.md) identifies the common
effective class law at *every* counted information set. The archive equality
above supplies the only missing observation in the binding query. Actual
opening and silent branches are already local. The counted candidate mask
retains the successful typed state and reconstructs discarded raw own memory.
It also covers a one-step counted deviation followed by the prescribed profile.

First project the fine literal witness to its effective/masked game.
At a masked fine information set, condition on its compatible literal fine
information sets. Choose a legal representative of a fixed class at each
literal information set. Their conditional gains average to the effective gain,
because the projected forced transition and prescribed continuation agree.
Hence the effective fine gain is at most \(\epsilon_j\).

The [finite transfer theorem](se-publication-transfer-mathematics.md) constructs
the actual private counted profile by sampling the common class law and then
a full-support local literal alias. It provides the exact conditional identity
\[
 G_j^{\rm private}(i,I,a)
   =\sum_F\lambda_j(F\mid I)
                 G_j^{\rm fine,effective}(i,F,\pi_I(a))
   \le\epsilon_j.
\]
The weights are actual conditional probabilities; each deviation class is
legal at every fine site receiving positive weight. Fixed finite compactness
gives one convergent subsequence of the private strategies and Bayesian beliefs.
That sequence establishes consistency, and the displayed bound establishes
sequential rationality. Its masked terminal law agrees with the fine sequence
at every index and therefore with its limit.

Finally use the actual-observation version of
`Vegas.EventGraphRuntime.PhaseCount.onePacket_raw_sequentialEquilibrium` in
[PhaseOnePacketExtension](../Vegas/Game/PhaseOnePacketExtension.lean).
It accepts any counted SE under its stated finite-nature, payoff-bound and
funded-coverage conditions. It preserves the actual counted terminal-history
law, its randomized settlement law and zero on-path charges. No fine raw
off-path profile is transported or assumed to ignore observations.

For the final equality apply the observation map
\[
 (\theta,s^+,z)\longmapsto
       (\theta,E_{\rm term}(s^+),
        \operatorname{originalPublicResult}(E_{\rm term}(s^+)),z),
\]
where \(z\) is the actual realized net-payoff vector. The common counted limit
has no exclusions; the raw extension preserves that support property.
This proves the claimed original initialized joint law, not merely each
coordinate's marginal expectation.

## Formalization contract and limits

The compiler and probability lemmas above are new. The cited runtime and
source constructions are existing ingredients. A formal implementation should
produce the following concrete interfaces in dependency order:

| Interface | Mathematical content | Owning layer |
|---|---|---|
| Context transport | Evaluation, dependency, observation and guard commutation | Expression/source |
| Padding transform | Fresh-name allocation, instruction embedding, erasure and unchanged commitment blocks | Source/compiler |
| Source SE expansion | Decision-history and menu correspondence; common-sequence gain and law identities | Source game / generic restriction tools as applicable |
| Expanded resource instance | \(N,W,C,Q,H\), candidate reserve, tape support and owned-event margins | Pending/runtime configuration |
| Publication invariant | Reachable cycle inequality, full-batch recording and counted binding archive equality | Pending |
| Native class adapter | All-index genuine class law, masked transitions, causal own memory, ordered pool readout | Pending / game |
| Controlled private transfer | Actual Bayesian mixture identity and literal deviation gain bound | GameTheoryExtensions |
| Final assembly | Fine vanishing-regret sequence, private counted limit, arbitrary-leak raw extension and original readout | Vegas game |

None of these interfaces should be replaced by an assumption that actual native
conditional gains already match the source: those gains are the conclusion.
Avoid new generic runner abstractions where the existing finite protocol,
conditional-gain and action-restriction machinery already supplies the needed
operations.

The finite theorem retains the current emission authorization and audit
interfaces. A real blockchain must separately justify its admission, inclusion,
recording and audit model, including withheld old signatures and traffic
capacity. The theorem gives no adaptive-builder extension and no preservation
claim for unbounded inclusion delays. Added physical costs or time-dependent
utilities are outside the unchanged-payoff assertion unless explicitly modeled.
