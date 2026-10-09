# Checked sequential-equilibrium obstruction in the native runtime

Analysis by Codex.

The existing asynchronous service contract does **not** suffice to preserve
every source sequential-equilibrium outcome with collateral fixed before the
builder. This is checked for an actual compiled three-instruction program,
including all responses in its bounded raw menu, remembered pending-packet
observations, authentic readiness credentials and the full settled audit.
Sequential equilibria of the target exist. Every one fails to reproduce the
selected source's exact joint terminal-store and realized-payoff law.

This is an outcome-implementation obstruction. It rules out more than one
particular strategy translation: no alternative native SE implements that
law in the chosen service. It does not assert that every asynchronous game,
every admissible builder or every blockchain has this problem.

## Quantifiers and collateral

Let the sender's reward scale be $R$, the publication forfeit be $D$, and the
sender and receiver audit deposits be $K_A,K_B$. Fix finite real amounts with

\[
R>0,\qquad D>R,\qquad K_A>R,\qquad K_B>1.
\]

For every $\varepsilon>0$, the checked theorem constructs one finite public
chance builder satisfying both the existing asynchronous service contract and
its late-packet erasure requirement. For the canonical late-opening policies,
its terminal omission probability $\delta$ satisfies

\[
0<\delta<\varepsilon.
\]

The erasure requirement says that the scheduling law is a mixture of
selecting the late packet and the law obtained when that packet is removed.
It controls interference with other service choices; it does not make the
packet's contents invisible.

The native game has an SE, and **every native SE has a different joint outcome
and payoff law from the source Safe law**. The order is

\[
\forall R,D,K_A,K_B\quad\forall\varepsilon>0\quad
\exists\text{ one admissible builder}\quad\forall\text{ native SEs}.
\]

The builder is selected after collateral, before any native equilibrium. It is a
fixed, exogenous chance rule, known to the players. It does not observe private
types or cooperate with a player. Quantifying over the service class selects a
counterexample rule; it does not model players as uncertain about that rule.
A game with an unknown producer distribution needs its own beliefs and
equilibrium definition.

The headline declaration is
`Vegas.Examples.LateOpeningRuntimeUniformSeObstruction.exists_service_with_no_preserving_equilibrium`
in [UniformSeObstruction](../../Vegas/Examples/LateOpeningRuntimeUniformSeObstruction.lean).
Its guarded axiom pin in [Paper.lean](../../Paper.lean) depends only on
`propext`, `Classical.choice` and `Quot.sound`.

The full failure-aware source comparison additionally assumes $D\ge1$.
One source SE admitting both failed bindings and failed publications can then
be fixed before $\varepsilon$ or the builder, with the exact Safe joint law.
This uses the concrete source extension below; $D\ge1$ is a sufficient
extension bound, not a proved minimal collateral requirement.

This strongest explicit source-to-target composition is
`Vegas.Examples.LateOpeningRuntimeSourceSeObstruction.exists_source_equilibrium_with_uniform_service_obstruction`
in [SourceSeObstruction](../../Vegas/Examples/LateOpeningRuntimeSourceSeObstruction.lean).
Its order is

\[
\forall\text{ fixed collateral}\quad\exists\text{ one source SE}\quad
\forall\varepsilon>0\quad\exists\text{ one admissible builder}\quad
\forall\text{ native SEs}.
\]

Every native SE's joint law differs from that same selected source SE's law.
Neither source nor target equilibrium existence is an unproved hypothesis.

## The source and target being compared

The source program is: Alice publishes an initialized Boolean; Bob commits an
answer; Bob publishes that answer. Alice also has a private preference label,
uniform on three possibilities and independent of the Boolean. The Boolean
has full support, with probabilities $9/20$ and $11/20$. It is immutable.

Bob has six answers: Safe, three label guesses, and two Boolean guesses.
After Alice publishes successfully, Safe gives Bob $2/5$, a correct label
guess gives him $1$, and Boolean guesses give him $0$. Without timing signals,
the posterior on the three private labels stays uniform. Safe is therefore
uniquely optimal. Every mandatory-publication source SE has the same joint
terminal-store and payoff law, with Alice's payoff $R/2$.

Alice's successful reward is $R/2$ for Safe. A label guess gives her $R$ for
private labels zero and one, and zero for label two. After her publication
fails, Bob can earn one by guessing her Boolean correctly. Alice's failure
reward is $R$ for a true guess at label zero, $R$ for a false guess at label one,
and zero otherwise, before deductions. These rewards are the program's actual
utilities, including its initialized private inputs.

The checked source declarations are
`Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_terminal_law`
and `.exists_withholding_equilibrium_with_safe_law` in
[SourceEquilibrium](../../Vegas/Examples/LateOpeningRuntimeSourceEquilibrium.lean).
The latter permits failed publications and preserves the same law when
$D\ge\max(R,1)$, retaining value-only binding admission.
The checked
`Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_preserved_under_forfeiture`
and `.exists_forfeiting_equilibrium_with_safe_law` in
[SourceForfeiture](../../Vegas/Examples/LateOpeningRuntimeSourceForfeiture.lean)
extend the comparison to the complete interface permitting immediate failed
bindings as well. In this particular program a failed Bob binding forces his
sole publication to fail, paying him exactly $-D$. Every value-only
continuation gives him at least $-D$. Thus **every** value-only withholding
source SE extends to this complete interface for $D\ge0$, preserving the exact
joint law. Composing the intended extension uses $R\ge0$ and
$D\ge\max(R,1)$. This is a concrete source theorem, not a generic
full-language failed-binding SE adapter.

The target is the actual bounded signed-message runtime. Its horizon is 26
rounds. It has a sure protected owner opportunity and two later opportunities
to send the same lawful opening. Both late choices precede Bob's irreversible
answer commitment. Bob commits only after Alice's publication has succeeded
or expired. No reveal crosses an earlier commitment dependency.

Pending packets can be observed. The example uses repeated partial samples:
an earlier foreign-packet sample is fair, and a later sample is also fair.
Remembered samples persist. A packet's authentic opening material can reveal
the Boolean even if the packet is eventually omitted. The declaration is for
this partially public observation rule; it is not a theorem about every
fully transparent mempool.

The builder's one late inclusion lottery has success probability
$q=w/(1+w)$ for a finite positive weight $w$, hence $\delta=1-q>0$.
Protected service, completion, packet bounds and the erasure law hold on
every legal bounded raw history. The canonical opening's final receipt law
is exactly this lottery after either late sending time. That is a
whole-horizon statement for the specified canonical policies, not a bound on
the probability that every action in any deviating execution succeeds.

Accepted lawful late openings are audit clean. An omitted sole opening incurs
the forfeit and sender audit charge, giving deduction $D+K_A$. The audit uses
the full authentic traffic record, with one capped charge per author. All
modeled malformed packets, silence, extra identifiers and private submission
aliases remain available. Sequential rationality supplies the required clean
continuations; the proof does not replace the players' future policies with
prescribed ones.

## Why rare failures change exact sequential rationality

The contradiction has four checked parts.

1. **Failure rewards sort the sending times.** For the actual receiver
   continuation of any native SE,
   the sender's first-minus-second timing values have the form
   $(P+T,P-T,-P)$ for the three private labels. $P$ records the difference in
   successful receiver behavior. $T$ records the extra chance of learning the
   Boolean from an earlier pending opening when publication eventually fails.
   For some Boolean, $T\ne0$ whenever $R>0$ and $\delta>0$, regardless of Bob's
   guess when he has learned nothing. Thus some private label strictly sends
   first and another strictly waits. The identical failure deduction cancels
   in this timing comparison.

2. **One consistency sequence links both receiver posteriors.** Let
   $\alpha_\ell$ be a label's genuine first-send probability. Conditional on
   successful publication, the leading label weights along the common
   fully mixed sequence are $\omega_\ell\alpha_\ell/2$ for the records with
   an earlier observed opening, and $\omega_\ell(1-\alpha_\ell/2)$ for
   records without one. These leading weights omit the common successful
   inclusion factor and original receiver-silence factors that tend to one.
   The exact history probabilities retain those factors and have uniform
   relative errors tending to zero. Here $\omega_\ell$ includes the original
   protected-silence probability and can vanish arbitrarily quickly along
   trembles. The proof uses relative errors and the same actual native
   fully mixed sequence for both records. It never assumes a positive limit
   or divides by a vanishing type weight. A label that surely sends and one
   that surely waits force a zero cross-product of the two limiting beliefs.

3. **Safe cannot remain supported at both records.** If Bob assigns positive
   probability to Safe at a successful record, every label probability must
   lie in $[1/5,2/5]$: no label guess may beat his Safe reward $2/5$, and the
   three probabilities sum to one. Safe at both records would give a cross-
   product at least $1/25$, contradicting the preceding identity. At one
   successful record Bob consequently puts zero probability on Safe.

4. **An available deviation exceeds the preserved value.** For the Boolean
   selected by the preceding steps and Alice's labels zero and one, sending
   at the first late opportunity then yields at least
   $3qR/4-\delta(D+K_A)$. Matching the source's joint law fixes her protected
   continuation value at $R/2$ for every initialized private type.
   Sequential rationality bounds her original later value by that amount,
   while requiring it to dominate the available first-opening response.
   Choosing
   \[
   \delta<\frac{R}{3R+4(D+K_A)}
   \]
   makes the lower bound strictly greater than $R/2$, a contradiction.

The builder also makes omission sufficiently small to ensure the opening and
retry incentive margins used in the raw-menu normalization. Every chosen
weight is finite. No zero-failure limit is substituted for the actual game.

The final fixed-service theorem is
`Vegas.Examples.LateOpeningRuntimeSeObstruction.equilibrium_terminal_law_ne_safe`;
`.equilibrium_terminal_law_ne_intended` compares directly with every intended
source SE. See [SeObstruction](../../Vegas/Examples/LateOpeningRuntimeSeObstruction.lean).
The key intermediate checked results are in
[AliceTimingValues](../../Vegas/Examples/LateOpeningRuntimeAliceTimingValues.lean),
[AliceTimingSorting](../../Vegas/Examples/LateOpeningRuntimeAliceTimingSorting.lean),
[LabelCross](../../Vegas/Examples/LateOpeningRuntimeLabelCross.lean),
[BobSafeProbability](../../Vegas/Examples/LateOpeningRuntimeBobSafeProbability.lean),
[AliceTimingFloor](../../Vegas/Examples/LateOpeningRuntimeAliceTimingFloor.lean), and
[AliceProtectedOptimality](../../Vegas/Examples/LateOpeningRuntimeAliceProtectedOptimality.lean).

## Consequences and open scope

Sure protected service, fixed horizon, hidden commitments, authentic causal
readiness and an authentic full audit all coexist with this negative. Arbitrarily
high canonical late reliability does not suffice for **exact** SE outcome
preservation. Finite collateral does deter forbidden departures here; it does
not remove the equilibrium consequences of accepted lawful timing choices.

The checked exact asynchronous Nash correspondence and the stronger calendar
SE theorem are unchanged. The same-fixture preserving weak PBE and the native
first-ready positive have reviewed paper proofs, not checked compiler
capstones. The smaller sender-deposit and partial-audit variants in
[the detailed analysis](native-late-action-analysis.md#smaller-sender-deposit)
are also paper results; the checked uniform negative uses $K_A>R$ and the full
authentic audit. No theorem here establishes a general PBE preservation result
or a necessary-and-sufficient interface for SE preservation.

A proposed positive for an unrestricted runtime must explicitly rule out this
combination of legal timing, observation and failure-dependent continuation
rewards, or state a weaker preservation target. One changed service property
alone is not proved sufficient by this negative. Restricting admission to
first-ready actions, changing failure settlement, or proving approximate
sequential rationality are separate claims requiring their own adapters.

The model assumes ideal cryptography and finite funded play. Fees and gas,
capital and time costs, participation, strategic or colluding producers,
unknown service priors, coalitions, outside public channels, concrete
cryptographic encodings, resource markets, reorganizations and finality risk
are absent. The bounded raw menu is the full menu of this configured model,
not every possible blockchain transaction. Additional observable fields may
introduce new signals and need a new proof. These omissions limit deployment
claims; they do not create an assumption of invisible pending messages in
the theorem above.
