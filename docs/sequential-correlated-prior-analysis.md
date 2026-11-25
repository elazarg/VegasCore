# Correlated priors and observed initial components

An intended sequential equilibrium can survive compilation even when players share
private information and the builder offers retries. Let `Z` be a statistic of the
initial draw. On supported draws, equal initial observations for player `i` must
give equal values of `Z`, for every player. Thus every player can determine the same
value using its own observations. The scheduler, ledger and public transcript need
no additional signal. [Common initial signal](../Vegas/Game/CommonInitialSignal.lean)

For every supported value of `Z`, supply the component compiler specification on
the same sequential graph, raw menu, builder, leak rule and horizon, with the
same audit service and deposits. Index the components by supported signal values.
For retries, conditional private-input independence given the component's public
signal suffices. The two-player single-opportunity alternative also applies
componentwise. The [specification adapter](../Vegas/Game/ConditionedClientSpecification.lean)
restricts a global service and its other certification hypotheses to the
conditional initial laws once the component prior conditions have been proved.

`SharesInitialSignal.preservesSequentialEquilibrium` yields one assessment of the
original bounded raw ledger game for each supplied intended sequential equilibrium.
The assessment is sequentially rational against whole-policy deviations, has
consistent beliefs at every decision, and preserves the intended joint law of
full terminal source configuration and settled payoffs under the **original**
prior. Every supported terminal history has an empty public default set and
zero count-audit charges. The physical clients decoded from this same
assessment preserve the joint law from every represented clean source
boundary, including off-path boundaries. A full-game raw history and its
matching one-packet history suffice. The trace itself identifies the component
for the continuation proof. [Continuation from a global boundary](../Vegas/Game/ObservedComponentEquilibrium.lean)

The same assessment [retains source strategies and beliefs](../Vegas/Game/ConditionedAssessmentFidelity.lean).
Every intended information site has a global raw counterpart whose posterior
replays to the supplied intended posterior. The normalized client plays the
intended action law at matching first decisions, and replay holds at all matching
forced sites with an owner turn. The decoder identifies the observed component,
replays the native history there, and embeds the source history in the original game. [Observed-component theorem](../Vegas/Game/ObservedComponentEquilibrium.lean)

## How the assessments fit together

1. Restrict the supplied source assessment and its single fully mixed approximating
   sequence to each observed component. Each conditional decision-history fiber
   embeds bijectively in the corresponding original fiber, including at zero-reach
   views. At every initialized history, original reach equals conditional reach
   multiplied by the component's marginal probability. This positive factor cancels
   in Bayes' rule. Every conditional continuation deviation has an original
   counterpart with the same continuation law.
   [Source Bayes transport](../Vegas/Game/ConditionedSourceBayes.lean) ·
   [Source equilibrium restriction](../Vegas/Game/ConditionedSourceRationality.lean)
2. Compile each restricted assessment, then select the component's strategy
   and history beliefs at each raw decision according to the player's actual
   view. All histories at that site belong to the same component. Selecting
   the component approximants at the same sequence index gives one global
   fully mixed Bayes sequence. The raw reach weights scale by the same marginal
   probability as in the source proof. Every unilateral deviation continues
   within that player's observed component under the common settlement rule.
   [Raw history fibers](../Vegas/Game/ConditionedLedgerFiber.lean) ·
   [Raw consistency](../Vegas/Game/ConditionedLedgerConsistency.lean) ·
   [Raw sequential rationality](../Vegas/Game/ConditionedLedgerRationality.lean)
3. Mix the conditional execution laws with their original probabilities. The
   physical state records the original private inputs and public outcome. A
   globally supported terminal state occurs in a supported component, where
   the compiler proves no defaults and zero charges.
   [Joint law](../Vegas/Game/ConditionedClientCompiler.lean) ·
   [Supported paths](../Vegas/Game/ConditionedLedgerPath.lean)

The unsampled root has reach one in both protocols and offers no player decision.
The reach identity and posterior comparison apply after initialization.

## A common private bit

Two players each observe a private copy of the same fair bit, then commit and
reveal fresh choices for Odds–Evens. Their two initial cells are dependent and
there is no public initial input. Conditioning on the common bit gives two
deterministic priors. Each player recovers the bit from its private ledger store
after arbitrary legal traffic. The periodic service uses full pending observation
and the same funded audit for both components.
[Source prior](../Vegas/Examples/CorrelatedInitialBits.lean) ·
[Ledger reader](../Vegas/Examples/CorrelatedInitialBitsLedger.lean) ·
[Periodic service](../Vegas/Examples/CorrelatedInitialBitsService.lean)

The example proves existence of an intended sequential equilibrium and realizes
every supplied intended sequential equilibrium on that periodic service with its
exact joint configuration and settled-payoff law.
[Correlated-bit equilibrium](../Vegas/Examples/CorrelatedInitialBitsEquilibrium.lean)

On a legal one-packet history the first owner passes and receives another turn
for the same binding. The instance also fails independence given every signal
determined by the public initial cells. Thus neither alternative of
`SequentialPriorCondition` covers this game and service.
[Repeated opportunity](../Vegas/Examples/CorrelatedInitialBitsRetry.lean)

## Where the component compiler uses independence

The relevant declaration surfaces are in
[OnePacketConditionalPrior](../Vegas/Game/OnePacketConditionalPrior.lean),
[OnePacketOwnerKeyed](../Vegas/Game/OnePacketOwnerKeyed.lean),
[OnePacketLateRecords](../Vegas/Game/OnePacketLateRecords.lean), and
[OnePacketSpliceForced](../Vegas/Game/OnePacketSpliceForced.lean).
The active raw capstone is
[native sequential preservation](../Vegas/Game/SequentialCompilation.lean).

There are two separate obligations. An owner swap must replace one player's
hidden initial cells while retaining a supported draw and the required
observations. It must also multiply every compared history's prior mass by a
single positive scalar, so normalization cancels that scalar. The latter
produces equal base laws of operational records at sites with the same late
key. The late key intentionally omits most of the owner's private information.

Full support supplies the required initial splice, but not the scalar. A
constant-ratio assumption for all private-type replacements and all remaining
states is conditional independence again. Merely renaming that assumption
does not weaken the result.

## Why full support alone does not repair the current construction

Let A and B be private bits, with no public initial input, and masses

| P(A,B) | B=0 | B=1 |
| --- | ---: | ---: |
| A=0 | 0.4 | 0.1 |
| A=1 | 0.1 | 0.4 |

Then P(B=0 | A=0)=0.8 and P(B=0 | A=1)=0.2. Consider two local options whose
success indicators are respectively B=0 and B=1. Each type has optimal value
0.8, but their unique optimizers differ. If a type-blind policy uses option zero
with probability x, the regrets at types zero and one are respectively
0.6(1-x) and 0.6x. Their maximum is at least 0.3 for every x. No vanishing
tremble scale eliminates this fixed loss.

This obstruction is not special to this table. If two conditional laws of B
differ, some event E has probabilities q0<q1. Compare the option paying
1_E with the constant option c=(q0+q1)/2. The types have opposite strict
preferences. A common randomized option has worst-type regret at least
(q1-q0)/4. Thus agreement of optimizers for every bounded decision problem
would already force equality of the conditional laws.

These are obstructions to a universal hidden-type-blind late-pool argument.
They are not runtime counterexamples: the options must still be realized by
actual legal runtime decisions and the other source/runtime hypotheses, and
one must rule out all preserving implementation equilibria. An obstruction to
one pooled construction does not establish that stronger conclusion.

For a fixed selected game, correlation can be harmless. If an available
operational option dominates the others pointwise in the remaining state,
every conditional law shares that optimizer. If the relevant signed gains
have the same expectation under all type-conditioned laws, those gains also
transport. The missing application result is to derive such an order or
observable restriction from the actual runtime, uniformly at the required
information sets and along one common consistency sequence. Assuming it at
the preservation boundary only names the missing adapter.

## Correlation remaining within a component

This does not cover arbitrary full-support correlation. For two players form a
bipartite graph of their initial observations, with an edge when a pair has
positive probability. A statistic computable by both players is constant on
every connected component: it has the same value at the endpoints of every
edge, and equality propagates along paths. Conversely each player can recover
the connected component from its own vertex. Full support makes this graph
connected, so every such deterministic common signal is constant. The 0.4/0.1
example above consequently receives no benefit from this extension.

A missing joint input does not by itself help. The support
{(0,0),(0,1),(1,1)} is connected and has no nonconstant common signal. In
contrast, the two-point diagonal or antidiagonal supports have two components.
Dealing two cards to two players can fall into that latter full-information
case, but ordinary card hands leave uncertainty about the allocation and are
not covered automatically. A randomized latent mixture variable that players
cannot recover is not a valid Z for this proof.
