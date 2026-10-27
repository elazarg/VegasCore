# Correlated priors: proof obstruction and a common-signal extension

This is a finite mathematical derivation, not a checked weakening of the Lean
preservation theorems. It identifies a genuine extension by conditioning and
gluing, and separates it from the unresolved case of correlated private
information that nobody jointly knows. The implementation, scheduler,
observation rule and audit remain fixed throughout.

## Checked source adapters

The source conditioning and Bayes accounting are mechanized:

* [ConditionedInitialLaw](../Vegas/Source/ConditionedInitialLaw.lean) changes only
  the actual initial law, restricts support, retains local observations and
  menus and post-initial kernels, and reconstructs the original source run law
  by mixing conditional source laws.
* [ConditionedInitialHistory](../Vegas/Source/ConditionedInitialHistory.lean)
  and [ConditionedInitialFiber](../Vegas/Source/ConditionedInitialFiber.lean)
  give an injective actual intended-history map, an inverse on the selected
  initial component, and state, length and observation preservation. Their
  information-history map is bijective when the whole actual information
  fiber determines the component.
* [ConditionedInitialPolicy](../Vegas/Source/ConditionedInitialPolicy.lean)
  transports actual intended choices and local randomized action laws without
  adding any observation of the signal.
* `Vegas.SourceProgram.Setup.conditionInitial_historyReachWeight_scale` in
  [ConditionedSourceReach](../Vegas/Game/ConditionedSourceReach.lean) proves the
  exact unnormalized history-reach identity below for every source behavioral
  profile and every nonempty conditional intended history.
* `Vegas.SourceProgram.Setup.conditionInitial_bayesBelief` in
  [ConditionedSourceBayes](../Vegas/Game/ConditionedSourceBayes.lean) gives exact
  mapped Bayes beliefs at an actual source information fiber determining the
  component, using the existing proportional-reach transport theorem.
* [CorrelatedInitialBits](../Vegas/Examples/CorrelatedInitialBits.lean) is an
  actual source with two owner-private copies of one Boolean bit, fresh owned
  commitments and reveals by both players, and Odds–Evens settlement. It proves
  failure of the Unit-signal independence premise, deterministic conditional
  priors satisfying that premise, and recovery of the common bit from each
  player's existing private initial observation.
  [CorrelatedInitialBitsInformation](../Vegas/Examples/CorrelatedInitialBitsInformation.lean)
  proves the actual source decision-information fibers determine their
  component and applies the Bayes transport theorem to them. It reuses the
  source's initial-cell observation and preservation invariants.

This does not yet weaken a raw-runtime SE preservation theorem. It remains to
restrict and glue SE consistency witnesses and continuation rationality, and
transport the actual forced-exit runtime and service hypotheses through
conditioning. The proofs do not assume the signal is ledger-public.

## Where the existing proof uses independence

The relevant declaration surfaces are in
[OnePacketConditionalPrior](../Vegas/Game/OnePacketConditionalPrior.lean),
[OnePacketOwnerKeyed](../Vegas/Game/OnePacketOwnerKeyed.lean),
[OnePacketLateRecords](../Vegas/Game/OnePacketLateRecords.lean), and
[OnePacketSpliceForced](../Vegas/Game/OnePacketSpliceForced.lean).
The active raw capstone is
[forced-exit recovery](../Vegas/Game/RecoverySequentialCompilation.lean).

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

## A genuine extension: an existing signal known to every player

There is a different route that does not compare late sites across the signal
values at all. Suppose the initial draw is X with finite law P. Let U be its
existing public initial data. Assume a finite-valued statistic Z(X) such that
each player i can recover Z from its own actual initial observation:

    Z(X) = z_i(initialObservation_i(X))       on the support of P.

The functions z_i and the prior are common knowledge. This is a property of
existing observations, not a new channel or a revelation event. In particular,
the ledger and scheduler are not given Z. The signal is remembered at every
later player decision. No player chooses before the initial draw.

The retained views support this premise structurally: player-store masking
keeps a player's own private inputs in [Information](../Vegas/EventGraph/Information.lean),
and the [recovery](../Vegas/Pending/ExclusionApplication.lean) player view retains
the native player view even after exclusion. The formal adapter still needs the input
store invariant and initial-to-runtime encoding identity, rather than merely
the view definitions.

Assume that, for every z of positive probability, the conditional initial law
P_z=P(. | Z=z) satisfies the retained private-input-independence hypothesis
given U. In words: after conditioning on the already mutually known signal
and existing public inputs, each player's hidden cells are independent of the
rest. No independence between Z and the program's residual private data is
required beyond this conditional condition.

Under the identity and restriction obligations below, the existing
non-concurrent preservation theorem implies preservation for P. This is a
hand-derived consequence of the checked conditional theorems plus finite
assessment gluing. It is not yet a Lean corollary.

### Conditioning changes only the initial distribution

For each z let pi_z=P(Z=z)>0 and replace only the setup's initial law by P_z.
Context, program, expression interpretation, exit transfers and utilities stay
the same. Consequently the compiled graph, wire alphabet, runtime durations,
response menus, scheduler kernel, reception rule, audit and deposits must be
identified with the original ones. Nobody samples a new scheduler conditioned
on Z, and nobody adds Z to a scheduler or ledger view.

The source's intended local menu is defined from the program and local view,
not from initial masses; see [IntendedGame](../Vegas/Source/IntendedGame.lean).
[Setup](../Vegas/Source/Setup.lean) isolates the initial law as a field. These
are useful identities for the implementation, but do not themselves prove all
the protocol/history transport statements below.

Each supported global history after initialization belongs to one component z.
The conditional game's legal histories are exactly the global histories in
that component, with the same moves, continuations and observations. Every
player decision information set lies inside one component, because its actual
observation/recall determines Z. Terminal observations retain the original
initial draw, rather than replacing it by Z.

### Restricting a source sequential equilibrium

Fix any intended source SE and one common fully mixed consistency sequence
(sigma_n, mu_n) witnessing it. Restrict the strategy to histories in component
z. For every such history h, at every n,

    reach_P(h; sigma_n) = pi_z * reach_Pz(h; sigma_n restricted to z).

Only the initial probability changes; all later chance and behavioral factors
are identical. A player's information set cannot contain another component,
so its Bayes numerator and denominator both gain the same factor pi_z.
The conditional beliefs therefore agree exactly with the restricted global
Bayes beliefs. Full mixing is preserved because local legal menus agree.

Conditional continuation gains are unchanged. The restricted assessment is
thus an SE of the conditional intended game. Its witnesses are restrictions
of the original witnesses, so this step does not choose incompatible source
beliefs separately for different components.

### Applying the existing theorem component by component

Apply the retained forced-exit theorem to each conditional
setup, using the conditional independence premise and U as the public signal.
All-history service properties restrict to a smaller supported initial law:
every conditional legal history is already a global legal history. The same
argument restricts support-dependent well-formedness and value coverage.
Deadline inequalities, payoff bounds, excluded-owner floor, wire capacity and
audit-coverage inequalities are unchanged. Conditional source terminal support
is a subset of global intended terminal support, so its floor premise follows
from the original floor premise.

This inheritance must use support restriction, not an average timing bound.
In particular, a single global service or evidence law is used in all fibers.
If funding is initially specified fiber by fiber, take common utility bounds
and sufficient deposits before choosing an equilibrium; the finite maximum
over fibers is legitimate. The simpler application keeps the original global
bounds and deposits throughout.

Obtain a target SE beta_z and one fully mixed Bayes witness sequence beta_z,n
for each z. No target action may depend on a hidden component: it depends on
Z only because the acting player can compute Z from its actual information.

### Gluing the target assessments

At any global target decision site, use beta_z for its uniquely determined
component. Use beta_z,n similarly to define the global witness at index n.
There are finitely many positive components, so using the same index n gives
simultaneous convergence; no exchange of a limit with an infinite family is
needed. Full mixing is preserved at every global decision menu.

The same reach identity holds for the target witnesses, since their operational
kernels and conditional initial laws have the required identities. Global Bayes
beliefs at a decision site equal beta_z,n's beliefs: pi_z again cancels. The
limiting beliefs are consistent, and every continuation deviation from that
site remains in component z. Its gain is the gain in beta_z, hence nonpositive.
The glued target assessment is therefore an SE of the original raw game.

The initialization may be implemented by a preliminary chance transition.
There is no player information set there to which the gluing argument would
assign a component before it is known. If a proposed protocol allows player
choices before the draw, this proof does not apply to those choices.

For the fixed initialized terminal-observation reader J, let L_z be the law
under beta_z and S_z the conditional intended law. Component preservation gives
L_z=S_z, so

    Law_target(J) = sum_z pi_z L_z = sum_z pi_z S_z = Law_source(J).

No-exclusion and no-charge claims also glue: every globally supported terminal
history lies in a positive component whose implementing law has those
properties. This preserves the original joint law, including the original
private initial cells; it does not replace that law by a quotient outcome.

## Examples and limits of this extension

With two private bits, P(0,0)=P(1,1)=1/2 and all other masses zero, each player
knows Z equal to its own bit. The common prior makes the two copies agree.
Conditional on Z, the initial draw is deterministic, so conditional independence
holds. With no public initial inputs the current theorem's public-signal
hypothesis fails: the original cross products are 1/4 and zero. The gluing
route therefore covers a genuinely excluded initial law without adding public
information or changing any runtime law.

The same argument allows an existing shared private signal together with
independent residual private cells on each signal/public-input fiber. The
shared signal can affect legal source choices, utilities and the selected SE;
the proof is not restricted to players ignoring that signal.

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

## Source and runtime adapter obligations

The source history and Bayes lemmas above discharge portions of the following
obligations. The complete SE and operational theorem still requires:

1. Conditioning a setup changes only its initial probability law; source menus,
   graph/runtime/readers, physical transition kernels and audit are transported
   through explicit identities. No compiler or scheduler is selected per z.
2. Conditional initial support embeds into global support, and the source and
   raw legal histories identify with their component restrictions. This must
   include the actual horizon and any terminalized prefixes.
3. Every source and target player decision information set determines Z, using
   retained initial observations and recall, including after exclusion. There
   are no player decisions before initialization.
4. The reach scaling identity holds for any behavioral profile and its legal
   restriction. Instantiate proportional Bayes transport, and then prove SE
   restriction and finite SE gluing using common fully mixed sequences.
5. All-raw-history service, finite nature, source well-formedness, coverage,
   candidate bounds and settlement premises restrict to each component without
   changing the operational law or giving the scheduler extra information.
6. The fixed initialized joint reader and clean-settlement predicates commute
   with the component embeddings and the finite initial mixture.

The first regression should be the perfectly correlated-bit law above under
the same concrete sequential service used by an independent-bit example.
Prove one actual common-signal instance and the identities it needs before
generalizing. Full-support correlated priors remain a separate open problem;
the existing [prior analysis](https://github.com/elazarg/VegasCore/blob/cb6b8df2d011c678c0c2bc03981feb8b04243048/docs/se-correlated-prior-research.md)
contains the earlier likelihood, coupling and observable-gain directions.

## Reuse boundary for formalization

The word “component” has two different meanings here. In
[ComponentCompletion](../GameTheoryExtensions/Analysis/Protocol/ComponentCompletion.lean),
`GameTheory.Protocol.InformationModel.exists_consistent_pooled_completion` and
`GameTheory.Protocol.InformationModel.exists_consistent_component_completion`
construct equilibrating mixtures of each information agent's local action
laws, optionally with weights pooled across agents. They do not assemble
assessment restrictions of different initial-distribution components. Their
fixed-point and compactness arguments are unnecessary for the finite gluing
proof above: each conditional equilibrium and its witness already exist.

Similarly,
`GameTheory.Protocol.InformationModel.exists_sequentialEquilibrium_limit_of_pooled_comparisons_of_lawError`
in [CopiedSiteLimit](../GameTheoryExtensions/Analysis/Protocol/CopiedSiteLimit.lean)
requires component actions, pooled rationality, local gain comparisons and a
source-law approximation. It could be made to prove a special case only by
supplying substantial obligations that exact information-component gluing
avoids. Re-running that construction would obscure the simple argument.

[ConsistencyCompletion](../GameTheoryExtensions/Analysis/Protocol/ConsistencyCompletion.lean)
exports
`GameTheory.Protocol.InformationModel.BehavioralAssessment.exists_consistent_completion_preserving`
and the corresponding consistent-subsequence theorems. These are useful if
only strategy convergence and tight beliefs are available. They do not provide
rationality or compatibility with a prescribed conditional assessment without
the stated projected-belief convergence premise. In the finite construction
here all conditional assessment sequences already converge. Exact gluing uses
those sequences directly and needs no fresh subsequence or belief choice.

The smaller foundation APIs are closer to the required proof:

* `GameTheory.Protocol.InformationModel.bayesBelief_apply` in
  [BehavioralBayes](../GameTheory/GameTheory/Protocol/BehavioralBayes.lean)
  exposes the exact normalized reach weight. It is the immediate consumer of
  the conditional-initial-law reach scaling identity.
* `GameTheory.Protocol.InformationModel.bayesBelief_projection_of_reach` in
  [BeliefTransport](../GameTheory/GameTheory/Analysis/Protocol/BeliefTransport.lean)
  transports beliefs through an actual history map when reach weights sum
  exactly over fibers. Its current premise has scalar one. Conditional versus
  unconditional reach instead differs by pi_z, so it cannot be instantiated
  directly before accounting for that scalar. The same file's
  `GameTheory.Protocol.InformationModel.bayesBelief_projection_at_depth`
  is appropriate for genuinely different decision depths; conditioning alone
  does not require a depth change.
* `GameTheory.Protocol.InformationModel.informationMass_projection_of_proportional_reach`
  and
  `GameTheory.Protocol.InformationModel.bayesBelief_projection_of_proportional_reach`
  in [ProportionalBeliefTransport](../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean)
  provide the scalar generalization and are used by the actual source Bayes
  consumer. Their fiber-sum premise is
  `scale * target reach = summed raw reach`. The positive finite multiplier
  cancels in Bayes normalization; the source consumer uses scale pi_z inverse,
  from conditional histories to their embedded global histories.
* `GameTheory.Protocol.InformationModel.BehavioralAssessment.IsLimitConsistent.exists_sequence`
  in [BehavioralAssessment](../GameTheory/GameTheory/Protocol/BehavioralAssessment.lean)
  extracts the existing consistency witness. The gluing construction should
  reuse such witnesses rather than merely pick new beliefs independently at
  each zero-probability information set.
* [ActionRestriction](../GameTheory/GameTheory/Protocol/ActionRestriction.lean)
  and [RestrictionExecution](../GameTheory/GameTheory/Protocol/RestrictionExecution.lean)
  provide history/information embeddings and exact continuation-law transport
  when actions are restricted. They preserve the initial history and initialized
  law through their stated structure. Conditioning a chance distribution is
  not an action restriction; their initialized-law theorem does not supply the
  missing change-of-initial-law identity. Their post-initial continuation
  techniques may be reused after an actual history embedding is defined.

No exported finite initial-component SE gluing theorem was found in these
owners or the foundation's protocol-analysis layer. This is an inspected reuse
boundary, not a claim that the whole foundation has been proved to lack one.

### The next sequential-equilibrium obligation

For the actual conditional setup, the source history embedding j_z and the
transported policy sigma_z, the checked reach identity is:

    for every conditional history h after initialization,
    reach_global(sigma, j_z(h)) = pi_z * reach_conditional(sigma_z, h).

The map retains the initial draw and all later actions and outcomes and
preserves length and actual observations. Its bijection on decision-information
fibers requires that the original fiber determine the component. The correlated
bit source proves that premise from each player's actual initial observation
and its retention at every later source decision.
The initialization-free root is excluded from the displayed scaling identity:
both protocols give their root reach one, not pi_z. There is no player decision
there, so this exclusion does not affect Bayes transport at decision sites.

The actual Bayes consumer uses j_z directly, with conditional histories on its
raw side, original histories on its target side and scale pi_z inverse. There
is no need to totalize a new inverse projection or prove another normalization
lemma.

The next result should restrict an existing source SE and its one common
consistency sequence to an observed component, preserving whole-continuation
rationality under the same actual history and choice maps. The source-law and
Bayes lemmas do not themselves transport continuation deviations or prove
consistency of a selected limiting conditional belief system. Derive those
properties and instantiate them on the correlated-bit source before attempting
runtime SE gluing. The forced-exit runtime and finite gluing steps remain
distinct obligations; the source regression is not raw SE preservation.
