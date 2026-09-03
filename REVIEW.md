## Bottom line

The strongest paper VegasCore is close to is not an end-to-end verified game-to-blockchain compiler paper.

It is a mechanized semantics paper along these lines:

> A well-formed finite VegasCore program compiles to a bounded imperfect-information game with perfect recall. Terminal
> graph executions reconstruct valid source executions with the same payoff, and behavioral and product-mixed-pure
> strategy presentations are mutually deviation adequate, so their outcome laws and Nash equilibria correspond.

Most ingredients are already proved:

- Terminal source-payoff reconstruction: Vegas/Compile/SourceAdequacy.lean:441
- Bounded horizon and perfect recall: Vegas/EventGraph/Protocol.lean:381, Vegas/Machine/Program.lean:122
- A finite-domain game construction: Vegas/Game.lean:36
- Behavioral↔mixed-pure deviation-adequacy certificates: Vegas/Game/Kuhn.lean:360
- Nash preservation/reflection from deviation adequacy: Vegas/Runtime/DeviationAdequacy.lean:236
- Exact FOSG→EFG behavioral-law and Nash results exist in the imported GameTheory library: GameTheory/GameTheory/
Languages/Bridges/FOSGToEFGStrategic.lean:240

The development is technically healthy. The entire Lean build succeeds—3,200 build jobs—and the paper-facing axiom
audits pass. Vegas itself is 107 Lean files/~29k lines; the GameTheory dependency is another 452 files/~111k lines. The
pinned Kotlin compiler’s mvn -q test also exits successfully; its reports contain 499 testcase elements with no failures
or errors.

## What the existing result actually says

The project currently has three strong but separate layers:

1. Source program → event graph

    Every terminal compiled execution reconstructs a possible written-order source execution with the same payoff. This
    is support-level, endpoint correctness. It is not equality of probabilistic laws or a strategy-preservation theorem.

2. Event graph → canonical game

    The graph induces a bounded FOSG with perfect recall. Player commitments at a strategic frontier are submitted
    jointly and serialized canonically. Internal nodes, however, are selected noncomputably with Classical.choose: Vegas/
    EventGraph/Protocol.lean:241.

3. Behavioral game ↔ product-mixed-pure game

    This is the strongest concrete deviation-adequacy instantiation. It is a substantial Vegas-specific application of
    the generic Kuhn machinery, and it really does support Nash equivalence.

What does not yet exist is an end-to-end deviation-adequacy certificate from a source strategic semantics to a generated
contract game. In fact, there is not yet a source-level strategy game corresponding to the raw program semantics. This
distinction should become the organizing honesty condition of the paper.

## The paper I would aim for

The best near-term paper would be something like:

“Mechanized Strategic Semantics for Compiling Partial-Information Games”

The contribution should be presented as:

- a proof-carrying typed core;
- compilation into a canonical concurrent event structure;
- operational source-payoff soundness;
- extraction of a bounded perfect-recall stochastic game;
- exact equivalence of standard strategic presentations;
- deviation adequacy as the interface required for later runtime passes.

To make that a convincing paper rather than a collection of library theorems, I think three additions are essential:

1. One umbrella theorem. Package the source, boundedness, perfect-recall, finite-domain, and behavioral/mixed-pure
    results into one publication-facing theorem with every assumption visible.

2. One real mechanized case study. The matching-pennies test exercises a remarkable amount of the infrastructure, but it
    never defines the equilibrium, proves it is Nash, or transports it through the representations: VegasTests/
    Game.lean:1262. Do that for Odds–Evens or matching pennies.

3. One result where deviation adequacy does genuine compiler work. At present, its generic Nash theorem follows quite
    directly from the fields of the definition, and its main concrete instance is Kuhn equivalence. It needs either a
    real runtime certificate or a checked counterexample showing exactly why one cannot exist.

## The strongest enhanced version

The most valuable additional theorem would connect the scheduling work to an actual compiled game:

> Publicly serializing independent player actions introduces a target strategy that cannot be uniformly backtranslated,
> while the canonical joint-frontier semantics restores deviation adequacy.

Ideally, prove this for the same Odds–Evens example in both forms:

- a negative implementation with observable incremental scheduling;
- a positive atomic or observation-restricted implementation;
- a concrete changed equilibrium or failure of deviation adequacy.

That would turn the paper from “here is a good correctness definition” into “here is a machine-checked diagnosis of a
real compiler bug class, and here is the compilation discipline that prevents it.” The infrastructure is close: the
repository already proves schedule observability, distinct schedule-sensitive strategy carriers, deterministic versus
permissive checkpoint behavior, and commuting base states. But those results currently live in a separate synthetic
ScheduledSystem; they are not connected to compiled Vegas programs.

## Claims that are currently unsupported or overstated

Several draft claims should be removed or narrowed immediately.

- The abstract says schedule signals can sustain correlated equilibria and that advance and incremental disclosure are
incomparable: overleaf/main.tex:38. I found no corresponding VegasCore theorem; “incremental” does not occur in the
formalization, and correlated equilibrium appears only in comments or proposed work.

- “Source-payoff adequacy” is one-way terminal reconstruction. The prose calling part of that a “support-level converse”
is confusing: overleaf/sections/03-language-graph.tex:126. There is no source/target law equality here.

- The “native frontier game to FOSG” translation is not a separate proved translation: the Vegas arena is directly
defined as a FOSG in Vegas/Game.lean:86. The EFG result is substantial, but imported from GameTheory and should be
attributed as such.

- The paper-facing schedule-confluence theorem is algebraic permutation invariance for completing a fixed assignment:
Vegas/Paper.lean:79. The operational local diamond theorems are stronger and more relevant. The prose currently blends
these levels.

- Vegas/Paper.lean:16 says every paper theorem is restated there and absent claims are unsupported. Yet it does not
expose perfect recall, bounded horizon, or FOSG/EFG adequacy, all of which the paper claims.

- “Checked program” currently means a manually constructed proof-carrying WFProgram: Vegas/Core/WellFormed.lean:56. The
core compiler is noncomputable, and there is no raw Vegas syntax→WFProgram proof-producing checker. Calling the Lean
side an “executable graph compiler” is therefore misleading.

- The language descriptions disagree in small but semantically meaningful ways. For example, Lean payoffs may omit a
player or contain duplicate entries, which are summed: Vegas/Foundation/Payoff.lean:20. The Kotlin IR instead claims
one payoff expression per strategic role.

- Lean’s Legal obligation quantifies over every visible environment, not just reachable ones: Vegas/Core/
Obligations.lean:281. This is a stronger and potentially more restrictive language boundary than the paper currently
suggests.

## Why the blockchain paper is not close yet

The runtime tower is impressively developed, but it currently establishes adjacent representation and code-generation
facts—not strategic preservation to a public blockchain.

The decisive gaps are:

- BooleanCompilationCorrect is stated but unproved: Vegas/Compile/EVMRefinement.lean:192.
- The EVM semantics is gas-free, partial, and explicitly not validated against Ethereum’s conformance suite: Vegas/
Machine/Contract/EVMExecution.lean:11.

- IdealVisibility explicitly models hiding that public EVM storage does not provide: Vegas/Machine/Contract/
IdealVisibility.lean:12.

- The Lean EVM path does not cryptographically realize sealed commitments; the supported handlers store typed action
values.

- There is no target game including public traces, transaction ordering, inclusion, nonresponse, deadlines, fees, gas,
oracle deviations, or external utility.

- Settlement is currently an outcome readout, not verified movement of assets.
- Kotlin and Lean implement related architectures independently. There is no checked interchange format or translation
validator.

- The Kotlin repository’s README currently claims faithful preservation of strategic properties and on-chain realization
of commit–reveal. Those claims are materially stronger than either artifact establishes.

The long draft’s status ledger is unusually accurate about these gaps: overleaf/Long/sections/a-status-ledger.tex:27. I
would treat it as the authoritative engineering plan and rewrite the short draft to agree with it.

## Artifact and positioning problems

The paper is not currently reproducibly tied to the reviewed code:

- It pins VegasCore commit cb814f3, while the current tree is 21 commits later with roughly 3,263 insertions.
- The draft reports 39 examples and 494 tests: overleaf/sections/07-artifacts.tex:28. The pinned Kotlin repository
currently contains 42 .vg files and emits 499 testcase records.

- overleaf/ is gitignored, so the reviewed paper is not versioned with the theorem surface.

The related-work section also misses the nearest conceptual predecessors. Halpern and Pass already relate mediator
implementation, deviating machines, distribution preservation, and equilibrium preservation in a cryptographic/game-
theoretic framework: Game Theory with Costly Computation. BitML is closer than the current paragraph suggests because it
has a computational-soundness story for compilation to Bitcoin, followed by an Agda verified-compilation development:
BitML, verified BitML compilation. The recent Pseudo-Equilibria paper directly addresses transferring equilibria from
ideal cryptography to real protocols.

Deviation adequacy can still be a good contribution, but its novelty should be claimed as an exact, finite, machine-
checked compiler interface—not as the first connection between deviation simulation and equilibrium preservation.

## Recommended order of work

1. Freeze and name one finite supported fragment.
2. State one umbrella theorem and make Vegas.Paper genuinely exhaustive.
3. Add one equilibrium-carrying mechanized example.
4. Prove the connected scheduling counterexample and positive canonical alternative.
5. Correct the abstract, theorem descriptions, attribution, README claims, and artifact counts.
6. Either build the Kotlin→Lean translation validator or present the artifacts unequivocally as independent.
7. Leave public-chain strategic adequacy and whole-handler EVM verification to a later paper.

Without item 4, there is still a credible formal-semantics/library paper. With item 4, I think there is a notably
stronger paper: one that explains, formally and concretely, why ordinary operational compiler correctness is
insufficient for games and how a particular concurrency discipline repairs it. The blockchain paper requires a different
scale of additional work.