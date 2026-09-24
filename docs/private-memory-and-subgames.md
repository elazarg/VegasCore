# Private implementations and semantic game histories

## The game boundary

The reactive game records semantic responses: an optional submission or replay,
the player's pre-response view, and the actual emitted envelope. It has no
auxiliary response-memory field. A cache, random seed, private counter or stored
compiler intention belongs inside the strategy implementation.

Private types, binding meanings, observations and semantic own-action recall
remain part of the game. In particular, fixing a commitment value changes which
future openings can succeed. This is a semantic effect even though the value
does not appear in the public packet.

This boundary is independent of finiteness. We impose no finite carrier or
representation bound on private strategy memory. Internal computation consumes
no extra activation or modeled clock time.

## Checked realization

The generic construction in
[PrivateStrategy.lean](../GameTheoryExtensions/Protocol/PrivateStrategy.lean)
starts with an initial private-state distribution and a response kernel from
state and observed input to output and new state. Conditioning on the player's
own input/output transcript produces a behavioral policy. Its definition is
independent of opponents, the environment and utilities.

`PrivateStrategy.realize` proves equality of the complete external state and
transcript law against an adaptive environment, provided the environment cannot
inspect private implementation state directly. All distributions have finite
support; the memory carrier need not be finite. The policy is total, including
at zero-probability transcripts through the conditional-distribution fallback.
That fallback is not an equilibrium argument.

The actual reactive adapter is
[ReactiveImplementation.lean](../Interaction/ReactiveImplementation.lean).
It reconstructs each past input from the player's recall prefix and the view
recorded at that response. `Implementation.realize` proves whole-execution law
equality from an arbitrary execution, with implementation state distributed
according to this local posterior. `Implementation.realize_initial` starts
from the implementation's own initial state distribution. Both allow arbitrary
opponents, schedulers and passive observation rules. The result retains the
application, network, receipts, player recall and scheduler recall, while omitting
internal implementation state.

These are playerwise results: replacing one player's implementation by its
behavioral realization leaves the others fixed. They cover arbitrary private
implementations, not just prescribed compiler code. They do not equate execution
from every individually fixed internal state with execution from the behavioral
policy: its continuation uses the posterior over those states.

The [reactive regression](../InteractionTests/ReactiveImplementation.lean)
checks two submissions correlated by one retained private bit. It also proves
that an implementation with an arbitrary initial distribution on an unbounded
private counter realizes the constant silent policy at every information state.

## Compiler intentions

[ReactivePolicy.lean](../Vegas/Pending/ReactivePolicy.lean) defines prescribed
and recovery implementations whose internal state is a list of source
intentions. Their behavioral realizations are the corresponding reactive
policies. The compiler completes prescribed play with recovery after unsupported
semantic responses. A player cannot inject arbitrary intention tags into game
actions or histories.

The distinction matters for failed disclosures: intending to disclose and
intending to withhold can emit exactly the same packet. The implementation
retains the sampled intention; its realization averages over internal states
consistent with actual observations and responses. Later behavior can therefore
depend on that retained randomness without introducing another game action.
Accepted packet identifiers determine which internal intention can reconstruct
source recall. Binding recall uses the value that actually took effect.

`compileReactivePolicy_realizes` in
[ReactivePolicyFacts.lean](../Vegas/Pending/ReactivePolicyFacts.lean) proves the
initialized execution-law equality between the prescribed private implementation
and the actual completed compiler policy, against arbitrary opponents and
scheduling. This is an implementation/behavioral-policy theorem, not the
source-game compilation theorem or an equilibrium preservation result.

## Credibility and remaining obligations

Auxiliary implementation distinctions should not create canonical histories or
alter proper-subgame boundaries. Genuine private information still limits what
ordinary SPE checks. The checked
[SequentialCredibility.lean](../GameTheoryExtensionsTests/SequentialCredibility.lean)
fixture has a private source bit and no scratch-memory actions: SPE permits a
strictly inferior off-path response that no belief system makes sequentially
rational. The credibility target therefore remains sequential equilibrium.

The [finite semantic response menu](finite-reactive-responses.md) removes
unavailable replays and ineffective private submission annotations from legal
actions. Its normalization certificate preserves the exact packet and the full
one-step application/network effect. It retains fresh hidden meanings and all
bounded malformed traffic. The compiler, including recovery, emits normal forms.
This is not a whole-policy or equilibrium quotient theorem for the raw syntax
game, whose sender recall can record the erased distinctions.

The remaining obligations are:

1. Justify any further identification of responses by semantic proofs. Removing
   auxiliary memory alone does not justify treating all syntactically different
   responses as strategically meaningful, or all rejected packets as silence.
2. Connect the complete bounded packet menu to a backend encoding and prove
   compiler coverage of its finite value and handle domains. Justify the
   interaction bound: the [sequential design](sequential-equilibrium-design.md)
   records it as a substantive restriction, not a consequence of contract timeouts.
3. Prove source-observation reconstruction and whole-service compilation laws.
4. Construct one common tremble sequence, transport off-path beliefs, and prove
   the continuation incentive condition for the realized compiler.

Behavioral realization does not prove sequential rationality or consistency,
nor does it guarantee that every public checkpoint starts a proper subgame.
No native sequential-equilibrium preservation theorem is claimed.
