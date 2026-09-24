# Auxiliary memory weakens SPE in the native representation

## Checked finding

The reactive protocol records an arbitrary private memory value in every
player response. Under the canonical definition of a proper subgame, this
has a substantial consequence:

> After a player has responded, a proper subgame can contain future decisions
> only by that same player. After two distinct players have responded, a proper
> subgame can contain no further player decisions.

This is proved for every reactive application whose memory type has at least
two values, every scheduler, every passive observation rule, every initial
distribution, and every horizon. It includes off-path histories. Remaining
chance or service steps are allowed; the conclusion concerns player decisions.

The proof is in
[ReactiveMemorySubgames.lean](../Interaction/ReactiveMemorySubgames.lean):
`not_subgameRoot_of_foreign_recall`, `subgameRoot_future_actor_eq`, and
`subgameRoot_no_future_decision_of_two_responders`.
The [Vegas theorem](../Vegas/Pending/ReactiveSubgameInformation.lean) proves the
obstruction while changing only `ResponseMemory.privateData`, preserving every
remembered source intention. The
[adapter regression](../VegasTests/ReactiveSubgameInformation.lean) also checks
the two-responder consequence for the actual runtime.

This does not prove SPE preservation impossible. It shows that the raw native
SPE predicate omits the multiplayer continuation checks we intended it to
express. A preservation theorem could be correct while inheriting that weak
coverage. This issue must be addressed before evaluating the sufficiency or
realism of further scheduler assumptions.

## Why one idle bit matters

Consider the following two legal histories:

| Event | First history | Second history |
|---|---|---|
| Alice responds | Records private bit 0 and sends nothing | Records private bit 1 and sends nothing |
| Application and network | Unchanged | Unchanged |
| Scheduler | Activates Bob | Activates Bob |
| Bob's observation and recall | Identical | Identical |

The complete canonical histories differ. Bob's information set therefore
contains a node under each history. A subtree rooted at one of his decision
nodes excludes the other, so it cuts his information set and is not a proper
subgame. [The small reactive regression](../InteractionTests/ReactiveMemory.lean)
constructs both initialized histories and proves the root failure. It has a
unit application state, no transmissions, and no leaked packets.

This is not a preparation turn or a computation cost. The bit is recorded
inside the existing atomic response. Coalescing consecutive turns does not
remove this particular representational distinction.

### Why the general theorem holds

[ReactiveMemory.lean](../Interaction/ReactiveMemory.lean) relabels the auxiliary
memory in one player's past responses. It leaves submission material,
commitment meanings, application state, packets, ledger, receipts, clocks,
and scheduler recall unchanged. It also leaves every other player's entire
information state unchanged.

`mapMemory_transition` proves equality of the transformed one-step laws.
`mapMemoryTrace` consequently maps every legal initialized history to another
legal history under the same scheduler and observation rule.

Suppose a proposed root follows Alice's response and contains a future Bob
decision. Change Alice's recorded memory to a value different from her first
remembered value. The transformed Bob history is still legal and gives Bob
the same information. It cannot descend from the original root: recall-prefix
preservation would require its first Alice memory to equal the original value.
Subgame closure is contradicted. Applying this argument to two distinct earlier
responders rules out every future decision inside a proper subgame.

Even a later message claiming Alice's old memory does not prevent the
construction: the transformed history keeps that message unchanged. The
application never authenticates the arbitrary scratch-memory field.

## Required semantic boundary and proved first step

Represent auxiliary memory as state of the **strategy implementation**, rather
than as an additional game action recorded in canonical histories. Keep actual
submission effects, binding meanings, private types, observations, and their
legitimate own-action recall in the game. In particular, privately fixing a
commitment value has a semantic effect and is outside the memory relabeling
theorem above.

This is a correction of the game boundary, not a request to bound private memory
or preserve the equilibria of the memory-expanded game. The required connection
to implementations is behavioral: preserve their interaction with the environment
and their available behavioral deviations. Equilibrium preservation must then
be proved for the corrected game, with its actual information sets.

Deleting the memory field alone would be inadequate engineering. A private
random seed can correlate several responses, and the compiler remembers source
intentions when several source choices emit the same packet. Those behaviors
need a realization proof.

The generic first step is proved in
[PrivateStrategy.lean](../GameTheoryExtensions/Protocol/PrivateStrategy.lean).
A strategy has an initial private memory distribution and a response kernel
from memory and observed input to output and new memory. A behavioral policy
conditions the memory distribution on its own input/output transcript and
samples the next output. This policy is fixed independently of the environment
and utilities.

`PrivateStrategy.realize` proves equality of the complete external state and
transcript law for any finite number of responses, against any adaptive
environment whose evolution depends on the output and its own state, with no
direct access to private strategy memory. The proof handles correlated private
randomness. All probability laws have finite support; their carriers need not
be finite. The policy is also defined at zero-probability transcripts using the
existing total conditional-distribution operation.

The [correlation regression](../GameTheoryExtensionsTests/PrivateStrategy.lean)
reuses one private random bit twice. The environment echoes the first output
as the second input; the player xors its input with the retained bit. The first
output is random and the second is certainly false. The realized behavioral
policy has exactly that law without recording the bit as a separate game action.

### Remaining obligations

The generic realization result is not a reactive policy adapter or an SPE
equivalence theorem. Before changing the production action representation:

1. Define precisely which parts of a response are semantic effects and which
   are private strategy implementation state. Audit ineffective operations such
   as a replay request for an unavailable identifier; removing `privateData`
   alone has not been proved sufficient.
2. Instantiate realization for the actual player view and response recall,
   including remembered source intentions and repeated activations. Prove
   playerwise execution/deviation correspondence uniformly over opponents and
   services. Do not condition on unobserved network or application state.
3. Preserve private inputs, binding at submission, partial foreign leaks,
   reactions before inclusion, and the actual remaining opportunities.
4. Recompute proper roots in the resulting game and audit the source's private
   action distinctions as well. Outcome equivalence by itself does not imply
   equivalence of SPE, as the existing information experiments demonstrate.
   As an acceptance test, require a public two-player sequential game to retain
   its second player's continuation obligation when the implementation uses an
   irrelevant private random seed. That test is not yet implemented for a
   revised reactive representation.
5. Apply the [incentive criterion](spe-incentive-criterion.md) to the resulting
   source and target presentations. Continue the service proof only with that
   meaning of the target guarantee explicit.

These are proof obligations, not established consequences of removing memory.
The production response type and compiled policies still include auxiliary
memory; their refactor is required and remains open.

## Other equilibrium interfaces

A requirement about credibility after public checkpoints may instead call for
an equilibrium notion that explicitly handles sets of indistinguishable
histories. The FOSG literature makes public information explicit to support
such decomposition; it does not turn every public checkpoint into a singleton
canonical subgame. See Kovařík et al.,
[Rethinking Formal Models of Partially Observable Multiagent Decision Making](https://arxiv.org/abs/1906.11110).

Sequential equilibrium checks optimality at information sets using beliefs,
including off-path information sets. It is a different preservation claim,
with belief consistency as an additional obligation. See Kreps and Wilson,
[Sequential Equilibria](https://www.gsb.stanford.edu/faculty-research/publications/sequential-equilibrium).
The [sequential-equilibrium design](sequential-equilibrium-design.md) specifies
the credibility target and the obligations for using GameTheory's existing
assessment definition. No native sequential-equilibrium or public-checkpoint
preservation theorem is claimed. Repairing auxiliary-memory representation
alone does not establish rationality under genuine private information.
The checked
[SequentialCredibility.lean](../GameTheoryExtensionsTests/SequentialCredibility.lean)
fixture demonstrates this distinction without scratch-memory actions: a private
source bit prevents a proper subgame at Bob's off-path decision, and SPE permits
a response that is strictly inferior under every belief. Removing implementation
memory therefore does not remove the reason to target sequential equilibrium.

## Consequences for existing results

The initialized Nash/Bayesian compiler theorems and exact finite-outcome
incentive-cone characterization retain their stated scopes. The reactive
one-player counterexamples are also unaffected by this diagnosis: their roots
and profitable deviations are independently proved, and the memory theorem
excludes future **foreign** decisions.

For the multiplayer positive theorem, it would be misleading to count missing
subgames as a successful treatment of noncredible threats. This is a
representation issue to resolve, rather than another miner assumption to add.
