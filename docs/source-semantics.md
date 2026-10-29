# Source semantics

[Source programs](../Vegas/Source/Basic.lean) are finite typed descriptions of
public sampling, owner-private commitment, guarded reveal and return. The
initial state can contain public data and persistent owner-private inputs drawn
from a joint initial law. Owners and instruction order are fixed by the
program; the language has no branching or loops.

The [configuration evaluator](../Vegas/Source/Semantics.lean) represents binding
omission separately from accepted unusability. Omission publicly defaults its
owner; an accepted unusable binding remains opaque until public opening fails.
A failed reveal defaults its owner. Later owned instructions complete
mechanically, without a policy callback or an invented own action. Samples and
other players continue. Public views retain the full default history.

The source protocol uses the same instruction successors as the evaluator.
The graph compiler preserves complete configurations and public default timing
for every source profile and public graph scheduler. The ledger application
derives default control from that graph configuration:
`Vegas.EventGraphRuntime.State.completeAutomatic_step` represents each
automatic completion by a supported step of the same graph executor.

The [replacement scope](source-absorbing-failure.md) records checked operational
refinement and outstanding probabilistic client, deviation, monetary and
equilibrium ports. The full repository and paper guards remain acceptance
gates. In particular, an operational graph-path theorem alone does not imply
preservation of every source sequential equilibrium.

Guards read permitted public data and their author's commitment. Executable
transfers and an external valuation are separate utility components. A
publicly defaulted player's source utility is its specified fixed exit value;
monetary interpretation still needs its settlement correspondence.

See [the preservation scope and open questions](sequential-se-open-problems.md).
