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

The [semantics guide](source-absorbing-failure.md) relates this execution to
ordinary client correctness, unilateral deviation backtranslation and intended
sequential-equilibrium compilation. Operational graph paths and probability
laws have separate capstones with their stated service and strategic premises.

Guards read permitted public data and their author's commitment. Executable
transfers and an external valuation are separate utility components. A
publicly defaulted player's source utility is its specified fixed exit value;
the monetary compiler preserves the corresponding settlement and cash law.

See [the preservation scope and open questions](sequential-se-open-problems.md).
