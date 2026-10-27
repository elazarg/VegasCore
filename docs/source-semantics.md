# Source semantics

[Source programs](../Vegas/Source/Basic.lean) are finite typed descriptions of
public sampling, owner-private commitment, guarded reveal and return. The
initial state can contain public data and persistent owner-private inputs drawn
from a joint initial law. Owners and the instruction order are fixed by the
program; the language has no branching or loops.

The continuing instruction evaluator represents failed commitment or revelation
as an explicit result. The intended analysis game restricts to successful
commitments and openings. The retained Nash results and the source SE extension
distinguish these views. The runtime additionally accounts for silence through
expiry and the stated failure rule; failure in the source evaluator must not be
silently identified with every runtime continuation.

The non-concurrent SE results start with an intended-game equilibrium. They
construct a raw-runtime equilibrium with no failures on its supported path,
while proving rationality at off-path runtime information sets. Their failure
payoff and conditional-prior hypotheses are explicit. They do not assert that
every equilibrium of a general source game with strategic withholding survives.

Guards read the source's permitted public data and their author's commitment.
The guard and revelation invariants are pinned in [Paper](../Paper.lean).
Executable transfers and an external valuation are separate utility components;
the monetary specialization retains the realized settlement law.

See [the exact preservation scope and open source questions](sequential-se-open-problems.md).
