# Source semantics

[SourceProgram](../Vegas/Source/Basic.lean) is a finite typed program with four
constructors: return, public sample, private commitment and guarded reveal.
The initial context can contain public data and persistent owner-private inputs.
Fresh commitment and publication cells carry an explicit success or failure
result. Failure is a value in the semantics, not an exception or missing state.

A public sample uses its declared kernel on the public source environment.
A commitment chooses a private typed value or failure. A reveal chooses TRUE
or FALSE. TRUE attempts publication of the committed value and checks the
completed guards; FALSE produces publication failure. Failed validation also
produces failure. The program continues according to its fixed syntax.

Player information consists of public values, owned private inputs and
commitments, and original own action recall. Other players' unpublished values
are masked. Equal public results do not erase the distinction between an
original TRUE with failed validation and an original FALSE.

Return expressions read the public source context. Preservation theorems can
also parameterize utilities by initial inputs and public results; their exact
payoff domain is stated in the theorem. Private implementation state is not
silently added to that domain.

[Semantics](../Vegas/Source/Semantics.lean) owns observations, evaluation and
source policies. [Protocol](../Vegas/Source/Protocol.lean) connects them to the
finite game model. The [compiler design](compilation-design.md) describes the
runtime boundary; the [SE plan](se-schedule-generalization.md) states the
required equilibrium result and its remaining obligations.
