# Source semantics

This page describes the continuing instruction evaluator used by the retained
plain-contract results. The chosen operational source game instead uses
permanent exit with commitment-phase retries, retained recall and declared exit
transfers. Its [semantic contract](common-semantics-contract.md) and
[source phase game](../Vegas/Game/SourcePhaseGame.lean) state the checked policy
and the remaining correspondence obligations.

[SourceProgram](../Vegas/Source/Basic.lean) is a finite typed program with four
constructors: return, public sample, private commitment and guarded reveal.
The initial context can contain public data and persistent owner-private inputs.
Fresh commitment and publication cells carry an explicit success or failure
result. Failure is a value in the semantics, not an exception or missing state.

The language has four limits. Programs are straight-line: no constructor
branches on a value or repeats. The owner of each commitment and reveal is
fixed by the program text. Every owned move is a commitment followed by a
reveal of it. A guard reads public data, publications and its author's own
commitment, never private inputs or other players' unpublished commitments
(`Vegas.SourceGuardRead`).

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

[Program payment utility](../Vegas/Game/ProgramPayoffs.lean) evaluates the return
expressions on the public outcome and sums the integer entries for each player.
Strategic utility adds a separately supplied valuation to these monetary
receipts. `Vegas.SourceProgram.canonical_transfer_law` preserves the evaluated
transfer vector through canonical compilation. The
[payment-dependent program](../Vegas/Examples/ProgramPayments.lean) exercises this
interface; the existing equilibrium capstones still accept utility parameters.

[Semantics](../Vegas/Source/Semantics.lean) owns observations, evaluation and
source policies. [Protocol](../Vegas/Source/Protocol.lean) connects them to the
finite game model. The [compiler design](compilation-design.md) describes the
runtime boundary; the [README](../README.md#checked-results) lists the checked
equilibrium results.
