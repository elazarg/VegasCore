# Source and compiler proof ownership

The compiler tail-order consumers and lower recovery-step eliminator are
integrated in their actual owners. Both complete compiler modules and all five
source owner/consumer modules pass strict checking with the central Lake setup.
The mathematical declaration statements are unchanged.

## Compiler tail order

`ContextRefsBefore.tail_cons` in
[EventGraphCompiler](../../Vegas/Compile/EventGraphCompiler.lean) proves that a
new head reference and all old references precede the residual outputs. Its
hypotheses include the actual source tail, event-count equality, output-layout
correspondence and the head field's identity.

The sample, commitment and reveal branches of both
[EventGraphLaw](../../Vegas/Compile/EventGraphLaw.lean) and
[EventGraphPolicyAlignment](../../Vegas/Compile/EventGraphPolicyAlignment.lean)
instantiate that owner. The dependent publication cast is covered by the same
factual equality. Policy normalization, legal source actions, decoded history
and partial readout stay in their original consumers.

Six substitutions remove **42 physical lines**, with no new API or imports.

## Recovery-step support

`CommitRecoveryState.step_raw_result` is directly after step in
[CommitRecoveryState](../../Vegas/Source/CommitRecoveryState.lean). It exposes the
actual raw recovery result, its exclusion-monotonicity witness and the exact
installed-and-closed target. The higher
[CommitRecoveryAttemptReset](../../Vegas/Source/CommitRecoveryAttemptReset.lean)
uses that owner.

Four actual consumers use it:

| Consumer | Owner | Physical proof lines |
| --- | --- | ---: |
| step_control_lt | [CommitRecoveryControl](../../Vegas/Source/CommitRecoveryControl.lean) | 42 to 35 |
| step_potential_lt | [CommitRecoveryState](../../Vegas/Source/CommitRecoveryState.lean) | 45 to 38 |
| clear_step_source | [CommitRecoveryProjection](../../Vegas/Source/CommitRecoveryProjection.lean) | 26 to 19 |
| step_own_history | [CommitRecoveryOwnHistory](../../Vegas/Source/CommitRecoveryOwnHistory.lean) | 21 to 14 |

The family removes **28 physical lines**. The existing eliminator has no new
mathematical assumptions. Only the potential result requires Fintype Player;
control and projection retain their broader scopes. Retries, exhaustion,
original owned history and automatic closure are preserved.

## Scanner reliability

The scanner in [lean-defs.py](../../lean-defs.py) distinguishes result-type
let/have assignments from the actual proof assignment, including nesting,
comments, strings and quoted identifiers. Four regression tests cover inventory
bodies and preserved declaration surfaces; all 100 Python tests pass.

The corrected review inventory has 3,705 cross-file eight-line windows at its
stated production baseline. These are search leads: the scanner is lexical,
equation-style declarations lack complete body coverage, windows overlap and
renamed variants can be missed. Old and corrected totals cannot measure proof
compression. The exact savings above count complete physical proof/module
lines and include the owning helper movement.

The two large repair inductions still build different repaired configurations
and source relations. A common simulation certificate or generic rank framework
has no checked full-family saving and is not introduced. The executable auction
retains actual transfers, separate valuations and its withholding obstruction.
