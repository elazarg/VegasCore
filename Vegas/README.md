# Vegas

This is the mainline language and backend implementation for the project.

Structure:

- `Expr/` — generic expression-language boundary and concrete instantiation
- `Protocol/` — Vegas syntax, static side conditions, and examples
- `BigStep.lean` — canonical denotational semantics
- `TraceSemantics.lean` — trace-based semantics
- `ActionGraph.lean` — graph extraction and graph-level execution model
- `Strategic.lean` — kernel-game bridge and strategic corollaries
- `MAID/` — the main backend and its correctness work

Direct EFG compilation is not part of the mainline layout. If EFG is needed, the
intended route is through the `GameTheory` MAID -> EFG bridge.
