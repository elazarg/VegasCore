# Semantics spine

The active semantic chain has three objects.

1. A checked sequential source program executes in written order. A player's
   policy sees only the declared source-visible environment at each choice.
2. Compilation produces a typed event graph. Nodes retain ownership,
   dependencies, guards, finite probability tables, and payoff expressions.
3. A native application consumes public messages through `Interaction`.
   Message execution is compared directly with reachable graph prefixes.

The graph is an executable compiler artifact, not merely an analysis view.
Retaining syntax and probability tables is necessary for downstream runtimes;
evaluator closures alone cannot be inspected or lowered.

The principal correctness boundary is support-level: native steps preserve a
graph witness, and a completed supported native run reconstructs a written-order
source execution with the corresponding public result. Probability,
information, and strategic claims require their own explicit hypotheses and
are not consequences of reachability alone.
