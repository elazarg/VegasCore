# Open paper-to-Lean audit items

These are reported review findings awaiting independent revalidation against
the current manuscript and Lean source. They are not confirmed defects or
completed fixes. Handle them separately from the proposed concurrent-runtime
implementation; the [resume guide](se-preservation-resume.md) covers that work.

The manuscript is maintained in the separate private `overleaf/` repository.
Every stated mathematical result needs an exact guarded pin in
[Paper.lean](../Paper.lean), and Paper should pin no unrelated results.

| Item to recheck | Action if confirmed |
|---|---|
| The prose claim that no intended-game publication fails in a well-formed setup lacks an exact pin. | Locate the precise safety result, add its guarded Paper pin and annotate the corresponding manuscript claim. |
| The Paper pin for the general client-menu Nash reflection direction may exceed what the manuscript states. The raw-interface direction is already part of its correspondence result. | Compare both exact statements to the paper, then remove only an unsupported extra pin and annotation. |
| The prose after the Nash theorem claims that every unilateral native policy against first-turn clients has the outcome law of a source deviation allowing failed bindings. | Check the statement of `Vegas.asyncDeviation_readout_law`; add its exact pin and manuscript annotation if that is the stated claim. |
| Finite branching of the builder is stated at the recovery theorem but may be missing from the general builder description. | State the finitely branching law where it is first required. |
| “Compile either graph” is expressed through a barrier-order hypothesis rather than directly through the permitted service modes. | Check the compiled graph facts and consider stating exclusion of the concurrent-reveals mode in the Paper restatement, deriving barrier order internally. Preserve the exact supported graph scope. |
| Reaction-bound notation and deposit notation both use the letter d. | Disambiguate the manuscript notation. |
| The concurrent theorem's exact tape-gap premise may be absent from its prose. | State the premise if retaining that theorem. This item is moot only if the owner removes the theorem. |
| [Semantics and enforcement](semantics-and-enforcement.md) describes the concurrent theorem as absent from the paper. | Reconcile the description with the actual manuscript scope after the editorial decision. |
| The late-leak theorem and supporting results have not received the complete paper-to-Lean walkthrough covered by this audit. | Read their statements, hypotheses, quantifier order and exact pins together. Do not infer coverage from a passing source-policy checker. |

The recovery deadline issue is reported resolved, as are the concurrent TODO
and headline qualification; neither is listed here as an outstanding fix.
Revalidate them if the affected theorem statements change. A documentation
reference check only establishes that a name exists, not that the manuscript
states the same mathematics.
