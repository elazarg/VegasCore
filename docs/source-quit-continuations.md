# Source quitting conditions and continuation comparison

## Checked quantitative boundary

The candidate-message theorem compares an arbitrary native unilateral deviation
with a legal source deviation against unchanged opponents. For source quitting
cap `c_i` and source support floor `f_i`, it proves

```text
E[U_i(native)] ≤ E[U_i(source alternative)]
                 + (c_i - f_i) * Pr[native timeout].
```

Both bounds are source-defined. The cap ranges over all legal terminal source
executions recording the player's designated quitting value. The floor ranges
over the supports of all unilateral source deviations against the fixed
opponents. Deadline-relative service attributes every timeout to the deviator;
the graph/native coupling supplies the comparison law. No native incentive
inequality is a premise.

Equal bounds yield exact Nash preservation. A nonnegative uniform bound `delta`
on their difference yields epsilon-to-`epsilon + delta` preservation. Reflection
at compiled profiles needs only honest utility agreement. The expectation
calculation is sharp as a finite-law inequality, but no claim says the chosen
source bounds or the resulting runtime loss estimate are optimal for a program.

When a legal source deviation can choose the designated quit, its supported
outcome satisfies both bounds; hence `f_i <= c_i`. These unconditional bounds
must not be presented as a strictly positive continuation margin. A finer
comparison needs to preserve enough of the actual source continuation context.

## Proposed source-only condition

This section specifies an unproved strengthening, not an additional checked
compiler theorem.

Fix a source profile `sigma` and a syntactic commitment decision site `s` owned
by player `i`. A terminal source environment determines the environment at `s`:
`SourceDecisionSite.recorded` projects the terminal bindings to the site's
post-commit context. Dropping its new commitment and retaining public bindings
gives the **public source environment strictly before s**, denoted `before_s`.

Require the following for each site and every unilateral source alternative:

1. `q` is a legal terminal source execution, with `s` recording the designated
   quitting value at the site's type.
2. `a` belongs to the support of that alternative against `sigma`'s unchanged
   opponents.
3. `before_s(q) = before_s(a)`.

Then require `U_i(q) <= U_i(a)`. Both outcomes and the equality are defined in
written-source semantics. There are no runtime histories, conditional native
laws, or hypothesized backtranslations in this condition. Across differently
typed sites, quitting is a typed-value equality, not an unchecked cast.

The current equal cap/floor condition implies this comparison by ignoring its
prefix equality. The equality can permit comparisons that no global cap/floor
separates: for example, an earlier opponent disclosure determines a baseline
payout, while the player's own participation adds a bonus and quitting subtracts
a penalty. Matching the baseline permits a local comparison even when the
baselines span more than the penalty. This is a motivating mathematical example,
not a mechanized source-to-runtime instance of the proposed condition.

## Required compiler argument

Keep the existing independently proved source/graph and graph/native edges.
The backend should establish a graph-level pair relation, with the compiler
transporting it to `before_s` equality. On normally completed coupling pairs,
public utility already agrees exactly. On timeout pairs:

1. Recover the first-timeout snapshot from the underlying full native trace,
   and select a timeout introduced by that clock transition. For a timed-out reveal, use
   its producer commitment as the decision boundary `s`.
2. Obtain a settlement graph realizing the native public payout, with the
   default recorded at this exact producer. Preserve its identity through
   source decoding; the existing existential `Chooses` result alone loses it.
3. Prove that the public prerequisites of this producer completed normally
   before the first timeout. The proof must account for one clock transition
   scanning several nodes and installing several defaults.
4. Relate those public values to the retained graph realization through
   opening provenance, `candidateGraphRun_accepted`, and append-only event
   persistence. The settlement and deviation graphs then agree on earlier
   public source bindings, although their later continuations may differ.
5. Use `decisionSite_recorded_agrees` and compiler public-prefix readability
   to obtain `before_s` equality. Apply the source comparison pointwise, then
   reuse the existing expectation and finite-mixture selection argument.

The first-timeout prerequisite theorem is checked in
`Interaction/SealedResolutionFirstTimeout.lean`. A positive window ensures that
every node expiring in that transition was ready before the transition: a node
first made ready during the scan cannot already have exhausted its window.
`Interaction/SealedCandidatePrerequisites.lean` separately proves that an
accepted commitment's prerequisites remain completed. This is needed for a
reveal timeout: the reveal depends on the producer, but prerequisite lists
are not assumed transitively closed.

The graph settlement lemma retains a specified defaulted producer, and
`candidateGraphCoupling_opened_before_timeout` proves agreement with the retained
graph realization for disclosures included before the first timeout. The
compiler also has a decoder lemma transporting equality of the relevant public
graph fields to `before_s` equality. These are components, not the completed
comparison: the remaining argument must select and align the producer, preserve
its earlier public values through the native continuation, and assemble the
source-only incentive theorem. The marginal probability laws alone do not imply
this pair relation.

## Boundaries that must be respected

An accepted-event set is not a sequential source prefix. Independent sites may
complete out of order, and accepted commitments are still sealed values.
Pending openings are observations but are not included source disclosures.

On reveal timeout, the settlement graph may replace the producer's value by
quit while the coupled source alternative retains its committed non-quit
value. Therefore the comparison boundary is before the producer commitment,
not after it or at the later reveal. Likewise, an arbitrary timeout in the final
list is unsuitable: defaults preceding it may already have caused the two
continuations to diverge. The proof must identify the first/root timeout.

Ordinary ex-ante dominance of the quit action remains insufficient: a player can
commit to a risky action, then disclose only on favorable observations. The
source-only condition must compare the continuation actually retained by the
coupling, rather than substituting a different safe action after it was locked.
