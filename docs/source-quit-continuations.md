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

## Checked prefix-relative condition

`VegasCore.QuitPayoutPrefixDominanceAgainst` in
`Vegas/Core/SourceQuitPrefix.lean` states the condition below.
`SealedCompilation.candidate_deviation_bound_of_source_quit_prefix` composes
its source/graph transport with an independent graph/native bound. The resulting
same-error Nash and epsilon-Nash equivalences at compiled profiles are checked
in `Vegas/Game/SourceCandidate.lean` and directly audited in `Paper.lean`.

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

The equal cap/floor condition implies this comparison by ignoring its prefix
equality; `QuitPayoutBoundAgainst.quitPayoutPrefixDominance` proves the implication.
`VegasTests/SourceQuitPrefix.lean` proves a strict separation: a public sampled
bit determines a baseline paid after either decision value. Prefix dominance
holds, although no global bound can cap the high-baseline quit and floor the
low-baseline continuation. This is a source-level example; its sample is outside
the candidate backend's admitted fragment, so it is not an end-to-end instance.

`VegasTests/SealedCandidatePrefix.lean` separately instantiates the new theorem
inside the admitted fragment: a first player commits and reveals a randomized
baseline, followed by the second player's commitment and reveal. The second
payout depends only on that baseline; the first payout is constant. The test
proves the source prefix condition and the native expected-utility bound for
arbitrary unilateral replacements and arbitrary unreserved wire behavior under
certified periodic inclusion service.

## Compiler argument

The proof keeps the independently proved source/graph and graph/native edges.
The backend establishes a graph-level pair relation, and the compiler transports
it to `before_s` equality. Normally completed coupling pairs have identical
public utilities. On timeout pairs:

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

`candidateGraphCoupling_timeout_public_prefix` identifies the producer and
preserves its public reads through the actual native continuation.
`candidateGraphRoundCoupling_timeout_settlement` constructs a terminal quitting
graph with the actual native public store and the same producer reads as the
retained graph realization. These are joint statements about supported coupling
pairs, not conclusions inferred from separate marginal laws.

`WFProgram.graphPayout_le_of_source_quitPrefix` transports the source condition
to those graph pairs. Its decoder uses
`SourceDecisionSite.recorded_tail_erasePubEnv_eq_of_choiceReads_eq` to prove
`before_s` equality. The graph-only theorem
`CandidateRoundModel.deviation_bound_of_quit_prefix` supplies the arbitrary
native deviation bound; the source theorem composes that inequality with the
source/graph strategic certificate. Opponents retain their original policies.

## Boundaries that must be respected

The end-to-end result covers the homogeneous, sample-free sealed fragment with
universally accepting guards, finite players, and the existing
deadline-relative service contract. The pointwise prefix condition is sufficient,
not a characterization of all utilities for which Nash is preserved. It compares
all legal quitting settlements to all supported unilateral continuations with
the same earlier public environment, including continuations that themselves
quit. It supplies no positive strict margin on those self-comparisons.

The candidate theorem does not yet transport general conditional-expectation or
commitment-dependent continuation conditions. Those require their own joint
correspondence and cannot be inferred from prefix equality alone.

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
