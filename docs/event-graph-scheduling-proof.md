# Exact scheduling comparison for public-barrier EventGraphs

## Statement and observation boundary

Let `g` be a finite `EventGraph` with `BarrierOrdered g`, and use the resulting
`InformationDiscipline g.prefixSchema`. Let `rho : FinDist g.Inputs` be an
arbitrary finite initial law. A strategy is chosen before the draw from `rho`.
Fix a public scheduler `E`, a canonical profile `sigma`, a focal player `i`,
and an arbitrary asynchronous replacement `tau` for `i`.

The comparison observes the complete typed terminal store, not the terminal
`Config`. An asynchronous run generally has a different completion trace, so
equality of terminal configurations is false and is not needed. Writing
`readout result := result.1.outcome result.2` for the map from
`g.gameSignature.Outcome` to `g.Outcome`, and `C` for the normalized strategy
compiler below, the target is

```text
honest:
  map readout ((g.gameForm rho E).play (C sigma))
    = map readout ((g.canonicalGame rho).play sigma)

deviation:
  exists mu : FinDist (BehavioralPolicy g i),
    map readout ((g.gameForm rho E).play ((C sigma)[i <- tau]))
      = bind mu (fun pi =>
          map readout ((g.canonicalGame rho).play (sigma[i <- pi])))
```

Here `mu` is chosen before the input draw. All nonfocal strategies are exactly
the compiled strategies from `sigma`; neither they nor `rho` are changed. The
scheduler remains the fixed adaptive policy `E`, rather than a fixed event
trace. This is the graph-local `MixtureSimulationOn` statement with
`Observation := g.Outcome` and all target deviations considered.

The theorem is independent of source syntax and of any native-message
scheduler. In particular, it assumes no factorization of a richer wire
environment through `PublicScheduler`.

## Compiled canonical strategies

At a strategic event `e` owned by `p`, replace the actual
`PlayerObservation.completionOrder` by the canonical source-ranked prefix.
Retain the projected visible store and the original dependent `ownActions`.
Then call `sigma p e` on that normalized observation.

Two existing facts justify this normalization at every reachable ready event:

- `InformationDiscipline.logicalObserve_store` says the ready player has
  exactly the declared visible prefix: all initial visible fields, earlier
  public outputs, and its own earlier bindings. A future foreign binding may
  have completed, but its value is absent from the player's store.
- `InformationDiscipline.ready_ownEventIds` says the chronological identities
  of the retained own completions equal the schema's source-ranked own
  history. The completion records themselves retain the original dependent
  actions, including a `resolve true` whose accepted result is failure.

Thus normalization changes only scheduling metadata. It does not reconstruct
an action from an output or reveal a foreign binding. The canonical completion
prefix should be defined from event rank, not copied from the asynchronous
trace.

For honest play, every strategy uses this projection. The only distinct events
that can be ready together under `BarrierOrdered` are hidden binding events of
different owners. Public events wait for every earlier event, and bindings of
one owner retain source order. A binding node has no semantic read and writes
its unique output. Consequently the corresponding steps commute for fixed
actions; the two owners' compiled kernels also agree before and after the swap
because each consumes the same normalized store and own-action history.
The local probabilistic diamond is checked by
`BarrierOrdered.policyStepThen_map_storeRecall_comm`. A tracewise adjacent-swap
argument alone is insufficient for an adaptive scheduler: its probabilities
depend on the preceding observations. The whole-run proof must compare
continuation laws before averaging the scheduler's selected event. Chance
nodes need no swap argument: they are public barriers and execute their
retained kernel once.

## Whole-run honest law

The checked graph-owned theorem
`BarrierOrdered.runPolicies_store_eq_canonical` equates the terminal store laws of
`runPolicies E (normalizeProfile sigma)` and
`runPolicies canonicalScheduler (normalizeProfile sigma)` for each initial
environment. It is proved before lifting through the finite initial law.
For compiled source profiles, normalization is definitionally the identity
(`normalizeProfile_compileEventProfile`), so the checked source-order law
supplies the source-facing conclusion `EventLowering.scheduled_setup_law`.

The proof uses the configuration projection

```text
semanticState c = (c.cut.completed, storeRecall g c)
```

and induction on the number of unfinished events. Canonical
normalized continuation depends only on this projection. The cut determines
readiness, the store determines node evaluation, and the store plus per-player
original actions determine the normalized policy kernels. Actual completion
order is unnecessary.

Choosing any ready event and continuing canonically gives the
same terminal law as choosing the least ready event. If they differ, both are
foreign-owner bindings. Apply the induction hypothesis to take the other
event next on each side, use the two-step diamond, and use continuation
congruence to identify the remaining laws. At a public event there is only one
ready event. Terminal cuts give the base case.

Finally, expand the actual scheduler's first-step bind. Each supported choice
has the same canonical continuation law, so their weighted average has that
law as well. This handles history-adaptive selection without fixing a trace or
assuming its probability is invariant under permutation. It proves only the
honest law; an arbitrary focal policy need not obey normalization.

## Predrawing and deviation extraction

The following is the mathematical plan for the remaining deviation theorem.
`Vegas.EventGraph.SchedulerReplay` implements bounded pure-scheduler replay,
public-store masking, and a total replay policy. Replay termination,
completion-order insensitivity, and the normalization fixed-point law are
checked. Reconstruction
of the observation along an actual scheduler-generated run, setup-wide
scheduler predrawing, and the deviation law remain unproved.

The arbitrary focal policy can use actual completion order, and `E` can adapt
to public completion identities and public fields. Predraw the **scheduler's**
responses over the complete finite execution tree generated from `rho`. A
pure draw supplies one deterministic scheduler response at every relevant
public observation and enabled set. The law of this draw precedes `rho`.
Player kernels, including the focal replacement `tau`, and node chance remain
live. Predrawing the focal policy is unnecessary for this graph edge.

Fix one pure scheduler `s`. At a canonical focal decision `e`, replay `s` from
the empty cut, retaining only event identities and stopping immediately before
it selects `e`. At each replay step, form the scheduler observation from the
replayed completion list and the current decision's public store, restricted
to initial public fields and public events already completed in the replay.
No event value is sampled by replay.

Replay reaches the target for every supplied store: each other selection
completes a fresh event, so the finite graph forces selection of the target.
No fallback observation is needed. The required actual-run lemma must show
that this replayed prefix equals the real prefix, not merely that replay
terminates.

Public barriers ensure that every public output encountered before `e` has
rank less than `e`. Those outputs are all available in its canonical decision
view. The scheduler may place later foreign bindings before `e`, but their
values are hidden from both the scheduler and the focal player. Same-owner
dependencies ensure that the actual focal own-action list and visible private
fields agree with their canonical counterparts.

Define a canonical focal policy by

```text
replayPolicy s tau e observation =
  tau e (observation with completionOrder := replayPrefix s e observation.store).
```

This policy ignores the supplied chronological order. Its kernel can still
randomize, exactly as `tau` does. The graph-specific replay theorem must show
that, at every reachable focal decision under `s`, the reconstructed
observation equals the actual observation passed to `tau`. This yields a
whole-run law replacing `tau` by `replayPolicy s tau` under the same scheduler.

All policies in that replaced profile are normalized: unchanged opponents
already use `normalizeProfile`, and `replayPolicy` is a fixed point of
normalization. The honest scheduler-erasure theorem therefore applies to the
entire replaced profile. It produces the canonical deviation law for this
pure scheduler without commuting an order-sensitive focal kernel. Averaging
over scheduler seeds gives `mu` and the exact mixture law. Source-facing
composition additionally needs canonical graph-to-source policy
backtranslation; the honest source-order law alone does not supply it.

`Vegas.Compile.EventGraphBacktranslation` proves two-sided reconstruction of
strategic actions and their dependent completion histories. The remaining
canonical backtranslation must reconstruct the complete player-visible store
from a source observation and prove the inverse on reachable canonical
decisions. Arbitrary graph policies can inspect every visible slot, so
successful decoding alone is insufficient: alias consistency and field
coverage must establish that re-encoding recovers the actual observation.

The setup-wide placement of the draw is essential. Predrawing separately after
each concrete input would produce an input-dependent policy and would not be a
legal witness for `gameForm g rho`.

## Hard locality and coupling lemma

The proof should isolate the graph-specific replay lemma rather than hide it
inside a whole-run source induction. For a pure scheduler, relate replay to
an asynchronous reachable configuration by:

1. the same completed public prefix and the same values for those public
   fields;
2. the same binding values and original action histories for every owner on
   that owner's completed source prefix;
3. possibly different completion order among current-interval foreign-owner
   bindings;
4. the asynchronous scheduler observation obtained by replaying the pure
   scheduler from the related canonical information.

The step lemma must cover the scheduler's actual selected event, not every
enabled event simultaneously:

- for a nonfocal bind, the compiled kernel is equal on the two normalized
  observations, and its draw can be commuted to the canonical position;
- for a focal bind, replay reconstructs exactly the observation passed to its
  original randomized response;
- at a public barrier, all earlier events are complete, so both sides have the
  same full prior store and execute the same resolve or sample kernel;
- completing any event appends its original action to the proper owner's
  history and preserves the relation.

This lemma is stronger than final-store commutation: it preserves precisely the
information needed by later kernels. It is weaker than transcript equality,
which is generally false.

## Failure modes and required library support

The exact theorem fails if a scheduler or player can observe a foreign binding
meaning. For example, let foreign `B` complete while focal `A` and foreign `C`
remain ready. If the scheduler sees whether `B` bound `0` or `1`, it can next
choose `A` before `C` in one case and `C` before `A` in the other. An arbitrary
focal `A` policy can read whether `C` is already complete and condition its
action on `B`'s hidden value. No canonical policy with the source information
can reproduce this. The current `publicStore`/`playerStore` projections exclude
that counterexample.

The theorem also fails for trace-sensitive observations: canonical and
asynchronous completion orders differ. It applies to typed terminal stores and
therefore to payoff or utility functions factored through those stores.

Existing message-application predrawing proves the analogous setup-wide joint
response result, but is tied to `MessageApplication` invocation sites. The
ideal graph proof needs either a small EventGraph specialization or a reusable
finite-horizon theorem: predraw the scheduler kernel over a finite initial
law, retain every player kernel live, and return a finite mixture chosen before
setup. No new probability model is required. After the graph-specific replay
lemma and honest scheduler erasure, ordinary `FinDist.bind`/`map` laws and
`MixtureSimulationOn` package the result.
