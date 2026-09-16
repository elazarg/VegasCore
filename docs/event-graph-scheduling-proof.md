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
Induction by adjacent swaps gives the honest store law. Chance nodes need no
swap argument: they are public barriers and execute their retained kernel once.

## Predrawing and deviation extraction

The arbitrary focal policy can use actual completion order, and `E` can adapt
to public completion identities and public fields. Predraw their responses
jointly over the complete finite execution tree generated from `rho`. A pure
draw consists of one deterministic focal response at every reached focal
observation and one deterministic scheduler response at every reached public
observation. The law of this draw precedes `rho`; opponents' kernels and node
chance remain live.

For each supported pure response pair, construct one canonical focal policy.
At a canonical focal decision, replay the deterministic scheduler within the
current public-barrier interval, using:

- the canonical public prefix;
- public completion identities and the enabled set;
- the focal player's original earlier actions; and
- the deterministic response pair.

Foreign binding meanings are not replay inputs. `publicStore` hides every
binding, while a focal `playerStore` hides foreign bindings. Completing an
opaque foreign binding reveals its event identity but not its action or stored
meaning. Hence the replay determines the asynchronous completion metadata
available to `tau` without clairvoyance. The extracted canonical policy applies
the predrawn focal response to that reconstructed observation.

Opponent binding values are still sampled from their unchanged kernels when
their events execute. Reordering those independent finite draws is justified
by bind commutation, not by predrawing or inspecting them. Averaging the exact
store law for every pure response pair yields `mu` and the deviation equation.

The setup-wide placement of the draw is essential. Predrawing separately after
each concrete input would produce an input-dependent policy and would not be a
legal witness for `gameForm g rho`.

## Hard locality and coupling lemma

The proof should isolate one graph-specific lemma rather than hide it inside a
whole-run induction. For a supported pure focal/scheduler response pair, relate
an asynchronous reachable configuration to a canonical residual execution by:

1. the same completed public prefix and the same values for those public
   fields;
2. the same binding values and original action histories for every owner on
   that owner's completed source prefix;
3. possibly different completion order among current-interval foreign-owner
   bindings;
4. the asynchronous scheduler observation obtained by replaying the pure
   scheduler from the related canonical information; and
5. equal residual store laws after canonical completion.

The step lemma must cover the scheduler's actual selected event, not every
enabled event simultaneously:

- for a nonfocal bind, the compiled kernel is equal on the two normalized
  observations, and its draw can be commuted to the canonical position;
- for a focal bind, replay reconstructs exactly the observation passed to the
  predrawn focal response;
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
finite-horizon theorem: jointly predraw two behavioral kernels over a finite
initial law, retain all other kernels live, and return a finite mixture chosen
before setup. No new probability model is required. After the graph-specific
locality/coupling lemma, ordinary `FinDist.bind`/`map` laws and
`MixtureSimulationOn` package the result.
