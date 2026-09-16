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

`BarrierOrdered.exists_deviation_mixture` proves the setup-wide graph law
against normalized opponents. Its right-hand side uses the original opponents
under the canonical scheduler, where normalization is proved to leave the
complete execution law unchanged. The theorem concerns the actual
`runPolicies` executor and the complete typed terminal store.

`eventSchedulingSimulation` packages this law and the honest law as
`MixtureSimulationOn` between the actual canonical and scheduled games.
Same-error Nash preservation and reflection follow for every terminal-store
utility by the shared game-theory theorem.

The proof has three independent components:

1. `exists_scheduler_mixture` preserves the full configuration law while
   replacing the public scheduler by a finite mixture of deterministic public
   schedulers. The mixture is chosen before private setup.
2. `SchedulerReachable.replayPrefix_eq_history` reconstructs the actual
   selected-event prefix from a deterministic scheduler and the player's
   visible store. `runPolicies_update_replay_eq` consequently replaces the
   arbitrary focal policy by its replay wrapper without changing the full
   execution law under that scheduler.
3. `BarrierOrdered.runPolicies_update_store_eq_canonical` applies scheduler
   erasure to the resulting normalized profile. Averaging gives the mixture
   of canonical deviations.

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
No fallback observation is needed. The actual-run proof uses write-once store
preservation to show that masking the later store recovers each earlier
scheduler observation. Induction over supported scheduler-selected steps
then identifies the replayed prefix with the real prefix.

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
randomize, exactly as `tau` does. At every reachable focal decision under `s`,
the reconstructed observation equals the actual observation passed to `tau`.
This gives the whole-run replacement law under the same scheduler.

All policies in that replaced profile are normalized: unchanged opponents
already use `normalizeProfile`, and `replayPolicy` is a fixed point of
normalization. The honest scheduler-erasure theorem therefore applies to the
entire replaced profile. It produces the canonical deviation law for this
pure scheduler without commuting an order-sensitive focal kernel. Averaging
over scheduler seeds gives `mu` and the exact mixture law. Source-facing
composition uses canonical graph-to-source policy backtranslation.

`Vegas.Compile.EventGraphBacktranslation` proves two-sided reconstruction of
strategic actions and their dependent completion histories.
`EventGraphObservationEncoding` constructs the complete player-visible store
from a source observation and proves its inverse at represented canonical
prefixes. `EventGraphPolicyBacktranslation` combines this with original-action
recall to construct a setup-uniform source policy and prove its local decision
kernels. Successful decoding at a canonical prefix is proved from available
fields; decoding and re-encoding the actual observation preserves the entire
visible store and own-action history, without assuming a source-state
simulation invariant.

`compileEventPolicy_backtranslate_at_prefix`, in namespace
`SourceProgram.EventLowering` and module `Vegas.Compile.EventGraphPolicyAlignment`,
proves constructor-recursive
kernel alignment: recompiling the backtranslated focal policy agrees with the
normalized arbitrary graph policy at every reachable selected source rank.
The other players remain unchanged. `runPolicies_canonical_eq_of_reachable`
lifts that equality to a full execution law, which composes with
`canonical_terminalState_law` and the scheduler mixture in
`EventLowering.scheduled_setup_deviation_law`.
`Paper.source_event_graph_deviation_law` delegates to this result.
`Setup.eventSimulation` exposes the composed certificate and yields same-error
Nash correspondence and source-state deviation guarantees through the generic
finite-mixture transport theorems.

The setup-wide placement of the draw is essential. Predrawing separately after
each concrete input would produce an input-dependent policy and would not be a
legal witness for `gameForm g rho`.

## Reusing finite predrawing

`SchedulerProtocol` presents event selection as one decision maker in
GameTheory's execution protocol, solely to apply its finite behavioral-to-mixed
theorem. This decision maker is not an additional player in the game. Its first
transition samples the input law; subsequent transitions use the actual player
policies and node chance kernels. Its information is precisely the public
graph observation and enabled event set.

`scheduler_runBehavioralFrom` proves this adapter has the state law of
`runPlan`. A scheduler information state cannot recur: it contains the
completion-order length, which increases at every graph step. The existing
finite predrawing theorem therefore yields the required pure scheduler
mixture. No finite payload or information-state type is assumed. The mixture
may depend on the fixed profile and input distribution, as a unilateral
deviation witness may; it does not depend on the realized private input.

## Information and outcome boundaries

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

Predrawing itself preserves the full configuration law, including trace
observables. Only the later scheduler-erasure step projects to terminal stores.
The ideal graph theorem does not imply a corresponding pending-message law:
packet observations, retries, and deadline service belong to the separate
event-addressed runtime edge.
