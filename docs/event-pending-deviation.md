# Asynchronous pending-message deviation proof

## Statement and boundary

`Vegas.Paper.source_event_pending_deviation_law` proves that, for the actual
event-addressed service, every unilateral native policy has the terminal
source-state law of a finite mixture of source policies, against unchanged
opponents. The mixture is outside the private setup distribution. The theorem
is proved, together with the honest outcome law, arbitrary-player completion,
and same-error Nash preservation and reflection at compiled profiles.

The backend statement belongs at `EventGraphRuntime`: a `BarrierOrdered` graph,
an input distribution, a graph profile, one replaced native policy, and the
concrete wire/order service. Its conclusion compares terminal stores with
canonical graph executions. Source syntax enters only in the final composition.
`ServiceFeasible` protects prescribed opponents, not the deviator. No finite
payload domain or failure-dominance assumption is required by this compiler.

The richer service must not be identified with a graph `PublicScheduler`.
The deviator can encode its own information in public packets, and the wire or
order policy can react to it. Such signaling is legal. The proof compares the
native run directly with canonical graph play.

## 1. Preserve prescribed opponents through partial stages

Between arbitrary native service blocks, a prescribed action can be partly
staged. For example, an honest event can initially be unavailable when its
three reserved calls occur. A reaction slot can then include a deviator's
preceding disclosure, enabling that event. Subsequent honest reaction calls
can remember and prepare its action without yet submitting it. The next
reserved visit must finish that same action, not redraw it.

The invariant therefore tracks each prescribed event's actual history stage,
remembered action, canonical candidate meaning, and submission provenance.
The three relevant stages are unsampled, remembered, and prepared. Submission
follows preparation. A prepared successful candidate has exactly the remembered
typed meaning; failure remains an explicit failure value.

Authentication and canonical packet provenance protect those resources.
Replaying an observed envelope retains its original sender and contents, so
replay must be covered by provenance rather than excluded by a sender test on
the replaying player. Inclusion of a duplicate completed event has no semantic
effect. The reserved selector cannot be displaced by another sender's traffic.

For a ready prescribed event, three reserved owner calls suffice from any of
its coherent partial stages. Combined with reserved inclusion and deadlines
of at least two ticks, this protects it from expiry. An event enabled after
its visit remains timely through the next sweep. The age argument concerns
prescribed events only: focal withholding may legitimately expire.

Checked local results establish cache/history coherence, canonical binding
resources, and resolution-packet provenance at every supported service prefix.
Three owner calls finish sampling and submission from any unsubmitted coherent
stage. An acceptable pending packet survives arbitrary clock-free reactions
or completes its event, and reserved inclusion completes an available prescribed
packet. `runServicePlan_submission_tail_complete` handles the first
submission anywhere in a visit: if it has not already completed, its packet
survives to the reserved inclusion. Thus unfinished prescribed events are
unsubmitted at visit boundaries; a persistent global pending-packet assumption
is unnecessary.

`ServiceReachable.ownerActivationAgeOne` proves the deadline bound at every
actual control prefix. The induction restores the prescribed-owner boundary
after each visit and epoch, then decomposes arbitrary prefixes around the one
clock tick. It does not require the owner to occur in the reaction roster.

## 2. Predraw only the additional strategic responses

Predraw the deviator's native policy, the wire policy, and the epoch-order
policy jointly before setup. Keep other players' policy kernels and application
chance stochastic. The service horizon is bounded and every kernel and setup
law has finite support. Hence only finitely many decision sites are reachable;
the input and payload types themselves need not be finite.

`ServiceControl` exposes the actual service as a current plan and remaining
epochs. Its small-step evaluator is proved equal to `runService`. A probability
protocol presents the three response interfaces without changing them.
Response sites use their existing authenticated histories and observations,
not an added omniscient state or serial number. Repeated calls grow those
histories; epoch boundaries are separated by mandatory environment steps.
This is the acts-once argument needed to reinstall predrawn response functions
through the original policy types.

`exists_pureServiceResponses_mixture` proves this predrawing equation for the
actual serviced game, including setup. It leaves the prescribed players and
application chance stochastic.

## 3. Extract effective focal actions by two-run locality

Fix one pure response triple. Read a focal action from the transition that
actually completes its event, not from arbitrary private preparation. The
graph's appended completion records the dependent action. In particular, a
guard-rejected `true` disclosure must not be reconstructed as `false` merely
because both publish failure.

The key locality statement compares two supported prefixes, possibly from
different supported initial states, that complete the same focal event with
the same normalized focal graph observation. Their effective actions must
agree. Totalizing this reached-action relation gives a graph policy; values
at unreachable observations can be arbitrary legal actions.

The two-run argument replays the native service, not the graph scheduler.
The comparison retains equal focal histories, focal candidate catalogues and
caches, public pools and receipts, environment histories, service cursors,
clocks, and activation metadata. Opponents' hidden choices and private
histories may differ; their staging counters and public effects agree.

The endpoint observation provides equality of the public prefix and the focal
player's own earlier information. This is a retrospective proof premise, not
information supplied to the runtime policy. Immutable fields let it be used
when pairing earlier transitions:

- A prescribed binding emits a value-independent opaque packet, including for
  failure. Private remembering and preparation expose no message contents.
- A prescribed resolution packet depends on its effective publication result
  and public accepted handle. Equal successful results give equal openings;
  withholding and guard-rejected disclosure give the same withholding packet.
- A ready public event is uniquely ready. Before its inclusion, no different
  event can complete; later focal decisions may use the value after inclusion.
- Focal responses, wire responses, and order responses agree when their actual
  sites agree. Focal self-signaling is retained in this replay.
- Chance outcomes before the focal event are public prefix fields. Equal
  endpoint observations identify those earlier draws; chance is not made a
  strategic response.

Every public completion before the focal event belongs to its allowed public
prefix by the barrier discipline. Every earlier focal completion belongs to
its own recall. Consequently the replay may use those endpoint equalities
without assuming access to a later public result. If one prefix completed the
focal event earlier, synchronized replay would complete it in the other prefix
then as well, contradicting its later unfinished occurrence.

The local opacity and authentication facts include prescribed opening
acceptance across differing foreign hidden states and initialization across
private setup draws. The full two-run action-locality theorem is
`reachedFocalAction_eq`. Its paired step retains the endpoint suffixes: independently
sampled chance outcomes need not agree merely because the preceding native
observations agree.

The actual control-step comparison now covers pure focal, wire, and order
responses, opaque prescribed submissions, authenticated packet inclusion,
delivery, grants, clocks, and expiry. Expiry's observation congruence has no
private-value premise. `ServiceControlPath.prescribed_resolutionPayload_eq_of_endpoint`
and `ServiceReplay.sampleStep_of_endpoint` obtain prescribed-resolution packet
equality and chance observation equality from the actual endpoint paths. They
are not runtime restrictions. `ServiceReplay.completionPaired` handles the
final focal completion without any future endpoint premise: a player invocation
cannot complete an event, and a sample instruction cannot complete a player-owned
event. The other instruction cases follow from actual native replay.

## 4. Conserve a graph continuation law

The continuation memoizes only unchanged opponents' samples. Focal native
memory is arbitrary implementation state and is erased from this memo table;
the extracted graph policy governs that coordinate instead.

For a native state `s`, write `C(s)` for the canonical graph outcome law with
that filtered table. The local equations are:

- Arbitrary focal preparation, remembering, submission, and replay preserve
  `C` before inclusion. Their public effects remain in native execution.
- Drawing a prescribed opponent action preserves `C` in expectation and saves
  its sample once, including across partially completed service blocks.
- An accepted prescribed action performs its saved graph step. An accepted
  focal action performs the graph step identified by locality and extraction.
- Application chance performs the original graph kernel. Grants, delivery,
  rejected inclusion, and clock advancement stutter semantically. Protected
  opponent events do not expire; focal expiry contributes its effective failure
  action.

`EventDeviationPotential` checks the focal command, prescribed sample, cached
step, chance, grant, and clock equations. `EventDeviationInvocation` checks
actual player invocations, including partial staging. `EventDeviationEnvironment`
checks actual inclusion, delivery, sampling, clock, and expiry instructions
under local action matching and protected-opponent age. `EventDeviationLaw`
checks the whole-service induction and finite-mixture averaging using
focal-action functionality and the unchanged-owner activation-age bound.
`EventGraphRuntime.exists_deviation_mixture_store_law` discharges both with the
locality and service-protection theorems. At the proved terminal horizon, `C`
is the point mass at the terminal semantic state, yielding the terminal store law.

## 5. Compose with the source edge

Map each graph-policy witness through `backtranslateEventPolicy` and apply
`canonical_deviation_terminalState_law` for each initial source state.
`eventPendingGame_map_outcome` supplies the total terminal readout on every
supported service execution. Distributing finite bind/map operations keeps
one source-policy mixture outside the setup distribution.

This composition requires no source-relative backend invariant or new
whole-program induction. `Setup.eventPendingGame_deviation_law` implements it,
and `Setup.eventPendingSimulation` packages the honest and deviation laws as a
generic mixture-simulation certificate. The generic equilibrium transfer gives
`Setup.eventPendingGame_approximate_nash_iff`. `Paper.lean` delegates directly
to these two theorems and pins their proof dependencies to the standard Lean axioms.
