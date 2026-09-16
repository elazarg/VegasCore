# Event-graph failure comparison

## Scope

This note specifies the utility premise needed when an implementation adds a
new opportunity to stop an otherwise feasible graph continuation. It is not a
simulation certificate and does not assume the desired unilateral-deviation
bound.

For a public-barrier compiler output, the ideal `EventGraph` game is designed
to admit an exact comparison. Bind failure and the disclosure Boolean are
already graph actions in both canonical and asynchronous schedules. The
information certificate guarantees the same declared public fields and own
history at a ready strategic event, while different ready orders add completion
metadata. The scheduling argument must show that this metadata creates no
additional outcome laws against unchanged compiled opponents.

The same conclusion applies to the **initial pending-message implementation**
described by the barrier design, provided its stated policy and service
contracts are actually proved:

- an honest bind or publication is prepared and submitted only when its event
  is ready;
- every public event waits for all source-earlier events, and the following
  private interval waits for that public event;
- prescribed traffic is value-oblivious until the corresponding publication;
- arbitrary early focal packets remain observable but unchanged compiled
  policies ignore them outside their logical source observations; and
- deadline-relative service completes every compliant enabled event before
  expiry, despite arbitrary focal traffic.

At an enabled public event there is therefore no unresolved earlier semantic
event and no later honest public value can appear while the focal player waits.
At an enabled private bind, concurrently completing foreign binds reveal only
value-independent completion metadata and opaque canonical handles. Adaptive
environment reactions to the focal player's raw packets may supply additional
public scheduling signals, but not information correlated with an opponent's
hidden meaning under these contracts. A behavioral graph policy can absorb
such random signals in the exact replay/backtranslation; they do not justify a
new clairvoyant stopping choice.

Expiry then realizes an action already present in the graph: failure at a bind,
or `false` at a resolution. Repeated expiry choices occur at their corresponding
barrier-separated graph decisions. No counterexample to exact pending-to-
canonical deviation simulation follows merely from delaying those choices.
Consequently the initial pending compiler should target the exact finite-mixture
deviation law, retaining arbitrary focal packets and adaptive public scheduling.
Failure comparison is not a blocking M1/M3 interface for that target.

A utility weakening becomes relevant only for a broader runtime that lets a
player exercise failure after learning information unavailable at the matching
graph decision—for example, early honest delivery across a public barrier,
value-dependent prescribed traffic, a scheduler signal correlated with hidden
candidate meaning, or another operation that exposes a genuinely new semantic
choice before expiry. The remainder of this note specifies the contract for
such an extension.

## One failure opportunity

Fix the deviating player, unchanged opponent policies, the admitted adaptive
public environment policy, and a reachable runtime history `h` at which a new
failure operation is available. Let `I(h)` be everything the deviator may
actually observe then: public application state, included and pending traffic,
receipts and clocks, its private cache and earlier actions, and any public
scheduler metadata.

A feasible repair consists of one continuation policy `repair_I` for each
supported information value `I`. It must:

1. be chosen from `I`, not separately for hidden semantic states compatible
   with `I`;
2. retain all commitments, registrations, messages, and public effects already
   fixed at `h`;
3. use only commands still available from `h` and obey the same service and
   environment policy as the failure branch; and
4. continue as a legal graph action/continuation against the unchanged
   opponents.

Write `Fail(h)` for the complete outcome law after exercising the additional
failure and `Repair(h, repair_I)` for the complete outcome law after the repair.
For the deviator's terminal-outcome utility `u`, the local weak condition is

```text
E[u | Fail(h)] <= E[u | Repair(h, repair_I)].
```

The expectation includes all later player, chance, scheduling, delivery, and
deadline behavior. It is not an immediate-transfer comparison. A margin
version adds a fixed nonnegative `delta` to the left side.

The quantifier order is essential:

```text
for every supported information value I,
  there exists one feasible repair policy repair_I such that
    for every hidden state compatible with I, the required comparison holds,
```

or, with a proved conditional-law correspondence, the analogous comparison of
conditional expectations on the whole `I`-fiber. Choosing a different repair
after inspecting each hidden state is clairvoyant and is not sufficient.

A simple, stronger source-facing premise is pointwise continuation dominance:
for each `I`, one repair works for every compatible semantic state. This
survives arbitrary refinement by public messages and adaptive scheduling. An
unconditional ex-ante comparison before the extra information is revealed does
not: a player can retain a risky commitment and stop only in the unfavorable
states.

## Repeated informed failure

There may be several stopping opportunities. Normalize them backward over the
finite remaining event/deadline tree. At the last exercised additional failure,
replace stopping by its feasible repair and apply the local comparison to the
full normalized continuation. Repeat until no additional failure remains.
Earlier repairs may change later public histories, so the premise applies to
every supported information state reached during normalization, not merely the
states reached by the original policy.

This is the compiler-specific use of
`FinDist.selective_stopping_le` (or its margin form). That lemma removes one
informed randomized Boolean stop once branchwise continuation superiority is
provided. It does not construct repairs, prove their measurability, or justify
the backward runtime coupling. After normalization supplies a unilateral
expected-utility bound, `GameForm.UtilitySimulation` packages the all-profile
result; its profile-local Nash theorem is the correct endpoint when the premise
is proved only against one fixed opponent profile.

## Boundaries and examples

- **Empty payload or unsatisfiable guard.** If no successful value exists, a
  timeout cannot be repaired into success. The resulting failure is unavoidable
  or already represented by the graph and is not removed by this condition.
  A feasible repair may itself end in failure; then the comparison is usually
  equality.
- **Withholding after learning more.** If a registered opening remains feasible,
  submitting that same opening is a candidate repair. Dominance must hold after
  the information used to decide withholding, not only when registration was
  chosen.
- **Raw announcements.** Keep already sent packets in both branches. They may
  change the adaptive public scheduler's later behavior. A repair that erases
  an announcement or substitutes a preselected schedule is infeasible.
- **Ordinary new choices.** If the runtime action changes a value, selects a
  candidate, rerolls chance, or otherwise does more than stop a fixed feasible
  continuation, this failure contract does not justify eliminating it. That
  behavior needs an exact correspondence or its own explicit utility bound.
- **Deadlines.** Expiry is an additional stopping option only when compliant
  continuation was still feasible. A missed service obligation is not blamed
  on the player, and an already impossible continuation is not a repair target.

The condition concerns the deviator's utility. It does not imply protection of
another player from a malicious failure. Exact outcome-law simulation is needed
for arbitrary source-observable guarantees.

## Open definitions required by a broader runtime

Before applying this utility comparison, a runtime that goes beyond the initial
barrier protocol must identify:

1. the precise histories at which failure is additional rather than an existing
   graph action or unavoidable result;
2. the actual information projection `I` governing the stopping decision;
3. the same-history feasible-repair relation, including service checkpoints and
   immutable packets/commitments; and
4. the finite well-founded measure used by backward normalization when repairs
   alter later histories.

These are operational definitions, not theorem hypotheses asserting a
simulation. No weaker information-conditional source predicate should be
adopted until the runtime proves that its stopping event and repair policy are
measurable with respect to the same information fibers.

For the initial barrier implementation, the immediate obligations are instead
exact-law obligations: prove value-oblivious prescribed traffic, service
protection under arbitrary focal traffic, causal replay of the adaptive public
environment, and backtranslation of each expiry to the already available graph
failure action. Failure of one of those proofs should produce a concrete
counterexample or identify the precise newly revealed information before this
utility contract is introduced.
