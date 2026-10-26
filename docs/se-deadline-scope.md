# Deadline scope of sequential-equilibrium preservation

**Priority: high. Status: open artifact generalization and manuscript scope
correction.** The two paper-facing turn-based recovery SE theorems fix the
deadline duration to source rank plus one. They do not quantify over the
configurable deadlines of the general ledger model. Their proofs remain valid
at that specialization; the manuscript omits this restriction.

This is a theorem-scope and applicability issue, rather than evidence of an
invalid Lean proof or a counterexample to configurable-deadline preservation.
It should be resolved before treating the turn-based result as a preservation
theorem for arbitrary positive-latency deadline configurations.

## Evidence and exact scope

| Surface | Checked definition or theorem signature | Deadline scope |
| --- | --- | --- |
| General runtime | `Vegas.EventGraphRuntime`, `Vegas.serviceRuntime` | A supplied duration for each event |
| Default sequential runtime | `Vegas.runtime`, `Vegas.rankDeadline` | `event.val + 1` |
| Forced-exit SE | `Vegas.Paper.recovery_intended_raw_sequential_equilibrium` | Default sequential runtime |
| Sequential singleton-phase SE | `Vegas.Paper.sequential_phase_intended_raw_sequential_equilibrium` | Same default sequential runtime |
| Asynchronous Nash | `Vegas.AsyncServiceSpec.deadline` | Supplied durations |

The specialization is defined in
[RevealService](../Vegas/Game/RevealService.lean). Both exact guarded paper pins
in [Paper.lean](../Paper.lean) take `AsyncTimely (runtime setup) delay bound`;
their schedulers, service contracts and resulting games use that same runtime.
An arbitrary scheduler does not imply an arbitrary deadline configuration.

The runtime's [WithinDeadline](../Vegas/Pending/EventApplication.lean) condition
is `clock - entered < runtime.deadline event`, where `entered` is the clock
when the event became ready. These are **relative durations**, not absolute
deadlines measured from game initialization. The
[AsyncTimely](../Vegas/Pending/ReactiveAsyncContract.lean) condition is

```text
for every player-owned event e:
  delay e + bound e < runtime.deadline e
```

Consequently the pinned turn-based theorems require
`delay e + bound e ≤ e.val`. If an event at rank zero is player-owned, both
natural-number bounds must be zero. If rank zero is a Nature event, that
particular consequence does not apply; later owned events still have the
rank-dependent budget. Rank counts all source events, including samples.

The model permits activations, submissions and inclusions without advancing
the logical clock. The checked
[singleton phase service](../Vegas/Examples/SequentialPhaseService.lean)
deliberately activates, receives and includes the first binding at clock zero,
then ticks and expires; it proves the full raw-history contract with both
bounds zero. Thus zero bounds do not make the theorem inherently vacuous.
However, acceptance of an owned rank-zero event must happen at its
readiness clock: after one tick its deadline test fails. It cannot accommodate
positive clock-tick reaction or inclusion latency at that event. Mapping this
logical clock to an externally advancing block number needs a separate
implementation argument; a builder's ability to issue several model commands
before advancing the clock does not supply that argument.

## Manuscript correction

The maintained manuscript describes a parameter `dl(e)` in Section 5, Appendix
A's ledger model and the ledger figure. Those generic model definitions are
appropriate for the configurable runtime and Nash theorem. They should not be
globally replaced by rank deadlines.

The missing specialization must instead be stated in `thm:recovery`, its
sequential phase-contract corollary, and Appendix A.4's hypothesis mapping:

> The turn-based SE result uses relative deadline durations
> `dl(e) = rank(e) + 1` logical clock ticks.

Until a generalized theorem is checked, prose describing the result as applying
to any timely builder must retain that deadline specialization. The ledger
figure can remain generic, with its theorem-specific instantiation identified.
This correction does not weaken a proved theorem: it aligns the paper with
the actual theorem's existing parameters.

## Preferred artifact repair

Generalize the asynchronous sequential comparison and preservation chain to a
supplied `EventGraphRuntime (graph setup)`, or equivalently a supplied deadline
function. The runtime structure contains only that function. Retain the
existing opportunity, protected-inclusion, completion and strict timeliness
hypotheses against the supplied runtime. The source equilibrium, consistency,
off-path comparisons, whole-policy deviations and exact joint readout/payoff
conclusion must keep their present scopes.

The lower pending-message and phase layers already accept a runtime parameter.
The difficult engineering boundary is the sequential game layer's repeated use
of the default `runtime`, `application`, model and utility abbreviations, and
the shared native/recovery/phase information dictionaries. A source search
alone does not establish that the entire proof will generalize. In particular,
any proof unfolding the default aliases or relying on their definitional
equality needs examination and checked rebuilding. The focused review found
rank-deadline arithmetic in the fixed-calendar roster proofs, and no such
arithmetic in the asynchronous recovery and singleton-phase comparison chain.
That supports the engineering assessment without establishing that the port
is automatic.

Do not change the default runtime's deadlines globally as a substitute for
quantification. The fixed calendar has its own rank-dependent scheduling
proofs. Its concrete callers can instantiate a generalized asynchronous result
at rank deadlines; the general proof should not acquire calendar premises.
Padding the source with dummy samples is also not a generalization of the
same source game.

Acceptance requires:

- Both existing turn-based paper-facing SE results quantify over the supplied
  deadlines, with every existing substantive hypothesis and conclusion kept.
- Any rank arithmetic is confined to actual fixed-calendar consumers.
- A checked nontrivial instance has a player-owned first event, positive
  reaction and inclusion budgets, a sufficiently long deadline, finite nature,
  and the full all-raw-history physical service contract. A timing inequality
  alone is insufficient evidence of applicability.
- Exact paper axiom pins, affected proof checks and a full build pass, and the
  manuscript and documentation agree with the resulting theorem scope.
- The separate GameTheory repository and the approved exit/retry, payoff,
  service and SE target semantics remain unchanged.

No new game-theoretic argument has been identified as necessary for this
repair. That is a working assessment of the existing parameterized layers,
not a checked configurable-deadline SE theorem. Prioritize this repair before
extending the default-runtime SE chain further; the new source/phase Nash
correspondence remains a separate unfinished task.
