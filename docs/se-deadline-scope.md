# Deadline scope of sequential-equilibrium preservation

The turn-based recovery and singleton-phase SE theorems take a supplied
`EventGraphRuntime (graph setup)`. Its `deadline` field assigns a relative
duration to each event. The source-rank schedule is a concrete calendar
instance, not a restriction of these preservation theorems.

## Checked theorem boundary

| Surface | Deadline scope |
| --- | --- |
| `Vegas.Paper.recovery_intended_raw_sequential_equilibrium` | Supplied runtime |
| `Vegas.Paper.sequential_phase_intended_raw_sequential_equilibrium` | Supplied runtime |
| `Vegas.SequentialPhase.intended_raw_programPayments_preserved` | Supplied runtime |
| `Vegas.AsyncServiceSpec.deadline` | Supplied durations |
| `Vegas.runtime`, `Vegas.rankDeadline` | Concrete source-rank-plus-one calendar |

The exact guarded pins in [Paper.lean](../Paper.lean) quantify over the runtime
used by the application, scheduler, legal histories, service contract, target
assessment and realized-payoff law. The monetary theorem in
[SequentialPhasePaymentPreservation](../Vegas/Game/SequentialPhasePaymentPreservation.lean)
uses the same parameter.

The substantive SE assumptions remain necessary: well-formedness; finite
intended histories and finite physical nature; private-input independence
conditional on an observable public initial signal; value coverage and candidate
capacity; bounded utilities and an exit payoff below intended terminal utility;
and audit coverage with multiplicative funding. Opportunity, protected inclusion
and completion hold over **every legal raw history**, including horizon-terminal
histories. The conclusions retain whole-policy sequential rationality, no exits
or audit charges on the preserved paths, and the exact joint typed readout and
realized settled-payoff law. Configurable timing does not discharge any of these
guards.

## Relative durations and strict margins

The runtime's [WithinDeadline](../Vegas/Pending/EventApplication.lean) condition
is `clock - entered < runtime.deadline event`, where `entered` is the clock
when the event became ready. These are relative durations, not absolute
deadlines measured from game initialization. The
[AsyncTimely](../Vegas/Pending/ReactiveAsyncContract.lean) condition requires

```text
for every player-owned event e:
  delay e + bound e < runtime.deadline e
```

No monotonicity of deadlines, rank-based formula or additional positivity
hypothesis is imposed. The strict inequality supplies the required positive
duration for each owned event. Nature events are outside this timing condition.

Choosing `Vegas.runtime setup` specializes the result to `event.val + 1`.
In that instance, an owned rank-zero event requires both natural-number service
bounds to be zero. The abstract clock permits multiple activations, submissions
and inclusions between ticks; the
[unit-deadline service](../Vegas/Examples/SequentialPhaseService.lean) supplies
such an all-history instance. The general theorem does not require that choice.

## Positive-latency instance

[SequentialPhaseDelayedService](../Vegas/Examples/SequentialPhaseDelayedService.lean)
uses a genuine player-owned rank-zero event: publication of an initially private
Boolean, with executable payments of two or zero. Every event has duration six.
A periodic reserved service has reaction bound three and inclusion bound two,
so `3 + 2 < 6`. Its concrete execution activates the first owner at clock one
and receives the packet at clock two.

The instance proves finite nature and the full opportunity, protected-inclusion
and completion contract on all raw histories, including silence, malformed
responses and horizon-terminal histories. The
[equilibrium application](../Vegas/Examples/SequentialPhaseDelayedEquilibrium.lean)
constructs an intended SE and a funded raw phase SE with no exits or audit
charges and the exact joint readout and realized settled-payoff law. Its deposit
is three and its evidence service has observation and delivery rates one.
These are proofs of applicability, rather than only a numerical timing margin.

The clock remains an abstract logical clock. An implementation using an
externally advancing block clock must establish the same service and timing
bounds for that interpretation; the ability to issue several model commands
between ticks does not itself prove such a refinement.

## Module boundary

The native, recovery, singleton-phase and stopped-comparison chains carry the
supplied runtime through their existing models. The concrete fixed-calendar
roster retains its rank arithmetic and explicitly instantiates its own runtime.
The separate GameTheory repository, the source and runtime transition rules,
exit/retry policy and payoff semantics are unchanged by deadline selection.

The source/phase operational-information and native Nash correspondence remains
a separate unfinished task; see
[source-phase correspondence](source-phase-correspondence.md).
