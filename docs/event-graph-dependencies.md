# Event-graph dependencies

The design separates event code, execution dependencies, observations and
scheduling. A dependency choice changes which events are ready. It leaves
node code and the observation and scheduling interfaces fixed; reachable
observations and the choices offered to the scheduler can change.

## Fixed event code and valid dependencies

An event graph fixes input and output types, node code, declared reads and
payoffs. Its source rank witnesses acyclicity; rank alone does not select the
next event.

`EventGraph.Dependencies` packages a predecessor relation with two structural
facts: predecessors have lower rank, and every declared output read has its
producer as a predecessor. `withDependencies` changes this relation while
retaining the same typed event code. The certificate is indexed by event count
and declared producer reads, so repeated changes do not require transports
between different copies of the code.

The dataflow choice contains exactly the declared producer reads. It is the
least relation satisfying this structural contract. This does not assert that
an expression's declared read footprint is semantically minimal.

## Source information

`toEventGraph` constructs the dataflow graph. `toInformationGraph` adds the
ordering used to preserve the source language's full decision interface.
Setup exposes these stages as `dataflowGraph` and `informationGraph`.

The current source interface retains chronological completion metadata and a
default-log slot for every preceding instruction. Public omissions can affect
later decisions even when their binding values are hidden. The information
compiler therefore uses the complete source rank. Existing source-law and
sequential-equilibrium results belong to this information graph.

This is an explicit, conservative compilation policy. It is not a claim that
every direct edge is necessary in every program: a chain can enforce total
precedence, and particular programs or restricted profiles can require less
information. A prefix-shaped completed set alone also does not fix the
chronological order in which that set was completed.

## Property-specific relaxation

Reveal relaxation removes edges between independent publications. Binding
relaxation removes edges between private bindings of different owners. Each
operation filters the dependencies it is given and retains declared reads.
Neither operation silently rebuilds a stronger order.

The source constructions consequently read as a pipeline:

```text
dataflow graph
  → add source-information ordering
  → relax independent reveals
  → relax independent bindings
```

The two relaxations commute. Their orders form a diamond: the combined
relaxation is contained in either individual relaxation. There is no general
inclusion between binding-only and reveal-only relaxation, although they can
coincide for particular programs. Declared dataflow dependencies are contained
in all these choices, and all are contained in source rank.

Relaxing dependencies does not itself prove preservation. A result states the
property it preserves and the prescribed policies, observation projection and
payoff discipline under which it does so. Arbitrary deviations retain their
actual observations. The existing reveal-preservation result and the ongoing
commitment-preservation proof use this distinction.

## Runtime and proof interfaces

The native runtime continues to execute any event graph with its per-event
timeout durations. It does not select a source compilation mode.

Source-specific runtime adapters take valid dependencies for the fixed source
code. Actor-based service has its own condition:
[OwnerSolitary](../Vegas/EventGraph/ActorTurns.lean) says that a particular ready
event has no other ready event with the same owner; `ActorSerial` requires this
at every event. Other owners may still act concurrently. These conditions say
nothing about which public results a decision must wait for. Local acceptance
and deadline proofs take the local condition; proofs about a whole traffic
history take `ActorSerial`. Proofs that already know the selected turn can use
that witness directly.

Public-barrier ordering and reveal-relaxed ordering remain separate, stronger
certificates for information and scheduling proofs. They imply actor service
conditions where needed. Pure initialization, typing and traffic lemmas need
no information-order premise. Full-source compiler artifacts directly use the
information graph.

Dataflow construction, information-preserving compilation, dependency
relaxation and actor service are separate operations and properties. There is
no execution-mode enumeration.
