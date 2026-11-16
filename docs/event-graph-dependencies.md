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
Setup exposes these stages as `Vegas.SourceProgram.Setup.dataflowGraph` and
`Vegas.SourceProgram.Setup.informationGraph`.

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
actual observations. The checked graph Nash result covers both independent
bindings and independent reveals, uniformly over dependency choices satisfying
`RevealRelaxedOrdered`. Source-prefix clients always submit bindings and open
active reveals; the same Nash error, full source-configuration/payoff law and
absence of defaults and failed reveals are preserved. The
[native honest-execution law](../Vegas/Game/PrefixClientOutcomeLaw.lean) covers
both relaxations for every intended extension, without a source disclosure or
equilibrium premise. The [native Nash theorem](../Vegas/Game/PrefixClientNash.lean)
preserves the same ε against arbitrary raw native policies for every dependency
choice satisfying `RevealRelaxedOrdered`, including the combined binding/reveal
relaxation. Its first-turn clients use effective openings of prescribed
source-prefix policies, with no caller disclosure premise. The conclusion
retains the actual full runtime readout jointly with the true forfeited payoff
vector, and supported native runs terminate without defaults or failed reveals.
It uses the same service and timeliness contracts on the existing native
application and `Vegas.serviceGame`.

## Runtime and proof interfaces

Complete event orders are characterized independently of node code and player
behavior. A topological order lists each event once and places every direct
predecessor before its event. The pure order API in
[TopologicalOrder](../Vegas/EventGraph/TopologicalOrder.lean) characterizes these
lists as the orders obtainable from source rank by adjacent swaps of distinct
events with no direct dependency in either direction.
[ExecutionOrder](../Vegas/EventGraph/ExecutionOrder.lean) identifies them with
the supported complete run orders, even for a fixed behavioral profile and
initial input. Its deterministic public scheduler forces any given topological
order for every profile and input; it uses only the public completion count.
These are event-identity statements. The terminal-law results above retain
their own dependency and client hypotheses, and do not assert equality of laws
conditional on an adaptive scheduler's realized order.

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

Fixed-code replay has a weaker requirement. Under `ActorSerial`, every
reachable terminal configuration has a source-ranked replay with the same full
configuration in source rank; see [RecordedReplay](../Vegas/EventGraph/RecordedReplay.lean).
The replay profile may depend on the terminal record table. This is a pointwise
reachability statement, so it supplies no observation-local strategy map.

Some failure properties need only valid dependencies. A compiled binding that
stores failure forces an owned failed publication and public default on every
reachable terminal path; see [BindingFailure](../Vegas/Compile/BindingFailure.lean).
This uses its actual subject reveal, rather than merely an event that reads
the binding as a guard input.

Public-barrier ordering and reveal-relaxed ordering remain separate, stronger
certificates for information and scheduling proofs. They imply actor service
conditions where needed. Pure initialization, typing and traffic lemmas need
no information-order premise. Full-source compiler artifacts directly use the
information graph.

Dataflow construction, information-preserving compilation, dependency
relaxation and actor service are separate operations and properties. There is
no execution-mode enumeration.
