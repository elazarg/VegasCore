# VegasCore

VegasCore is a Lean 4 development of a small language for games with partial
information, a compiler from it to typed event graphs and to contracts on a
pending-message chain model, and theorems on which equilibria of a program
survive compilation. Blockchain ledgers are the motivating target; the chain
model does not depend on one.

## Source language

A [source program](Vegas/Source/Basic.lean) samples public chance, lets an owner
commit to a private typed value under a guard, lets the owner reveal that
commitment, and returns. The initial context holds public data and owner-private
inputs, drawn from a joint initial law. The instruction evaluator represents
failure as a value and continues; that view remains in the retained plain Nash
results ([source semantics](docs/source-semantics.md)). The chosen operational
policy is permanent public exit with observed commitment-phase retries. Its
[source phase game](Vegas/Game/SourcePhaseGame.lean) reuses the existing exit/retry
kernel and requires program-declared integer exit transfers. The full
continuing-source/phase Nash port remains separate; the
[semantic contract](docs/common-semantics-contract.md) states that boundary.

The language is deliberately small:

- programs are straight-line, without branches or loops;
- the owner of every move is fixed by the program text;
- every owned move is a commitment and a later reveal of it;
- a guard reads public data, publications and its author's own commitment, never
  private inputs.

Utilities in the existing equilibrium capstones are parameters, over the public
outcome together with initial-input parameters, or over the terminal state.
[Program payment utility](Vegas/Game/ProgramPayoffs.lean) adds a separate
valuation to the program's evaluated `ret` payments. The
[payment example](Vegas/Examples/ProgramPayments.lean) proves that changing a
program bonus reverses a strict incentive, and that compilation preserves the
payment law. Both phase SE environments have monetary specializations over the
same terminal-observation carrier. The [compiled cash reader](Vegas/Compile/EventGraphCash.lean)
evaluates native payment instructions and applies the declared exit override.
The [compression and migration report](docs/consolidation-compression.md) records
the checked scopes, measured costs and remaining contract ports.

## Compilation

The [compiler](Vegas/Compile/EventGraphCompiler.lean) lowers a program to a typed
event graph of bindings, resolutions and public samples
([design](docs/event-graph-design.md)). In the concurrent mode, commitments of
different owners between two public events are unordered. The sequential mode
orders every event by its source position.

The graph runs on the [`Interaction`](Interaction) chain model. Players send
signed packets to a pending pool. A builder chooses activations, inclusions,
clock advances and expiries, and each player sees the pool through an
observation rule. A compiled contract accepts or rejects packets. An audit
collects evidence of forbidden packets and charges deposits.

There are three compiled contracts:

- **plain:** a failure is recorded and play continues;
- **forced exit:** a failing owner leaves the game with a fixed exit payoff;
- **phase:** forced exit on the concurrent graph, where a binding missed in a
  commitment phase reruns the phase for the remaining owners.

The [design note](docs/semantics-and-enforcement.md) compares them. The
[consolidation ledger](docs/consolidation.md) plans to keep only the phase
contract.

## Checked results

[Paper.lean](Paper.lean) audits every result below. Main preservation statements
are in `Vegas.Paper`; prose invariants and examples are pinned at their owning
declarations. Each pin checks the exact standard axiom dependencies.
Every mathematical result claimed as checked in the maintained manuscript has
a pin, independently of whether another theorem uses it. Technical import
exceptions require an explicit reason and a separately checked audit.

The source invariant `Vegas.SourceProgram.Setup.terminal_guards_hold` covers
every source profile and supported terminal state: a guard's subject or a
required input failed, or its code holds on the published values. Completion
alone is the separate invariant `Vegas.SourceProgram.Setup.revealed`.

For every source profile, the joint typed readout and realized settlement of
its raw clients is within the deferral error `δ` of the source law
(`Vegas.AsyncServiceSpec.clientSettlementLaw_withinTV`). An event probability
lower bound `p` transfers as `p - δ`; a bounded observable expectation lower
bound `b` transfers as `b - δ * R`, where `R` is its range width on both laws'
supports. Both corollaries are pinned, need no equilibrium assumption, and
retain unfinished results and audit settlement in the compared joint law.

The *intended game* of a program is the analysis view in which nothing fails.
The *forfeit utility* charges a fixed amount for each failed reveal, and the
*exclusion utility* gives a player with a failed reveal a fixed payoff.

### Compiler correctness

| Theorem | Statement |
| --- | --- |
| `scheduled_terminal_state_law` | Under every public scheduler of the compiled graph, the compiled profile's decoded terminal states have the source program's execution law. |
| `concurrent_event_nash_iff` | Take finite binding types and a finitely supported initial law. Under any public scheduler of the concurrent graph, a compiled profile is an ε-Nash equilibrium iff the source profile is one of the source game. This holds for every utility of the public outcome. |
| `source_protocol_horizon` | Every source execution ends within one step more than the program has instructions. |

### From the intended game to the source game

| Theorem | Statement |
| --- | --- |
| `intended_sequential_equilibrium` | A sequential equilibrium of the intended game extends to one of the source game whose forfeit is at least the utility range. No reveal fails on its path, and the joint law of outcome and payoffs is unchanged. |
| `intended_nash` | Every source profile extending an intended ε-Nash equilibrium is an ε-Nash equilibrium of the source game under the same forfeit, with no failed reveal on its path and the same joint law of outcome and payoffs. |

### Nash preservation on the plain contract

These theorems hold for any builder meeting the asynchronous contract
(`Vegas.AsyncServiceSpec`):

- an owner is activated within a reaction bound once its event is ready;
- its sole packet for the event is included within an inclusion bound;
- both bounds fit before the event's deadline;
- every run completes the graph.

The audit is any authentic sampler, and deposits are nonnegative. Binding values
have finite message forms, and the initial law has finite support.

| Theorem | Statement |
| --- | --- |
| `async_first_turn_nash_iff` | A source profile is an ε-Nash equilibrium iff its first-turn clients are one on the bounded raw ledger. |
| `async_client_nash_correspondence` | For clients that may defer, both directions hold with extra slack: twice the total deferral weight times the payoff range. |
| `async_client_nash_reflection` | The source direction, on every response menu that admits the clients. |
| `intended_async_first_turn_nash` | Take a source profile extending an intended ε-Nash equilibrium. Its first-turn clients are an ε-Nash equilibrium under the forfeit utility, with the intended joint law of outcome and payoffs. |
| `intended_async_client_nash` | The same for deferring clients, with the slack above. The joint law is within the total deferral weight in total variation. |

### Sequential-equilibrium preservation

| Theorem | Contract and environment | Statement |
| --- | --- | --- |
| `concurrent_source_raw_sequential_equilibrium` | Phase contract on the concurrent graph with a count audit. A reserved-epoch service runs it, processing every pending packet each cycle on one tape drawn from a fixed prior, independent of the inputs. Activation and processing gaps are bounded, and every player sees every pending packet. | Every sequential equilibrium of the intended game is matched by one of the raw contract. The two have the same joint law of initial inputs, terminal state, public result and realized payoff vector, and nobody is excluded or charged on its path. |
| `recovery_intended_raw_sequential_equilibrium` | Forced-exit contract on the sequential graph with a count audit and supplied per-event relative deadline durations, under any finitely branching builder meeting the asynchronous contract for that runtime. Private inputs are independent conditional on an observable public initial signal. | Every sequential equilibrium of the intended game is matched by one of the raw contract. The joint law of outcome and payoffs is the same, and nobody is charged on its path. |
| `one_packet_raw_sequential_equilibrium` | Plain contract with a count audit, under any finitely branching builder. | In a sequential equilibrium of the game where each player sends at most one permitted packet per event, the extension to all raw responses is one too. The law is the same and nobody is charged. |

Both raw contracts charge deposits through the count audit. Each deposit,
multiplied by the rates at which evidence against its owner is observed and
delivered, must cover that owner's payoff spread.

The sequential singleton-phase SE pin also takes supplied deadline durations.
Both retain the full service contract and require reaction and inclusion bounds
to fit strictly within each owned event's duration. A
[positive-latency equilibrium](Vegas/Examples/SequentialPhaseDelayedEquilibrium.lean)
instantiates this contract; the [deadline scope](docs/se-deadline-scope.md)
describes its timing and clock assumptions.

### Limits of preservation

These results concern an abstract late-turn game, not the ledger
([`Vegas.Examples.LateLeak`](Vegas/Examples/LateLeak.lean)). A sender may open at a
protected turn or later, and a listener sees pending openings before they
resolve.

| Theorem | Statement |
| --- | --- |
| `late_leak_intended_outcome_not_preserved`, `late_leak_not_preserved_when_deferral_pays`, `late_leak_not_preserved_for_every_margin`, `settle_late_not_preserved_for_every_margin` | The intended game has a sequential equilibrium, and every one realizes the intended outcome law. The late game has sequential equilibria, but none realizes it. The four theorems cover the sample parameters, any parameters where deferring pays, and every inclusion probability above an explicit threshold below one. |
| `late_leak_equilibrium_total_variation_gap`, `late_leak_equilibrium_result_total_variation_gap` | For the sample parameters, every equilibrium outcome law of the late game is at least 267/2000 from the intended one in total variation, and every result law at least 3/2000. |
| `late_leak_outcome_preserved_by_failure_costs` | Suppose the forfeit exceeds half the reward, and so does the expected loss of a late opening, counting the forfeit and the drop charge. Then the late game has a sequential equilibrium, and every one realizes the intended outcome law. |

## Scope of the claims

- The preservation theorems start from an equilibrium of the intended game, in
  which nothing fails, not of the source game. The concurrent theorem is named
  `source` but assumes `ConcurrentPayoffs.SourceEquilibrium`, an equilibrium of
  the intended game.
- In the concurrent theorem, the excluded payoff is constant per player. It is
  at most zero and at most every terminal utility. A run unfinished at the
  horizon pays zero. Binding types are finite, and the initial law may correlate
  players but has finite support.
- The assumptions of the concurrent theorem are sufficient, not minimal.
  [These counterexamples](docs/consolidation.md#why-the-concurrent-theorem-assumes-what-it-does)
  show why several of them are needed.
- Five theorems have no concrete program as an instance: `intended_nash`, the
  two intended asynchronous Nash forms, and the one-packet and turn-based SE
  theorems. The concurrent theorem's hypotheses are discharged only for a
  program without strategic content
  ([test](VegasTests/ConcurrentRawHypotheses.lean)). A two-player
  late-opening program instantiates the intended-to-source extension and its
  exclusion variant `Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_extends_to_exclusion`
  ([source](Vegas/Examples/LateOpeningRuntimeSourcePreservation.lean))
  and three Nash forms on a concrete builder
  ([runtime](Vegas/Examples/LateOpeningRuntimeNash.lean)).
- Cryptographic commitments, signatures and the EVM are ideal interfaces here;
  realizing them needs separate refinement proofs.

Retired models, routes and examples remain at the `research-tree` tag. The
[consolidation ledger](docs/consolidation.md#retired-results) indexes them.

## Build and validate

`lakefile.toml` makes Lean warnings errors, so a `sorry` fails the build. The
source policy rejects axiom declarations and trust escape hatches. Run the
checks after the build and before committing:

```powershell
lake build
python scripts/check-module-boundaries.py
python scripts/check-lean-options.py
python scripts/check-doc-references.py
python -m unittest discover -s scripts -p 'test_*.py'
```

The GameTheory dependency is a Git submodule. The [script notes](scripts/README.md)
describe the checks. The [documentation index](docs/README.md) lists the design
and research notes, and the [module map](docs/module-architecture.md) locates
the code.

The code is released under the [MIT license](LICENSE).
