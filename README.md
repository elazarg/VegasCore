# VegasCore

VegasCore is a Lean development of a small commit–reveal language, its compiler
to typed event graphs and message-ledger contracts, and preservation of strategic
behavior. The maintained core focuses on checked non-concurrent sequential
equilibrium (SE) preservation and the source, runtime and mathematical results
that support it.

## Checked preservation results

Every paper-stated mathematical result has an exact guarded standard-axiom pin
in [Paper.lean](Paper.lean). Library and example results build with the same strict
source policy. The manuscript is maintained separately in `overleaf/`.

| Result | Checked scope |
| --- | --- |
| `Vegas.Paper.recovery_intended_raw_sequential_equilibrium` | Intended-game SE extends to the forced-exit contract on the sequential graph under a finitely branching asynchronous builder, arbitrary pending observation, conditional independence of initial private data given a public signal, and funded count-audit coverage. The realized joint outcome/payoff law is preserved and no player is excluded or charged on the implementing path. |
| `Vegas.Recovery.intended_raw_programPayments_preserved` | Monetary specialization with executable program transfers and valuation, retaining the initialized typed/public/net-payoff joint law. |
| `Vegas.Paper.one_packet_raw_sequential_equilibrium` | Extension from the one-permitted-packet game to all raw responses on the plain contract, under conditional audit coverage and adequate deposits. |

These theorems need neither complete pending visibility nor independent
inclusion jobs for different messages. Their substantive hypotheses include
timely opportunities, protected inclusion and completion on every legal raw
history; finite source and physical branching; bounded utility and the stated
failure payoff; and conditional audit observation/delivery coverage. They are
theorems for ideal authenticated commitment interfaces and specified services.
They do not themselves implement signatures, cryptography or an EVM backend.

The [open-problems guide](docs/sequential-se-open-problems.md) states the exact
boundaries and the next questions. The [two-player service](Vegas/Examples/OddsEvensRecoveryService.lean) and its
clock, opportunity, receipt and completion proofs exercise actual runtime
service premises.

The [two-player Odds–Evens instance](docs/sequential-se-instances.md) combines
positive latency with imperfect evidence capture and delivery on the same
forced-exit runtime. Its fair source equilibrium, exact joint law, expected
payoff of 100 per player, and funding scope are checked.

## Language and compiler

Programs are finite, straight-line typed descriptions of public samples,
owner-private commitments, guarded reveals and terminal payments. The intended
game is the analysis view in which commitments and reveals succeed. Failure is
accounted for by the source failure view and the runtime's exclusion rules.
See [source semantics](docs/source-semantics.md).

The compiler lowers source instructions to a typed event graph. Its checked
source law, scheduler correspondence and Nash results remain in the core,
including the concurrent event-graph Nash theorem: that result is about public
graph scheduling, not concurrent raw-ledger SE preservation. The plain and
forced-exit implementations remain where the retained theorems use them.
There is no API compatibility requirement.

The [ordinary compiler capstones](Vegas/Game/CompilerCorrectness.lean) preserve
the exact law of every total typed-terminal-store reader on the actual bounded
ledger clients, including failures, without an equilibrium or audit premise.
They compare those same clients with canonical execution of the compiled graph.
[Operational refinement](Vegas/Pending/GraphRefinement.lean) separately covers
arbitrary raw responses. The [completion guide](docs/compiler-correctness-plan.md)
records their hypotheses and the optional stronger graph-policy interface.

The [uniform semantic client compiler](docs/semantic-client-compiler.md) takes
any supplied intended equilibrium and returns a certified runtime assessment
and physical player clients. It reuses the preservation completion and policy
decoder. Ledger clients agree at every legal raw history when the interface
delivers no pending data. The completion backend is nonconstructive;
executable numerical synthesis and client code generation are separate work.

Checked late-leak examples delimit preservation and show sufficient payoff
conditions in their stated finite games. Their impossibility conclusions do
not extend automatically to every runtime or compiler. The small auction and
payment examples distinguish the declared transfer law from truthful incentives.

## Working on the core

Start with the [documentation index](docs/README.md), [module ownership](docs/module-architecture.md)
and [open problems](docs/sequential-se-open-problems.md). Search the owning
modules and inspect signatures with `python lean-defs.py` before adding machinery.

The [research archive](docs/archives.md) preserves the broader concurrent work,
proof experiments and earlier design documents at fixed revisions, with a
restart guide. Those research targets are not current theorem claims.

## Build and validate

The GameTheory foundation is a separately managed Git submodule. The pinned
toolchain and manifest determine dependencies. Run:

```powershell
lake build
python scripts/check-module-boundaries.py
python scripts/check-lean-options.py
python scripts/check-doc-references.py
python -m unittest discover -s scripts -p 'test_*.py'
```

Required Lean options are centralized in `lakefile.toml`; warnings fail the
build. Source policy rejects admissions, axiom declarations and trust escapes.
The [script guide](scripts/README.md) explains the structural checks and inventories.

Released under the [MIT license](LICENSE).
