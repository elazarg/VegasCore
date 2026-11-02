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
| `Vegas.intended_raw_sequentialEquilibrium_preserved` | Intended-game SE extends to the bounded raw-menu game of the forced-exit contract on the sequential graph with finite catalogues covering every binding, publication and initial-input value, under a finitely branching asynchronous builder, arbitrary finitely branching pending observation, conditional independence of initial private data given a public signal, and funded count-audit coverage. The realized joint outcome/payoff law is preserved and no player is excluded or charged on the implementing path. |
| `Vegas.intended_raw_programPayments_preserved` | Every supplied compilation and its exact physical clients retain executable receipts jointly with initial inputs, typed terminal state and public results. |
| `Vegas.EventGraphRuntime.MessageBounds.onePacket_raw_sequentialEquilibrium` | Extension from the one-permitted-packet game to the bounded raw response menu of the same native application and scheduler, for normalization-invariant utilities, authentic count-evidence coverage and deposits covering the legal-history payoff spread. |

These theorems need neither complete pending visibility nor independent
inclusion jobs for different messages. Their substantive hypotheses include
timely opportunities, protected inclusion and completion on every legal raw
history; finite source and physical branching; bounded utility and the stated
failure payoff; and conditional audit observation/delivery coverage. They are
theorems for ideal authenticated commitment interfaces and specified services.
They do not themselves implement signatures, cryptography or an EVM backend.

The [open-problems guide](docs/sequential-se-open-problems.md) states the exact
boundaries and the next questions. The [two-player service](Vegas/Examples/OddsEvensService.lean) and its
clock, opportunity, receipt and completion proofs exercise actual runtime
service premises.

The [two-player Odds–Evens instance](docs/sequential-se-instances.md) combines
positive latency with imperfect evidence capture and delivery on the same
forced-exit runtime. Its fair source equilibrium, exact joint law, expected
payoff of 100 per player, and funding scope are checked.

## Language and compiler

Programs are finite, straight-line typed descriptions of public samples,
owner-private commitments, guarded reveals and terminal payments. The intended
game is the analysis view in which commitments and reveals succeed. Public defaults are absorbing: a defaulted player stays inactive at later
instructions. The graph and ledger preserve the same source configuration.
See [source semantics](docs/source-semantics.md).

The compiler lowers source instructions to a typed event graph. Its checked
source law, scheduler correspondence and Nash results remain in the core,
including approximate Nash correspondence. The compiled graph is a total source
order: every permitted public graph scheduler produces the same event plan
(`Vegas.toEventGraph_policyPlan_eq`). Scheduler quantification adds no choice of
execution order for this compiler. Source execution and the native runtime
share absorbing public defaults; the runtime mechanically
completes instructions of owners who have defaulted.
There is no API compatibility requirement.

The [direct physical compiler laws](Vegas/Game/SourceServiceFirstTurnCompletion.lean)
preserve every total observation of the joint typed terminal state and public
default history under actual sequential clients, for every source profile.
They compare those clients with canonical execution of the compiled graph,
under the asynchronous service and timing premises. No finite wire catalogue,
equilibrium or audit premise is required. The
[bounded-menu compiler laws](Vegas/Game/CompilerCorrectness.lean) realize this
observation on the sequential compiled graph. A dependency mode satisfying the
public-barrier certificate yields that identical graph; the certificate does
not supply another compiler mode. Generic nonordered graph results and their
regressions remain separate library interfaces.
[Operational refinement](Vegas/Pending/GraphRefinement.lean) separately covers
arbitrary raw responses. The [completion guide](docs/compiler-correctness-plan.md)
records their hypotheses and the optional stronger graph-policy interface.

The [uniform semantic client compiler](docs/semantic-client-compiler.md) takes
an intended equilibrium and a certified specification, and returns an SE
assessment of the finite bounded raw-menu game plus physical clients realizing
it. Deviations outside that menu are not covered. Catalogue coverage requires
finite binding/publication value types, including initial binding inputs;
finite strategy support over an unbounded bid type is insufficient. Ordinary
clients support arbitrary specified finitely branching pending observations; ledger clients have
the same run when no pending data is delivered. The completion backend is
nonconstructive; numerical synthesis and client code generation are separate work.

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
toolchain and manifest determine dependencies. The pinned foundation revision
is anchored by the annotated tag
[`v4.35.0`](https://github.com/elazarg/GameTheory/tree/v4.35.0).
Run:

```powershell
lake build
python scripts/check-paper-audit.py
python scripts/check-module-boundaries.py
python scripts/check-lean-options.py
python scripts/check-doc-references.py
python -m unittest discover -s scripts -p 'test_*.py'
python -m unittest scripts.paper_audit_tests
```

Required Lean options are centralized in `lakefile.toml`; warnings fail the
build. Source policy rejects admissions, axiom declarations and trust escapes.
The [script guide](scripts/README.md) explains the structural checks and inventories.

Released under the [MIT license](LICENSE).
