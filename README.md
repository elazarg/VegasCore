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
| `Vegas.intended_raw_sequentialEquilibrium_preserved` | Intended-game SE extends to the bounded raw-menu game of the forced-exit contract on the sequential graph with finite catalogues covering every binding, publication and initial-input value, under a finitely branching asynchronous builder, arbitrary finitely branching pending observation, funded count-audit coverage, and either conditional independence of private initial data given a public signal or at most two players with one submission opportunity per event. The realized joint outcome/payoff law is preserved and no player is excluded or charged on the implementing path. |
| [Observed common signal](Vegas/Game/ObservedComponentEquilibrium.lean) | Every player can recover the same signal from its own initial observation. When each supported component satisfies the compiler hypotheses under a shared service, audit and deposits, one global raw sequential equilibrium realizes the supplied intended equilibrium's joint configuration and settled-payoff law with no supported defaults or charges. |
| `Vegas.SourceProgram.Setup.compileIntendedExtension_forfeit` | Source-prefix graph clients preserve intended ε-Nash equilibrium with independent bindings and reveals concurrent, for every disclosing intended extension and every public scheduler of any dependency choice retaining the required barriers. The complete source-configuration/payoff law is preserved, with no defaults or failed reveals; private inputs may be correlated. |
| `Vegas.native_compileIntendedExtension_law` | Under timely asynchronous service, effective-opening source-prefix clients preserve the full source-configuration/payoff law of every intended extension with independent bindings and reveals concurrent. Supported runs terminate without defaults or failed reveals. No equilibrium, finite binding catalogue, finite initial support, disclosure or utility-bound premise is required. |
| `Vegas.native_compileIntendedExtension_preserved` | For every `RevealRelaxedOrdered` dependency choice, including concurrent independent bindings and reveals, first-turn effective-opening source-prefix clients of every supplied intended extension preserve the same ε-Nash error against arbitrary raw native policies. The actual full runtime readout and forfeited payoff vector have the intended joint law; supported runs terminate without defaults or failed reveals. The theorem assumes well formedness, finite players, finite binding types and initial support, the utility-spread forfeit bound, and timely asynchronous service. It needs no source disclosure, independent-prior, audit or deposit premise. |
| `Vegas.intended_raw_programPayments_preserved` | Every supplied compilation and its exact physical clients retain executable receipts jointly with initial inputs, typed terminal state and public results. |
| `Vegas.EventGraphRuntime.MessageBounds.onePacket_raw_sequentialEquilibrium` | Extension from the one-permitted-packet game to the bounded raw response menu of the same native application and scheduler, for normalization-invariant utilities, authentic count-evidence coverage and deposits covering the legal-history payoff spread. |

The sequential-equilibrium theorems need neither complete pending visibility nor independent
inclusion jobs for different messages. Their substantive hypotheses include
timely opportunities, protected inclusion and completion on every legal raw
history; finite source and physical branching; bounded utility and the stated
failure payoff; and conditional audit observation/delivery coverage. They are
theorems for ideal authenticated commitment interfaces and specified services.
They do not themselves implement signatures, cryptography or an EVM backend.

The [open-problems guide](docs/sequential-se-open-problems.md) states the exact
boundaries and the next questions. The [two-player instance](Vegas/Examples/OddsEvensService.lean)
uses the [shared periodic service](Vegas/Pending/PeriodicServiceCompletion.lean), whose
clock, opportunity, receipt and completion proofs exercise actual runtime
service premises.

The [two-player Odds–Evens instance](docs/sequential-se-instances.md) combines
positive latency with imperfect evidence capture and delivery on the same
forced-exit runtime. Its fair source equilibrium, exact joint law, expected
payoff of 100 per player, and funding scope are checked.

The [concurrent Odds–Evens application](Vegas/Examples/OddsEvensConcurrentNative.lean)
uses the combined binding/reveal relaxation, full pending observation and the
same periodic builder. Its compiled clients preserve fair Nash play and the
complete configuration/payoff law against arbitrary native policies.
The [bounded private-values auction](Vegas/Examples/BoundedPrivateValueAuctionSequential.lean)
has a truthful intended sequential equilibrium for every prior. Its
[concrete ledger compilation](Vegas/Examples/BoundedAuctionService.lean) uses
independent uniform values, full pending observation and a funded finite raw
interface, preserving the full law and expected utility 8/7 per bidder. A
[fixed public builder](Vegas/Examples/BoundedAuctionRoster.lean) gives each ready
event a single submission opportunity and realizes truthful play for every joint
valuation prior.

## Language and compiler

Programs are finite, straight-line typed descriptions of public samples,
owner-private commitments, guarded reveals and terminal payments. The intended
game is the analysis view in which commitments and reveals succeed. Public defaults are absorbing: a defaulted player stays inactive at later
instructions. The graph and ledger retain this absorbing rule.
See [source semantics](docs/source-semantics.md).

The compiler lowers source instructions to a typed dataflow graph. Its
information-preserving compilation adds total source order: every public graph
scheduler then produces the same event plan
(`Vegas.toInformationGraph_policyPlan_eq`). The full-source law and Nash
correspondence results use that information graph. Composable binding and reveal
relaxations permit real scheduling choices. Prescribed source-prefix clients
preserve intended Nash equilibrium under both relaxations on the graph and native
ledger. The [native capstone](Vegas/Game/PrefixClientNash.lean) retains the same
Nash error, the joint law of the actual full runtime readout and forfeited payoff,
and clean terminal play for every intended extension.
See the [dependency design](docs/event-graph-dependencies.md).
Source execution and the native runtime
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
observation on the source information graph. Dependency choices and actor-service
conditions have separate APIs; the full-source physical compiler uses the
information graph directly. Generic graph results and their regressions also
cover less restrictive dependencies.
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
restart guide. Concurrent sequential-equilibrium preservation remains open.
The [concurrent-commitment guide](docs/concurrent-commitment-preservation.md)
describes the checked graph and native Nash results and their observation scope.

## Build and validate

The GameTheory foundation is a separately managed Lake package. The pinned
toolchain and manifest determine dependencies, and Lake fetches them into
`.lake/packages`. The pinned foundation revision is anchored by the annotated tag
[`v4.36.0`](https://github.com/elazarg/GameTheory/tree/v4.36.0).
Run:

```powershell
lake --wfail build
python scripts/check-paper-audit.py
python scripts/check-module-boundaries.py
python scripts/check-lean-options.py
python scripts/check-doc-references.py
python -m unittest discover -s scripts -p 'test_*.py'
python -m unittest scripts.paper_audit_tests
```

Required Lean options are centralized in `lakefile.toml`. The strict build rejects
compiler and Lake warnings, including cached diagnostics. Source policy rejects
admissions, axiom declarations and trust escapes.
The [script guide](scripts/README.md) explains the structural checks and inventories.

Released under the [MIT license](LICENSE).
