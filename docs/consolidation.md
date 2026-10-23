# Consolidation ledger

This ledger tracks the reduction of VegasCore to one source language, one
compiled contract on one chain model, and the theorems about them. It holds the
target, the codebase review measured at commit `8c67dad2`, the step order, the
owner decisions the steps depend on, and the index of retired results.

Rules:

1. Steps run in order. A step closes when its exit criteria hold on a green
   `lake build` with the repository checks passing.
2. A finding closes with the commit that resolves it; tick its box in that
   commit.
3. Anything removed that carries a checked result worth citing gets an annotated
   tag first and a row in [retired results](#retired-results).
4. Step and finding labels stay in this file. They never appear in Lean names or
   docstrings (see AGENTS.md).

## Target

**Source language.** Straight-line commit–reveal programs: private inputs,
public chance, guarded commitments and reveals, and payoffs computed by the
program. Branches and loops are out of scope; the design should not preclude
them.

**Payoffs and utility.** The program's payoffs are what the compiler sees.
Players' utilities are quasi-linear: a private valuation of the outcome plus the
payoff. Deposits, forfeits and exit payoffs are payoffs; the valuation bounds
they need are declared parameters, not properties the compiler reads from the
program.

**Truthfulness.** The designer can specify truthfulness, for example that
truthful bidding is dominant in a second-price auction. Preserving it through
compilation is desired but not expected to hold in general; where it fails, the
ledger records why rather than claiming it (decision D4).

**Compiled output.** One compiled contract with one verdict and audit model on
the `Interaction` chain model. The environment (builder, observation, audit
coverage) is a parameter, and the strength of the preserved notion depends on
it.

**Theorem ladder.**

| Result | Environment | Graph | Present state |
| --- | --- | --- | --- |
| Compiler correctness: terminal law, unilateral deviation law, Nash equivalence on the ideal graph | none | any mode | checked: `canonical_setup_law`, `canonical_setup_deviation_law`, `Vegas.Paper.concurrent_event_nash_iff` |
| Nash preservation | any timely builder | sequential and concurrent | checked on the plain contract (`Vegas.Paper.async_first_turn_nash_iff` and siblings); to port |
| Non-concurrent sequential-equilibrium preservation | any timely builder, independent private inputs | sequential | checked on the forced-exit contract (`Vegas.Paper.recovery_intended_raw_sequential_equilibrium`); to port |
| Concurrent sequential-equilibrium preservation | reserved-epoch tape, complete pending observation | concurrent | checked on the phase contract (`Vegas.Paper.concurrent_source_raw_sequential_equilibrium`) |
| Intended game to source game | none | none | checked: `Vegas.Paper.intended_sequential_equilibrium`, `Vegas.Paper.intended_nash` |
| Late-leak impossibility | abstract game | none | checked: `Vegas.Paper.late_leak_intended_outcome_not_preserved` and siblings |

**Size.** The owner's estimate is 50–80k lines of Lean outside the GameTheory
submodule. [Measurements](#measurements) give the current floor and explain any
excess.

## Measurements

Measured at `8c67dad2` with a declaration-level dependency walk: from the root
theorems, follow the constants each declaration uses through the project
libraries, then merge the source ranges of the reached declarations per module.
File headers, `variable` lines and notations are not counted, so whole files
run 10–20% larger. `#print axioms` pins do not count as uses.

| Root theorems | Lines in cone | Beyond the concurrent SE cone |
| --- | ---: | ---: |
| Concurrent SE | 210k | |
| Turn-based SE (forced-exit contract) | 109k | 90k |
| Calendar SE | 74k | 60k |
| Calendar Nash | 60k | 47k |
| Asynchronous Nash | 49k | 36k |
| Ideal-graph Nash (compiler correctness) | 9k | 4k |
| One-packet SE | 8k | 3k |
| Late leak | 8k | 8k |
| Intended to source, exclusion | 5k | 1k |
| Public scheduling | 2.5k | 2k |
| All 26 Paper theorems | 317k | |
| Whole tree (files, without GameTheory) | 871k | |
| Whole tree after Step 3 pass one | 597k | |
| In modules no Paper theorem, test or example reaches, after Step 0 (438 modules) | 80k | |
| Whole tree after Step 3 pass two | 494k | |
| Whole tree after unreached declarations | 445k | |
| Whole tree after Step 3 | 442k | |

The concurrent SE cone by layer: Vegas/Game 136k, Vegas/Pending 32k,
Vegas/Source 24k (17k of it the `CommitRecovery*` and `ProposalRecovery*`
carriers), Interaction 7k, GameTheoryExtensions 4k, Vegas/EventGraph 3k,
Vegas/Compile 3k. Within Vegas/Game: `QualifiedBinding` about 53k,
`PhaseProposal*` 42k, `ProposalRecovery*` 13k, `ReservedEpoch*` 11k.

**Why the floor exceeds 50–80k.** The language, compiler, chain model and phase
contract fit in about 55k lines, and the source language with its compiler and
Nash equivalence on the ideal graph in 9k. The excess is the proof of concurrent
SE preservation: about 150k lines (Vegas/Game plus the source-side carriers).
Removing unreached code reaches about 250k for concurrent SE and both Nash
forms, or about 340k with turn-based SE kept on its own contract. Reaching
50–80k would need the concurrent proof to shrink by a factor of four or more,
which nothing measured so far supports. The slack indicators are real (F-S4,
F-S2; 12.5% of six-line windows recur in another file), but their yield is
unmeasured. Step 6 starts by compressing one self-contained module and measuring
the ratio before any size target is fixed. Extrapolating a factor of 1.5–2.5 on
the proof layer gives an end state of roughly 100–170k lines; this is an
estimate, not a measurement.

## Model inventory

Each construction gets one disposition: keep, merge, carrier (a labelled proof
device in the proof layer), tag and remove, or remove.

**Source-level games.**

| Construction | Role | Proposed disposition |
| --- | --- | --- |
| `SourceProgram.gameForm`, `Setup.gameForm` | Source semantics as a game form | keep one; `Vegas.SourceProgram.Setup.protocol_runBehavioral_eq` relates it to the protocol |
| `Setup.executionProtocol`, `Setup.informationModel` | Source semantics as an information model, parameterized by a commitment interface | keep |
| `Setup.intendedModel` | Analysis view: commitments hold predicted values, reveals open; premise of every SE theorem | keep |
| `Setup.exclusionModel`, `Setup.exclusionMoveModel` | Analysis view with a fixed exit payoff | decision D3 |
| `commitRecoveryModel`, `commitRecoveryErasedModel`, `proposalRecoveryModel` | Proof carriers of the concurrent SE theorem (26k of the 47k lines in Vegas/Source) | carrier: move to the proof layer and label |
| `Setup.valueBindingGame` | Pure value-binding game form, used only by the commit–reveal auction example; its behavioral edge ([`Vegas/Game/ValueBindingEdge.lean`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/ValueBindingEdge.lean)) is unused | remove the edge; keep the game form only with the example |
| `SourceProgram.Initial` | Duplicate of `Setup` with a point-mass initial state | removed; tests use a `Setup` with a point-mass law, and `Vegas.SourceProgram.Setup.revealed` states the accounting theorem |
| `Vegas/Language` | Surface-syntax prototype with no semantics or elaboration | tag and remove |

**Compiled contracts.** All three run on the same `Interaction` chain model.

| Contract | Packets and verdict | Results on it | Proposed disposition |
| --- | --- | --- | --- |
| Plain (`serviceApplication`) | `WitnessedPacket`, settled-record verdict | Nash (all forms), calendar SE, one-packet SE | remove after the Nash port |
| Forced exit (`recoveryApplication`) | `WitnessedPacket`, count verdict | turn-based SE | remove after the turn-based SE port |
| Phase (`phaseApplication`) | `CommitAttemptPacket`, phase count verdict | concurrent SE | keep: the contract |

**Audit models.** The settled-record authentic sampler (calendar) and the count
evidence report service (forced exit and phase). Keep the count service.

**Environments.** Calendar rosters, `AsyncContract`, `Recovery.AsyncContract`
and the reserved-epoch tape. Keep one timely-builder contract (for Nash and
turn-based SE) and the reserved-epoch tape (for concurrent SE).

## Steps

Order: work that needs no new mathematics and causes no long breakage comes
first (Steps 0, 1 and 3, and the documentation parts of Steps 2 and 7). Steps 4
and 5 wait until those are done. Removing code is not a risk: the tag
`research-tree` holds the full tree.

### Step 0. Record

- [x] Commit this ledger.
- [x] Annotated tag `research-tree` on `main` holding the full research tree,
      so every later removal is recoverable by tag.
- [x] Pin `recovery_intended_raw_sequentialEquilibrium_preserved` in Paper, as
      `Vegas.Paper.recovery_intended_raw_sequential_equilibrium`; the paper cites
      it as `thm:recovery`.

### Step 1. Guardrails that make removal cheap

- [x] Remove `warn.sorry = false`, the open-obligation registry,
      `scripts/report-open-obligations.py` and its CI step. With
      `warningAsError` a `sorry` then fails the build. A `sorry` is allowed only
      temporarily during a large planned proof effort, and none is planned.
- [x] Remove the hand-written pins in `VegasTests/AxiomAudit`. The axiom audit
      is the pins in Paper.lean; the build rejects `sorry`, and the source
      policy rejects `axiom` declarations.
- [x] Reduce `scripts/check-lean-options.py` to the central options, the ban on
      `sorry` and `axiom`, the Paper pin format with its expected axiom list,
      and a ban on escape hatches: declaration-adding metaprograms, skipped
      kernel checks, native evaluation, and options set per library or through
      command-line definitions.
- [x] Add the dependency walk as a script: list modules with no declaration
      used by Paper, a test or an example, counting names that test and
      example source mentions. Report only until Step 6
      (`scripts/report-unreached.py`).

Exit: green build with sorry warnings as errors; the walk script is committed.
This step comes first because every removal would otherwise edit audit pins.

### Step 2. Fix the contract

- [ ] Owner decisions D1–D8.
- [ ] Paper.lean states exactly the kept theorems, under the naming scheme of
      D8.
- [x] One results table in README keyed to the Paper pins, with scope and
      hypotheses; ARTIFACT.md folded into it.
- [ ] Stale or contradictory status statements fixed or deleted (findings
      F-D1 to F-D4).

Exit: README, Paper and the docs agree; the documentation checks pass.

### Step 3. Prune to the kept cone

Two passes. The first removes every module outside the import closure of the
kept roots: the modules holding declarations used by the kept Paper theorems
and by `recovery_intended_raw_sequentialEquilibrium_preserved`, plus the kept
tests and instance examples. No kept module imports a removed one, so this pass
cannot break the build. At `0a2dbc66` it removes 1,508 modules (295k lines) and
keeps 2,306 (594k). The second pass shrinks the closure: unused imports, then
unreached declarations inside kept modules, rebuilding as it goes.

Removed results are indexed under [retired results](#retired-results).

Pass one, done:

- [x] `archive/`.
- [x] The calendar theorems in Paper and the calendar checklist with its
      evidence script.
- [x] `CommitSeedBroadcast*`, `CommitSeedSignalling*`, `CommittedResolution*`
      and `LateOpeningRuntime*` examples, except the two instance files
      `LateOpeningRuntimeNash` and `LateOpeningRuntimeSourcePreservation` and
      the modules they need.
- [x] `PhaseTiming*` and most of `PhaseRecovery*`.
- [x] `Vegas/Language`, the Communication chain, `CommitmentEvidence`,
      `EventGraphEvidence`, `PayoffTransport`, `ValueBindingEdge`.
- [x] `VegasTests/AxiomAudit`, `VegasTests/Language`, and the
      GameTheoryExtensions modules that only their own tests used.

Pass two:

- [x] The 438 modules (80k lines) none of whose declarations Paper, a test or
      an example reaches, as `scripts/report-unreached.py` lists them, and the
      407 declarations in 143 kept modules (23k lines) that use them. Each import
      of a removed module became the surviving modules it imported, and module
      docstrings that described removed results were rewritten.
- [x] Unreached declarations inside kept modules: 1,812 declarations (48k
      lines) in 572 modules, and the 5 modules that left empty. A declaration
      stays when surviving source outside comments mentions its name (rfl
      lemmas used by `simp`, `show` types, `variable` binders), when it is an
      instance or an rfl `@[simp]` lemma, or when it lies in
      `ExclusionMoveGame` (decision D3) or in the language and compiler layers.
- [x] Unreached declarations in `Vegas/Foundation`, `Vegas/Expr`,
      `Vegas/EventGraph` and `Vegas/Compile`, reviewed by hand. Removed 91
      (1.6k lines): helpers of removed proofs (commit-prefix filling, encoding
      inverses, configuration restriction, output coupling), and the
      nullable-commitment, substitution and default-value helpers of the simple
      expression language with its unused `CommitPayloadTy` and `DefaultVal`
      classes. Kept as specification, though nothing uses them yet: dependency
      soundness of the expression interface (`Vegas.IExpr.expr_deps_sound`),
      the guard characterizations, compiler correctness for expressions, payoffs
      and payouts (`Vegas.canonical_payout_law`) and under public scheduling
      (`Vegas.scheduled_setup_law`), the event graph's information-flow lemmas,
      the guarantees on resolution fields and published guards, and the
      relation between the sequential and concurrent execution modes
      (`Vegas.EventGraph.canonical_fromSequential_store_law`), which a
      derivation of the sequential results from the concurrent ones would start
      from.
- [x] Unused imports: 1,524 project imports removed and 423 added where a
      module had reached a dependency only through a removed one (net 1,101 of
      7,059), and the last unreached module. A library module imports the
      modules owning the constants its declarations use, the rfl `@[simp]`
      lemmas whose left sides they use, and the names its `open`, `variable`
      and notation lines and `simp` lemma lists mention.
- [ ] The calendar's remaining `ServiceRoster` and `SourceService*` modules,
      `MessagePool` and most of `OnePacket*` stay because the turn-based SE and
      asynchronous Nash theorems use them on the plain and forced-exit
      contracts; they wait for Step 4.

Exit: the walk reports only modules on its allowlist; measurements updated.

### Step 4. One contract

Before a theorem moves to the phase contract, a written comparison of the old
and new statements shows that the move does not weaken it: environment,
deviations, payoffs and the preserved law. Paper states one clear Nash
preservation theorem.

- [ ] Nash preservation on the phase contract under timely builders
      (first-turn clients and the deferral bound).
- [ ] Non-concurrent SE on the phase contract over the sequential graph, or the
      concurrent theorem generalized over the graph mode if the environments
      can be reconciled. Start with a short investigation of which properties
      of `.concurrent` the concurrent proof uses.
- [ ] Remove the plain and forced-exit contracts, `WitnessedPacket` and the
      settled-record audit.

Exit: every preservation theorem is stated for `phaseApplication`.

### Step 5. Language: payoffs, exit, truthfulness, instances

- [ ] Program payoffs are load-bearing: utility is valuation plus payoff, and
      the capstones are stated that way.
- [ ] The source failure semantics of D3.
- [ ] A truthfulness specification (D4).
- [ ] Every Paper theorem applied to a concrete program in which some player has
      a strict incentive; impossibility statements include existence of the
      equilibria they quantify over.

Exit: no capstone takes a utility over terminal states except through the
valuation; every Paper theorem has an instance.

### Step 6. Proof compression and naming

- [ ] Recurring hypothesis groups bundled into structures; repeated terms
      named with API lemmas; declarations over 500 lines split.
- [ ] Duplicate private helpers and near-copy files merged.
- [ ] Directories by layer and concept; namespaces only `Vegas` and
      type-attached ones; the naming scheme of D8 applied throughout.
- [ ] Examples in their own library; abstract examples outside `Vegas`.
- [ ] The walk script gates CI.

Exit: size within the target, or the excess explained in
[measurements](#measurements).

### Step 7. Documentation and CI

- [ ] README (purpose, results, build), design notes, research notes behind one
      index; the module map generated or replaced by per-directory headers.
- [ ] CI: separate documentation job on `main` only, concurrency group,
      GameTheory build cache, actions pinned by commit.

## Owner decisions

- **D1. Kept theorem set.** Decided: the ladder in [target](#target), without
  the calendar results. A calendar is a fixed instruction plan
  (`rosterScheduler` reads `rosterPlan` by round), so every player knows the
  schedule in advance; its sequential-equilibrium and Nash theorems are
  retired. Non-concurrent SE stays the turn-based theorem under any timely
  builder. Deriving it from the concurrent theorem waits: the environments
  differ, so the derivation is not expected to be routine.
- **D2. The single contract.** Proposed: the phase contract.
- **D3. Source failure semantics.** Commit–reveal with exit
  (semantics-and-enforcement.md III.1), or the intended game with forfeit and
  exclusion payoff rewrites as analysis views only. This also decides the fate
  of `exclusionModel`.
- **D4. Truthfulness.** Decided meaning: truthfulness preservation, for example
  that truthful bidding stays dominant when a second-price auction is compiled.
  Not expected to hold in general; the language must be able to state it, and
  the conditions under which it holds or fails are open.
- **D5. Impossibility results kept on `main`.** Proposed: the late-leak family
  (abstract, about 8k lines, motivates the exit payoff), moved out of the
  `Vegas` namespace. The runtime obstructions (`LateOpeningRuntime*`,
  `CommitSeedSignalling*`) at tags.
- **D6. Tags or branches.** Proposed: annotated tags for retired results;
  branches only for a result to be maintained against the evolving core.
- **D7. `public_scheduling_sequential_equilibrium`.** Keep (about 2k lines
  beyond the concurrent cone) or tag.
- **D8. Naming scheme.** Settle before Step 2 renames anything, so every name
  changes once. Proposed: "contract" for compiled output, never "runtime";
  theorem names of the form premise game, target, notion (for the concurrent
  theorem: concurrent, intended, raw, sequential equilibrium).

## Findings

Severity: H high, M medium, L low. "Step" is the step that resolves the finding.

### Claims and evidence

- [ ] **F-C1 (H, Step 2).** `concurrent_source_raw_sequential_equilibrium`
  assumes an SE of the intended game (`SourceEquilibrium`,
  `Vegas/Game/ConcurrentRawSequentialPreservation.lean:102`), not of the
  source game; its name and README say "source".
- [x] **F-C2 (M, Step 2).** README omits scope conditions of the concurrent
  theorem: a non-strategic first-in-first-out service that clears every pending
  packet at each processing cycle, complete pending observation, a constant exit
  payoff, and payoff zero for a run unfinished at the horizon.
- [ ] **F-C3 (H, Step 5).** Ten of the 23 Paper theorems are never applied to
  a concrete program: exclusion SE, public-scheduling SE, the one-packet SE,
  turn-based SE, and six of the asynchronous Nash forms (only `Vegas.Paper.async_first_turn_nash_iff`
  has an instance). The retired calendar theorems had none either.
- [ ] **F-C4 (H, Step 5).** The only instance of the concurrent hypotheses
  (`VegasTests/ConcurrentRawHypotheses.lean`) has no strategic content: Bob's
  payoff is identically zero and every profile gives Alice one half
  (`honest_alice_value`). The capstone is never applied to it.
- [ ] **F-C5 (M, Step 5).** `settle_late_not_preserved_for_every_margin`
  quantifies over the SEs of a game with no proof that it has one; the
  `late_leak_*` and `CommitSeedSignalling` obstructions omit existence from
  their statements although it is proved nearby. The `late_leak_*` Paper
  theorems now state that the late game has a sequential equilibrium
  (`Vegas.lateLeak_exists_sequentialEquilibrium`); the settle-late game still
  lacks a decision-recall proof.
- [ ] **F-C6 (L, Step 5).** The concurrent joint law reads the initial inputs
  from the terminal store rather than from the native initial draw.
- [x] **F-C7 (L, Step 2).** `one_packet_raw_sequential_equilibrium` uses
  `IsSequentialEquilibriumFor` with a truncated context instead of
  `IsSequentialEquilibrium`. It and `recovery_intended_raw_sequential_equilibrium`
  now state `IsSequentialEquilibrium`, through the raw protocol's horizon bound.

### Trust base

Verified faithful: Kreps–Wilson consistency (`IsSequentiallyConsistent`),
sequential rationality at every information set against whole-policy
deviations, Nash and ε-Nash, beliefs as distributions over information sets,
perfect recall proved for every model, horizons equal to proved bounds.

- [ ] **F-T1 (L, Step 5).** Unfinished runtime executions pay a literal zero
  (`serviceBaseUtility`, `phaseExclusionBase`); make it a named parameter or
  prove every terminal history reads out.
- [ ] **F-T2 (L, upstream).** Library information fibers may contain terminal
  histories (`BehavioralAssessment.lean:62-69`); inert in Vegas, where every
  model proves its sites nonterminal.

### Proof policy

- [x] **F-P1 (H, Step 1).** `warn.sorry = false` with an empty obligation
  registry: a `sorry` produced by a macro passes the build and the text check
  (core `stop` expands to `repeat sorry`). Only declarations under an axiom pin
  are protected.
- [x] **F-P2 (M, Step 1).** The pin check accepts `#guard_msgs (drop all)`,
  ignores the expected axiom text, and misses theorems with attributes or
  modifiers.
- [x] **F-P3 (M, Step 1).** The option check reads only the top-level option
  table; options set per library or through command-line definitions pass.
- [ ] **F-P4 (M, Step 6).** `backward.isDefEq.respectTransparency = false` is
  global; nothing records which proofs need it. Prefer `@[implicit_reducible]`
  on the carriers.

### Language and models

- [ ] **F-L1 (H, Step 5).** `ret` payoffs are never read by a game, a capstone
  or Paper; both auction examples write `.ret []`, and `simpleExpr` cannot
  express their utilities.
- [ ] **F-L2 (H, Steps 3–4).** About eight source-level games and three
  compiled contracts; see [model inventory](#model-inventory).
- [x] **F-L3 (M, Step 2).** The language's limits (straight-line, fixed actors,
  every move a commit and a reveal, guards cannot read their author's private
  inputs) are not stated in README or source-semantics.md.
- [ ] **F-L4 (L, Step 5).** A guard failure lands on whichever reveal completes
  the guard (`Vegas/Source/Semantics.lean:355-363`): a value may violate its own
  guard and publish as a success while a later reveal fails.
- [x] **F-L5 (M, Step 3).** `check-module-boundaries.py` checks only imports into
  `Vegas.*`; it cannot see Source importing the Interaction runtime or analysis
  layers. Foundation, Expr, Source, EventGraph and Compile may now import neither
  `Interaction` nor the analysis libraries, except that the commit- and
  proposal-recovery carriers in Source may use analysis until they move to the
  proof layer.

### Size, duplication and proof engineering

- [x] **F-S1 (H, Step 3).** 2,165 of 3,777 modules (about 428k lines) contain no
  declaration used by Paper or by a test declaration; 35% of declarations are
  reached from Paper. After Step 3 the report lists no module.
- [ ] **F-S2 (H, Step 4).** Parallel runtime stacks: 269k lines mention
  `WitnessedPacket`, 244k `CommitAttemptPacket`, 46 files both. Three copies of
  the one-packet raw extension theorem (`OnePacketExtension.lean`,
  `RecoveryOnePacketExtension.lean`, `PhaseOnePacketExtension.lean`; 81% and
  67% line overlap).
- [x] **F-S3 (M, Step 3).** 67 `CommitSeedBroadcast*` files are near copies of
  `CommitSeedSignalling*` files.
- [ ] **F-S4 (H, Step 6).** Eight declarations exceed 1,000 lines
  (`source_admitted_binding_row` about 1,957); statements with up to 83 explicit
  binders; one term spelled out 183 times in one file; the initial-law equation
  re-proved inline 39 times; 601 copies of one `local notation`.
- [ ] **F-S5 (M, Step 6).** 13 grouping namespaces with no type of that name
  hold 2,523 declarations (for example `Vegas.PhaseProposalQualifiedBinding`).
- [ ] **F-S6 (M, Step 6).** Flat directories: 1,496 files in Vegas/Game and 887
  in Vegas/Pending; the aggregators are unordered import lists.
- [ ] **F-S7 (M, Step 6).** The 136k lines of examples ship inside the `Vegas`
  library; the late-leak examples use no Vegas code.

### Tests

- [x] **F-X1 (M, Step 1).** 17.3k of the 21.2k VegasTests lines are 2,961
  hand-written axiom pins covering about 16% of theorems.
- [ ] **F-X2 (M, Step 5).** No small concrete tests for the pending runtime, the
  reserved-epoch scheduler, the count audit or belief transport; no `#eval` or
  `#guard` checks.

### Documentation and repository

- [x] **F-D1 (H, Step 2).** Docs describe the concurrent theorem as unproved or
  admitted: se-reserved-service-preservation.md:4-11,
  se-concurrent-code-inventory.md:39-43, se-concurrent-replay-analysis.md:5-6,
  module-architecture.md:17-19 and 2929-2937.
- [x] **F-D2 (H, Step 2).** ARTIFACT.md omits the concurrent theorem and 12
  other Paper pins; se-async-checklist.md:68 names the fixed-calendar theorem as
  the headline; two docs claim Paper pins that Paper no longer has
  (se-async-checklist.md:409, standard-runtime-se-status.md:71).
- [x] **F-D3 (M, Step 2).** LICENSE is MIT; every Lean header says "All rights
  reserved", two say Apache 2.0. Every header now names the MIT license.
- [ ] **F-D4 (M, Step 7).** module-architecture.md is 2,937 lines under one
  heading; 53 of 81 Markdown files are unreachable from README; six overview
  documents overlap. The module map is now grouped by layer, and
  [docs/README.md](README.md) reaches every Markdown file; the overlap remains.
- [x] **F-D5 (M, Step 3).** `archive/` keeps 1,105 tracked files; live docs link
  into it.
- [x] **F-D6 (L, Step 7).** scripts/README.md says investigation scripts are in
  the archive; 14 are tracked in scripts/experiments.
- [ ] **F-D7 (L, Step 7).** About 22 documentation sites encode history.
- [x] **F-D8 (L, Step 2).** AGENTS.md says to commit and push every checkpoint;
  an agent's note said to push only on request. The owner keeps the AGENTS.md
  rule.

### CI

- [ ] **F-I1 (M, Step 7).** The documentation job takes 89–138 minutes against
  a build of about 10, deploys Pages from any branch, and holds Pages
  permissions for the whole job; there is no concurrency group.
- [ ] **F-I2 (L, Step 7).** `GameTheory/.lake` is not cached, so each run
  rebuilds the submodule; each run saves a 4.8 GB cache.
- [x] **F-I3 (L, Step 1).** The checkers' comment and string strippers miss
  character literals, raw strings and guillemet names; the documentation check
  passes vacuously outside the repository root. Both checks now share one
  lexer that handles them, and the documentation check fails without a
  `lakefile.toml` in the working directory.

## Why the concurrent theorem assumes what it does

These counterexamples explain assumptions of
`Vegas.Paper.concurrent_source_raw_sequential_equilibrium`. The late-leak family
stays on `main`; the others are checked at the `research-tree` tag. The
arguments are in [semantics-and-enforcement.md](semantics-and-enforcement.md),
Sections I.5 and I.7.

| Assumption | Counterexample | Shows |
| --- | --- | --- |
| A failing player's payoff is a constant exit payoff, at most every terminal utility | `Vegas.Paper.late_leak_intended_outcome_not_preserved`, `Vegas.Paper.late_leak_outcome_preserved_by_failure_costs` | With continued play after failure, a forfeit charge, and late openings included with probability close to one, no sequential equilibrium of the late game keeps the intended outcome law; failure costs that make the failure branch worth the same to every type restore it. |
| The service is the reserved-epoch tape, which processes every pending packet at each cycle, not an arbitrary timely builder; collateral is fixed before the service | [`exists_service_with_no_preserving_equilibrium`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/LateOpeningRuntimeUniformSeObstruction.lean#L28), with variants under [all-or-none traffic sampling](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/LateOpeningRuntimeAllOrNoneSeObstruction.lean#L77) and [partial sender auditing](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/LateOpeningRuntimePartialAudit.lean#L190) | For a positive reward and any sufficiently large forfeit and deposits fixed first, one exogenous, commonly known finite builder meeting the timely-service requirements, with an arbitrarily small positive late-opening failure, has native sequential equilibria, and none realizes the source joint law. |
| The exit loss lies below every payoff a participant could receive | [`exists_honest_sequentialEquilibrium_without_native_preservation`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingNonpreservation.lean#L59); [the note](se-private-seed-signalling.md) | When packet timing reveals a hidden coin, a player controls which useful observations another receives. With the exit loss below the reward range, every native sequential equilibrium gives Alice at least one quarter, while every honest source profile gives her zero. |

The three-owner fixture behind
[se-strong-exclusion-signalling.md](se-strong-exclusion-signalling.md), which
tests an exit loss above the reward range, is at the tag with its native
obstruction unfinished.

## Retired results

Each row names the declaration or files at the `research-tree` tag, what they
show, and the models they need. They are checked at the tagged commit only.

| Result at the tag | Shows | Needs |
| --- | --- | --- |
| [`Vegas.Paper.source_audited_raw_sequential_equilibrium`](https://github.com/elazarg/VegasCore/blob/research-tree/Paper.lean#L43), [`Vegas.SourceServiceSpec.intended_audited_raw_sequentialEquilibrium`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/IntendedServiceCompilation.lean#L42) | SE preservation, from the source and from the intended game, on a fixed calendar that every player knows in advance | Plain contract, settled-record audit, calendar roster |
| [`Vegas.Paper.source_audited_raw_nash_iff`](https://github.com/elazarg/VegasCore/blob/research-tree/Paper.lean#L292), [`Vegas.Paper.source_audited_raw_nash_reflection`](https://github.com/elazarg/VegasCore/blob/research-tree/Paper.lean#L258), [`Vegas.Paper.intended_audited_raw_nash`](https://github.com/elazarg/VegasCore/blob/research-tree/Paper.lean#L428), [`Vegas.Paper.raw_service_horizon`](https://github.com/elazarg/VegasCore/blob/research-tree/Paper.lean#L114) | Nash correspondence and horizon on the same calendar | As above |
| The late-opening and seed-signalling counterexamples | See the previous section | Plain contract, specific services |
| [`CommitSeedBroadcast*`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedBroadcast.lean) | Three-owner timing fixture; obstruction unfinished | Plain contract |
| [`certain_late_inclusion_with_joint_contract`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommittedResolutionErasure.lean#L69) and the other `CommittedResolution*` examples | The service and erasure contracts do not force a positive late-failure floor | Plain contract |
| `PhaseTiming*`, most of `PhaseRecovery*` | An unfinished timing route for SE on the phase contract | Phase contract |
| [`Vegas/Language`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Language.lean) | Surface-syntax prototype, without semantics or elaboration | None |
| [`VegasTests/AxiomAudit`](https://github.com/elazarg/VegasCore/blob/research-tree/VegasTests/AxiomAudit.lean) | 2,961 hand-written axiom pins | None |
| [`archive/se-generalization`](https://github.com/elazarg/VegasCore/blob/research-tree/archive/se-generalization/README.md) | Uncompiled earlier designs, experiments and probes | None |
| [`docs/se-proof-checklist.md`](https://github.com/elazarg/VegasCore/blob/research-tree/docs/se-proof-checklist.md), [`scripts/check-se-evidence.py`](https://github.com/elazarg/VegasCore/blob/research-tree/scripts/check-se-evidence.py), [`docs/se-compilation-stack.md`](https://github.com/elazarg/VegasCore/blob/research-tree/docs/se-compilation-stack.md), [`ARTIFACT.md`](https://github.com/elazarg/VegasCore/blob/research-tree/ARTIFACT.md) | The calendar checklist, its evidence check, and overviews of the calendar proof | The calendar theorem |
| [`Vegas.onePacket_intended_sequentialEquilibrium_of_openInputs`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/OnePacketCertificateDischarge.lean#L4461), [`Vegas.onePacket_intended_raw_sequentialEquilibrium_of_blindInputs`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/OnePacketCertificateAssembly.lean#L443) and the rest of the one-packet certificate | Turn-based SE preservation of the one-packet game and its bounded raw runtime, assuming the certificate's open inputs (value blindness, late commitments); a route left conditional | Plain contract on the sequential graph, count audit |
| [`Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_commitRecovery`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/CommitRecoveryPreservation.lean#L22), [`Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_commitRecovery_continuing`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/CommitRecoveryContinuingExtension.lean#L24) | Intended SE extends to the source game with end-of-block rollback and permanent exclusion, keeping strategies, beliefs and the joint readout and payoff law | Source commit-recovery game |
| [`Vegas.phase_counted_raw_sequentialEquilibrium`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/PhaseRawReadoutLaw.lean#L27) | The raw count-audit extension of a phase-contract equilibrium keeps the typed readout jointly with the realized payoffs, for every scheduler | Phase contract, count audit |
| [`Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_extends_without_voluntary_failure`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/ExclusionMoveExtension.lean#L64) | Intended SE extends to the full exclusion game without voluntary failure at nonexcluded decisions, under a continuation payoff floor | Source exclusion-move game (decision D3) |
| [`Vegas.watched_raw_equilibrium_extends`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/RevealServiceWatcher.lean#L123) | An equilibrium with a silent watcher extends to the full bounded raw game of the reveal service | Plain contract, reveal service |
| [`Vegas.onePacket_intended_sequentialEquilibrium_of_certificates`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/OnePacketSequentialPreservation.lean#L71), [`Vegas.onePacket_intended_raw_sequentialEquilibrium`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/OnePacketSequentialPreservation.lean#L131) | Intended SE extends to the one-packet game and its bounded raw runtime, given the one-packet certificates and a deposit covering the spread of the exclusion payoff | Plain contract with exit payoff, count audit |
| [`GameTheory.Protocol.InformationModel.ActionRestriction.exists_deposits_preserving_sequential_equilibria`](https://github.com/elazarg/VegasCore/blob/research-tree/GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean#L269) | One finite nonnegative deposit vector extends every source SE to an audited target when each excluded action is collected with positive conditional probability | An action restriction and a sound terminal audit |
| [`GameTheory.Enforcement.exists_sound_deterrent_iff`](https://github.com/elazarg/VegasCore/blob/research-tree/GameTheoryExtensions/Analysis/ObservableEnforcement.lean#L168) | A sound alarm with a finite penalty deters one profitable deviation iff the deviation puts positive observable mass outside the admitted observations | None |
