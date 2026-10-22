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

**Truthfulness.** The designer can specify a truthful profile and state that it
is an equilibrium. Preservation of truthfulness is not a target (decision D4).

**Compiled output.** One compiled contract with one verdict and audit model on
the `Interaction` chain model. The environment (builder, observation, audit
coverage) is a parameter, and the strength of the preserved notion depends on
it.

**Theorem ladder.**

| Result | Environment | Graph | Present state |
| --- | --- | --- | --- |
| Compiler correctness: terminal law, unilateral deviation law, Nash equivalence on the ideal graph | none | any mode | checked: `canonical_setup_law`, `canonical_setup_deviation_law`, `Vegas.Paper.concurrent_event_nash_iff` |
| Nash preservation | any timely builder | sequential and concurrent | checked on the plain contract (`Vegas.Paper.async_first_turn_nash_iff` and siblings); to port |
| Non-concurrent sequential-equilibrium preservation | any timely builder, independent private inputs | sequential | checked on the forced-exit contract (`Vegas.recovery_intended_raw_sequentialEquilibrium_preserved`), not pinned in Paper; to port |
| Concurrent sequential-equilibrium preservation | reserved-epoch tape, complete pending observation | concurrent | checked on the phase contract (`Vegas.Paper.concurrent_source_raw_sequential_equilibrium`) |
| Intended game to source game | none | none | checked: `Vegas.Paper.intended_sequential_equilibrium`, `Vegas.Paper.intended_nash` |
| Late-leak impossibility | abstract game | none | checked: `Vegas.Paper.late_leak_intended_outcome_not_preserved` and siblings |

**Size.** The owner's estimate is 50–80k lines of Lean outside the GameTheory
submodule. [Measurements](#measurements) give the current floor and explain any
excess.

## Measurements

Measured at `8c67dad2` with a declaration-level dependency walk: from the root
theorems, follow `ConstantInfo.getUsedConstantsAsSet` through the project
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
| `SourceProgram.gameForm`, `Setup.gameForm` | Source semantics as a game form | keep one; `protocol_runBehavioral_eq` relates it to the protocol |
| `Setup.executionProtocol`, `Setup.informationModel` | Source semantics as an information model, parameterized by a commitment interface | keep |
| `Setup.intendedModel` | Analysis view: commitments hold predicted values, reveals open; premise of every SE theorem | keep |
| `Setup.exclusionModel`, `Setup.exclusionMoveModel` | Analysis view with a fixed exit payoff | decision D3 |
| `commitRecoveryModel`, `commitRecoveryErasedModel`, `proposalRecoveryModel` | Proof carriers of the concurrent SE theorem (26k of the 47k lines in Vegas/Source) | carrier: move to the proof layer and label |
| `Setup.valueBindingGame` | Pure value-binding game form, used only by the commit–reveal auction example; its behavioral edge (`Vegas/Game/ValueBindingEdge.lean`) is unused | remove the edge; keep the game form only with the example |
| `SourceProgram.Initial` | Duplicate of `Setup` with a point-mass initial state | remove |
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

### Step 0. Record

- [ ] Commit this ledger.
- [ ] Annotated tag on `main` naming the full research tree, so every later
      removal is recoverable by tag.
- [ ] Pin `recovery_intended_raw_sequentialEquilibrium_preserved` in Paper; the
      paper cites it as `thm:recovery`.

### Step 1. Guardrails that make removal cheap

- [ ] Remove `warn.sorry = false`, the open-obligation registry,
      `scripts/report-open-obligations.py` and its CI step. With
      `warningAsError` a `sorry` then fails the build.
- [ ] Replace the hand-written pins in `VegasTests/AxiomAudit` with one
      environment check that every declaration of the project libraries
      depends only on `propext`, `Classical.choice` and `Quot.sound`. Keep the
      Paper pins.
- [ ] Reduce `scripts/check-lean-options.py` to what the environment check does
      not cover: central options, and a ban on metaprogramming escape hatches
      (`addDecl`, `debug.skipKernelTC`, `ofReduceBool`, `+native`, library-level
      `leanOptions` and `-D` arguments).
- [ ] Add the dependency walk as a script: list modules with no declaration
      used by Paper or by a test declaration. Report only until Step 6.

Exit: green build; CI runs the environment check; the walk script is committed.
This step comes first because every removal would otherwise edit audit pins,
and because the hand-written pins cover only about 16% of the theorems.

### Step 2. Fix the contract

- [ ] Owner decisions D1–D8.
- [ ] Paper.lean states exactly the kept theorems, under the naming scheme of
      D8.
- [ ] One results table in README keyed to the Paper pins, with scope and
      hypotheses; ARTIFACT.md folded into it.
- [ ] Stale or contradictory status statements fixed or deleted (findings
      F-D1 to F-D4).

Exit: README, Paper and the docs agree; the documentation checks pass.

### Step 3. Prune to the kept cone

Per family: tag if it carries a citable result, remove, build, record. Largest
and most clearly orphaned first.

- [ ] `archive/` (git history already holds it).
- [ ] `OnePacket*` on the plain contract.
- [ ] `CommitSeedBroadcast*` (open obstruction), `CommitSeedSignalling*` and
      `LateOpeningRuntime*` examples, after tagging their checked obstructions.
- [ ] `PhaseTiming*`, `PhaseRecovery*`, and the `Recovery*`/`CommitRecovery*`
      modules outside every kept cone.
- [ ] `Vegas/Language`, the Communication chain (`Interaction/Communication*`,
      `Vegas/Source/Communication.lean`, `CommitmentEvidence`,
      `EventGraphEvidence`), `PayoffTransport`, `MessagePool`,
      `SourceProgram.Initial`, `Vegas/Game/ValueBindingEdge.lean`.
- [ ] The calendar family (`SourceService*`, `RevealService*`, the
      settled-record verdict, rosters), if D1 retires the calendar results.

Exit: the walk reports only modules on its allowlist; measurements updated.

### Step 4. One contract

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

- **D1. Kept theorem set.** Proposed: the ladder in [target](#target). Are the
  calendar results (`thm:sequential`, calendar Nash) retired as documented
  alternatives, as semantics-and-enforcement.md III.2 item 7 proposes? And
  which environment does non-concurrent SE need? Under any timely builder it
  is a separate proof (90k lines today, on its own contract). Under the
  reserved-epoch tape it may follow from the concurrent theorem on the
  sequential graph at little cost, if that theorem generalizes over the graph
  mode.
- **D2. The single contract.** Proposed: the phase contract.
- **D3. Source failure semantics.** Commit–reveal with exit
  (semantics-and-enforcement.md III.1), or the intended game with forfeit and
  exclusion payoff rewrites as analysis views only. This also decides the fate
  of `exclusionModel`.
- **D4. Truthfulness.** Proposed meaning: the designer names a profile that
  reports private inputs truthfully, and states that it is a Nash or sequential
  equilibrium of the source; preservation of the equilibrium property then
  follows from the ladder. Dominant-strategy truthfulness is specifiable but
  not preserved.
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
  theorem names of the form premise game, target, notion
  (`concurrent_intended_raw_sequential_equilibrium`).

## Findings

Severity: H high, M medium, L low. "Step" is the step that resolves the finding.

### Claims and evidence

- [ ] **F-C1 (H, Step 2).** `concurrent_source_raw_sequential_equilibrium`
  assumes an SE of the intended game (`SourceEquilibrium`,
  `Vegas/Game/ConcurrentRawSequentialPreservation.lean:102`), not of the
  source game; its name and README say "source".
- [ ] **F-C2 (M, Step 2).** README omits scope conditions of the concurrent
  theorem: a non-strategic first-in-first-out service that clears every pending
  packet at each processing cycle, complete pending observation, a constant exit
  payoff, and payoff zero for a run unfinished at the horizon.
- [ ] **F-C3 (H, Step 5).** No `SourceServiceSpec` is constructed anywhere: the
  calendar SE theorem and four Nash companions have no instance. Nine of the 26
  Paper theorems have no instance at all.
- [ ] **F-C4 (H, Step 5).** The only instance of the concurrent hypotheses
  (`VegasTests/ConcurrentRawHypotheses.lean`) has no strategic content: Bob's
  payoff is identically zero and every profile gives Alice one half
  (`honest_alice_value`). The capstone is never applied to it.
- [ ] **F-C5 (M, Step 5).** `settle_late_not_preserved_for_every_margin`
  quantifies over the SEs of a game with no proof that it has one; the
  `late_leak_*` and `CommitSeedSignalling` obstructions omit existence from
  their statements although it is proved nearby.
- [ ] **F-C6 (L, Step 5).** The concurrent joint law reads the initial inputs
  from the terminal store rather than from the native initial draw.
- [ ] **F-C7 (L, Step 2).** `one_packet_raw_sequential_equilibrium` uses
  `IsSequentialEquilibriumFor` with a truncated context instead of
  `IsSequentialEquilibrium`; `raw_service_horizon` holds by construction.

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

- [ ] **F-P1 (H, Step 1).** `warn.sorry = false` with an empty obligation
  registry: a `sorry` produced by a macro passes the build and the text check
  (core `stop` expands to `repeat sorry`). Only declarations under an axiom pin
  are protected.
- [ ] **F-P2 (M, Step 1).** The pin check accepts `#guard_msgs (drop all)`,
  ignores the expected axiom text, and misses theorems with attributes or
  modifiers.
- [ ] **F-P3 (M, Step 1).** The option check reads only top-level
  `[leanOptions]`; library-level `leanOptions` and `-D` arguments pass.
- [ ] **F-P4 (M, Step 6).** `backward.isDefEq.respectTransparency = false` is
  global; nothing records which proofs need it. Prefer `@[implicit_reducible]`
  on the carriers.

### Language and models

- [ ] **F-L1 (H, Step 5).** `ret` payoffs are never read by a game, a capstone
  or Paper; both auction examples write `.ret []`, and `simpleExpr` cannot
  express their utilities.
- [ ] **F-L2 (H, Steps 3–4).** About eight source-level games and three
  compiled contracts; see [model inventory](#model-inventory).
- [ ] **F-L3 (M, Step 2).** The language's limits (straight-line, fixed actors,
  every move a commit and a reveal, guards cannot read their author's private
  inputs) are not stated in README or source-semantics.md.
- [ ] **F-L4 (L, Step 5).** A guard failure lands on whichever reveal completes
  the guard (`Vegas/Source/Semantics.lean:355-363`): a value may violate its own
  guard and publish as a success while a later reveal fails.
- [ ] **F-L5 (M, Step 3).** `check-module-boundaries.py` checks only imports into
  `Vegas.*`; it cannot see Source importing the Interaction runtime or analysis
  layers.

### Size, duplication and proof engineering

- [ ] **F-S1 (H, Step 3).** 2,165 of 3,777 modules (about 428k lines) contain no
  declaration used by Paper or by a test declaration; 35% of declarations are
  reached from Paper.
- [ ] **F-S2 (H, Step 4).** Parallel runtime stacks: 269k lines mention
  `WitnessedPacket`, 244k `CommitAttemptPacket`, 46 files both. Three copies of
  `onePacket_raw_sequentialEquilibrium` (81% and 67% line overlap).
- [ ] **F-S3 (M, Step 3).** 67 `CommitSeedBroadcast*` files are near copies of
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

- [ ] **F-X1 (M, Step 1).** 17.3k of the 21.2k VegasTests lines are 2,961
  hand-written axiom pins covering about 16% of theorems.
- [ ] **F-X2 (M, Step 5).** No small concrete tests for the pending runtime, the
  reserved-epoch scheduler, the count audit or belief transport; no `#eval` or
  `#guard` checks.

### Documentation and repository

- [ ] **F-D1 (H, Step 2).** Docs describe the concurrent theorem as unproved or
  admitted: se-reserved-service-preservation.md:4-11,
  se-concurrent-code-inventory.md:39-43, se-concurrent-replay-analysis.md:5-6,
  module-architecture.md:17-19 and 2929-2937.
- [ ] **F-D2 (H, Step 2).** ARTIFACT.md omits the concurrent theorem and 12
  other Paper pins; se-async-checklist.md:68 names the fixed-calendar theorem as
  the headline; two docs claim Paper pins that Paper no longer has
  (se-async-checklist.md:409, standard-runtime-se-status.md:71).
- [ ] **F-D3 (M, Step 2).** LICENSE is MIT; every Lean header says "All rights
  reserved", two say Apache 2.0.
- [ ] **F-D4 (M, Step 7).** module-architecture.md is 2,937 lines under one
  heading; 53 of 81 Markdown files are unreachable from README; six overview
  documents overlap.
- [ ] **F-D5 (M, Step 3).** `archive/` keeps 1,105 tracked files; live docs link
  into it.
- [ ] **F-D6 (L, Step 7).** scripts/README.md says investigation scripts are in
  the archive; 14 are tracked in scripts/experiments.
- [ ] **F-D7 (L, Step 7).** About 22 documentation sites encode history.
- [ ] **F-D8 (L, Step 2).** AGENTS.md says to commit and push every checkpoint;
  the owner pushes only on request.

### CI

- [ ] **F-I1 (M, Step 7).** The documentation job takes 89–138 minutes against
  a build of about 10, deploys Pages from any branch, and holds Pages
  permissions for the whole job; there is no concurrency group.
- [ ] **F-I2 (L, Step 7).** `GameTheory/.lake` is not cached, so each run
  rebuilds the submodule; each run saves a 4.8 GB cache.
- [ ] **F-I3 (L, Step 1).** The checkers' comment and string strippers miss
  character literals, raw strings and guillemet names; the documentation check
  passes vacuously outside the repository root.

## Retired results

Each row names the tag that holds the result, its theorem, what it shows, and
the models it needs. Checked at the tagged commit only.

| Tag | Theorem | Shows | Needs |
| --- | --- | --- | --- |
