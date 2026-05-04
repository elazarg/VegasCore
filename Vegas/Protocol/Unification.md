# Vegas IR ↔ Machine Unification — Design Plan

## Goal

Eliminate the redundancy between Vegas's IR-side execution semantics
(`outcomeDist` / `outcomeDistPure` over `VegasCore` syntax) and the
machine-side trace/outcome semantics (`Machine.outcomeKernel` over
`graphMachine g hctx`). End state: one canonical execution semantics,
with `outcomeDist`-shaped facts derived from machine-level facts.

This document is the result of investigation done after the
`protocol-info-machine` branch landed, as a plan for follow-up work.

## End-state shape (the "cleanest design")

The cleanest end state is **not** "make `outcomeDist` an alias for
`Machine.outcomeKernel`". The deeper redundancy is:

`OmniscientOperationalProfile` is an evaluator-facing notion of
"how to make choices given full erased environments". The machine
already has `Machine.LegalEventLaw` — a state → PMF event scheduler
which is the canonical "how to make choices" abstraction.

So the cleanest end state is:

1. **Delete `Vegas/Operational.lean`** (the file containing
   `OmniscientOperationalProfile` and `CommitKernel`).
2. **Express `outcomeDist` as a derived definition** on the
   graph machine. Concretely, for a checked program `g`:

   ```
   def outcomeDistKernel (g : WFProgram P L) (hctx : WFCtx g.Γ)
       (law : (graphMachine g hctx).LegalEventLaw) : PMF (Outcome P) :=
     (graphMachine g hctx).outcomeKernel law.val (syntaxSteps g.prog)
   ```

   The legacy `outcomeDist sigma p env` becomes a thin compatibility
   wrapper over this, where `sigma : OmniscientOperationalProfile`
   is converted to a `LegalEventLaw` (or `OmniscientOperationalProfile`
   is itself replaced with a `LegalEventLaw`-shaped type).

3. **Strategic kernel rebuilt around event laws.** Pure profiles,
   behavioral profiles, and mixed profiles all become specific
   `LegalEventLaw` constructions on the graph machine. The current
   indirection through `outcomeDistPure` / `outcomeDistBehavioral` /
   `outcomeDistBehavioralPMF` collapses.

## What is already in place

- `Vegas/Protocol/Trace.lean`:
  - `Machine.traceDist`, `Machine.traceDistFrom`, `Machine.outcomeKernel`
  - `Machine.LegalEventLaw` from `Vegas/Protocol/Machine.lean:181`

- `Vegas/Protocol/Checked.lean`:
  - `graphMachine g hctx`, `graphMachineFOSGView g hctx`
  - `cursorWorldOfGraphConfiguration g hctx` projecting machine
    configurations to cursor worlds (which carry the IR's `env` + `prog`)
  - Cursor ↔ machine step equivalences (`graphStepPlay_project_*`,
    `graphMachine_step_map_cursorWorld_eq_cursorProgramTransition_of_available`)
  - `graphMachineTurn` deciding which player moves at each
    configuration based on the cursor program's head constructor:
    - `.commit _ who _ _` ⇒ `Turn.play who`
    - everything else (`.ret`, `.letExpr`, `.sample`, `.reveal`) ⇒
      `Turn.internal ()`
  - `graphMachine.outcome` is *definitionally* equal to
    `cursorWorldOutcome ∘ cursorWorldOfGraphConfiguration`

- `Vegas/PureStrategic.lean:489`:
  - `(toStrategicKernelGame g).outcomeKernel σ =
       (outcomeDistPure g.prog ...).toPMF`
  - This is the pure-strategy IR ↔ kernel-game bridge.

- `Vegas/StrategicPMF.lean:596`:
  - `(toKernelGamePMF g).outcomeKernel
       (LegalProgramPureProfile.toBehavioralPMF σ) =
     (toStrategicKernelGame g).outcomeKernel σ`
  - FOSG-side ↔ strategic-kernel-side equivalence.

## Stages

### Stage A — Event-law adapters (foundational, ~200 lines)

Define the conversions from the strategic-kernel strategy spaces to
graph-machine event laws.

```
namespace Vegas.Machine.GraphEventLaw
  variable {P : Type} [DecidableEq P] {L : IExpr}

  /-- One event chosen at a configuration under an omniscient profile. -/
  noncomputable def eventOfOmniscient
      (σ : OmniscientOperationalProfile P L)
      (g : WFProgram P L) (hctx : WFCtx g.Γ)
      (cfg : (graphMachine g hctx).State) :
      PMF (graphMachine g hctx).Event :=
    let cursor := cursorWorldOfGraphConfiguration g hctx cfg
    match cursor.1.cursor.prog with
    | .commit x who R _ =>
        ((σ.commit who x R (VEnv.eraseEnv cursor.1.env)).toPMF _).bind
          fun v => PMF.pure (.play who (programActionOfCommit cursor v))
    | _ => PMF.pure (.internal ())

  /-- The omniscient event law and a proof it is legal. -/
  noncomputable def lawOfOmniscient
      (σ : OmniscientOperationalProfile P L)
      (g : WFProgram P L) (hctx : WFCtx g.Γ) :
      (graphMachine g hctx).LegalEventLaw :=
    ⟨eventOfOmniscient σ g hctx, by …⟩

  -- Also: lawOfPure, lawOfBehavioral, lawOfBehavioralPMF
end Vegas.Machine.GraphEventLaw
```

The `programActionOfCommit cursor v` constructor needs to be derived
from the cursor's commit head. Look at how `singleProgramJointAction`
in `Vegas/Protocol/Checked.lean` builds program actions from values.

The `LegalEventLaw` proof obligation: at each configuration, the
chosen events lie in `EventAvailable`. Discharged by inspecting the
cursor head and using existing `graphAvailable` / `graphAvailableInternal`
characterizations.

### Stage B — Bridge theorem (~500-1000 lines)

Prove:

```
theorem outcomeDist_eq_machine_outcomeKernel
    (σ : OmniscientOperationalProfile P L)
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (hd : NormalizedDists g.prog) (hσ : σ.NormalizedOn g.prog) :
    (outcomeDist σ g.prog g.env).toPMF (by
        exact outcomeDist_totalWeight_eq_one hd hσ) =
      (graphMachine g hctx).outcomeKernel
        (lawOfOmniscient σ g hctx).val (syntaxSteps g.prog)
```

Proof strategy:
1. Induction on `syntaxSteps g.prog`. At each step the configuration's
   cursor has a definite head (`ret`/`letExpr`/`sample`/`commit`/`reveal`);
   the machine step distribution refines through `cursorWorldOf-`
   projection to the cursor program transition.
2. Match the eventLaw firing against the corresponding `outcomeDist`
   recursion case via cursor agreement lemmas already in
   `Vegas/Protocol/Checked.lean`.
3. Use `outcomeDist_comm_commit` / `outcomeDist_comm_reveal` (now in
   `Vegas/BigStep.lean`) to handle ordering differences between the
   IR's syntactic order and the action graph's frontier-completion
   order, if any arise. (They likely don't if the linearization
   chosen by `graphMachineTurn` is exactly the IR order, which it
   appears to be by construction.)

Risk: the bookkeeping to align FDist↔PMF and to track the cursor
position through `syntaxSteps`-many machine steps is tedious. Plan
on this stage being the bulk of the work.

### Stage C — Pure-strategy specialization (~50 lines)

Once Stage B holds for omniscient profiles, derive the pure version
as a corollary:

```
theorem outcomeDistPure_eq_machine_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (σ : LegalProgramPureProfile g) :
    (outcomeDistPure g.prog (fun i => (σ i).val) g.env).toPMF (...) =
      (graphMachine g hctx).outcomeKernel
        (lawOfPure σ g hctx).val (syntaxSteps g.prog)
```

This connects to `(toStrategicKernelGame g).outcomeKernel σ` directly
via `PureStrategic.lean:489`.

### Stage D — Collapse `outcomeDist` (~1000 lines + cascading edits)

Replace `outcomeDist` and `outcomeDistPure` with definitions in terms
of `Machine.outcomeKernel`. Concretely:

1. Mark `Vegas/BigStep.lean:outcomeDist` as deprecated.
2. Add `outcomeDistFromMachine` definitions producing `PMF` directly.
3. Update each consumer:
   - `Vegas/PureStrategic.lean:303` `outcomeDistPure`
   - `Vegas/Strategic.lean:223` `outcomeDistBehavioral`
   - `Vegas/StrategicPMF.lean:268` `outcomeDistBehavioralPMF`
   - `Vegas/FOSG/Observed/Kernel.lean` (cursor-world kernel)
   - `Vegas/SmallStep/Properties.lean` (uses `outcomeDist_comm_*`)
   - `Vegas/SmallStep/Agreement.lean` (uses `outcomeDist`)
4. After all consumers are migrated, delete the legacy definitions.
5. Delete `Vegas/Operational.lean` (`OmniscientOperationalProfile`).

Risk: each consumer file may need new infrastructure to express what
it needs in machine terms. Some theorems may need restating.

### Stage E — Strategic kernel cleanup (~500 lines)

With `outcomeDist` collapsed, the strategic kernel can be simplified:

- `Vegas/PureStrategic.lean:toStrategicKernelGame` becomes a thin
  shell over `lawOfPure` + `Machine.outcomeKernel`.
- `Vegas/StrategicPMF.lean:toKernelGamePMF` similarly.
- The FOSG-side bridge (`Vegas/FOSG.lean:1199` etc.) potentially
  simplifies because there's only one outcome semantics to relate to.

## Order of work (recommended)

1. Stage A first (foundational, contained).
2. Stage B (the proof) — the bulk of the multi-day work.
3. Stage C (corollary, easy).
4. Stage D (cascading edits, mechanical but wide).
5. Stage E (cleanup).

Each stage should land as its own commit. Stages A, B, C are
non-breaking additions; Stage D breaks consumers and must land
together with their migrations; Stage E is pure simplification.

## Out-of-scope adjacents

- **`FOSGBridge` namespace flattening** in `Vegas/FOSG.lean`. Same
  no-grouping-namespace rule applied in `protocol-info-machine` to
  `Protocol`/`Checked` should be applied here. Touches all external
  references including `README.md` and `latex/main.tex`. ~30 minutes.

- **`expandCommitReveal` rewrite** as a proven Lean theorem, mirroring
  the Kotlin implementation at `../vegas/src/main/kotlin/vegas/ir/ActionDag.kt:184-339`.
  Currently Lean has only the predicate `NeedsCommitRevealSplit`
  (`Vegas/Protocol/ActionGraph.lean:1136`). Independent of this
  unification.

## Resurrection map

If anything from this design plan turns out to be the wrong direction,
the load-bearing pieces can be restored:

- `Vegas.Trace` is at `git show 127486d:Vegas/TraceSemantics.lean`
- Old `Vegas/ActionGraph.lean` (event-DAG) is at
  `git show 5ced9ea:Vegas/ActionGraph.lean`
- Pre-merge cursor-world FOSG primary semantics is at
  `git show 5ced9ea:Vegas/FOSG.lean` (master before
  `protocol-info-machine` merge).
