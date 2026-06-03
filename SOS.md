# Small-step Operational Semantics (SOS) — plan & roadmap

> **Status.** This milestone implements only the **minimal Layer 1** below: the
> simplest faithful sequential small-step relation on `VegasCore`, whose single
> purpose is to give a programmer the most intuitive understanding of what a
> program does. Layers 2–4 (graph schedule observational equivalence and the
> source↔graph linearization that make "the player does not care about the
> schedule" a precise theorem) are the recorded roadmap, **not yet built**.

## Context

`VegasCore` (4-constructor source syntax `ret`/`sample`/`commit`/`reveal`,
`Vegas/Core/Basic.lean`) has no direct operational semantics today; meaning is
reconstructed indirectly via `compile → Graph →` schedule-free graph execution
`→ sourceOutcomeAtTerminal`. The small-step is the missing, most-straightforward
definition of *what a program does*, threading a `VEnv L Γ`. It is deliberately
**sequential** (each constructor has one continuation), so it is simpler than the
graph's concurrency. The inherent complications it must faithfully carry are
**probability** (`sample` draws from a distribution) and **information hiding**
(`commit` guards see only the actor's view; `reveal` exposes a hidden value).
It must NOT bake in observability/concurrency/proof foresight.

## Layer 1 — minimal sequential small-step (Core) — THIS MILESTONE

New `Vegas/Core/SmallStep.lean`, imports only `Core/Basic` + `Foundation/Payoff`.

- `SourceConfig P L` = `{ ctx : VCtx P L, env : VEnv L ctx, cont : VegasCore P L ctx }`.
- `SourceConfig.initial prog`, `SourceConfig.outcome?` (`.ret p ↦ evalPayoffs p env`),
  `SourceConfig.IsTerminal`.
- `SmallStep : SourceConfig → SourceConfig → Prop`, three rules:
  - `sample`: draw `v` from `(L.evalDist D' env.eraseSampleEnv).support`, bind `(x,.pub b)`.
  - `commit`: choose `v` with `evalGuard R v ((env.toView who).eraseEnv) = true`, bind `(x,.hidden who b)`.
  - `reveal`: bind `(y,.pub b)` to the looked-up hidden value `env.get hx`.
  Uses the **direct indexed form** (`SmallStep ⟨Γ, env, .sample x D' k⟩ ⟨…⟩`) —
  the canonical SOS presentation; empirically it inverts (`cases`) and supports
  forward/progress-style construction just as cleanly as the equation-field
  encoding, so the more intuitive form wins.
- `SmallStep.Star` (reflexive-transitive closure) so full runs are expressible.
- **Labels (instrumentation).** `Label`, the labeled relation `LStep`, and the
  forgetful bridge `smallStep_iff_exists_label`. Labels add *no behavior*; the
  unlabeled `SmallStep` is the explanatory headline (the paper introduces it
  first), and labels are an annotation used only by later stages (linearization,
  per-player/epistemic views). A label records the *full* action; information
  hiding is applied later as a per-player view of labels, not baked in here.

Faithfulness notes: the relation is support-level (it records which transitions
are *possible*: nature draws from `D`, players choose subject to the guard). The
quantitative weights live in the existing denotational/graph layers; they are not
needed for the operational "what can happen next" reading. Intentionally omitted
as "beyond minimal": the FWeight kernel/event objects, progress/determinism
meta-theory, and anything observability-related.

## Roadmap (NOT in this milestone)

### Layer 2 — graph schedule observational equivalence (EventGraph)
`ObsEquiv G c d := publicObserve G c = publicObserve G d ∧ ∀ who, observe G c who = observe G d who`.
Headline `terminal_config_unique_of_values` (value-pinned confluence via the
existing `supported_available_events_diamond`) ⇒ all schedules obs-equivalent.
Sample draws must be pinned by a value function (naive "same config" is false
across draws). `canonicalSchedule` = complete least-unfinished node (topological
by `prereq_lt`).

### Layer 3 — source↔graph linearization (Compile, over `WFProgram`)
Node id `k` ⟺ `k`-th non-`ret` source constructor. `SourceGraphSim` invariant
(done = initial segment; store ⟺ `VEnv.cons` chain). New prefix analogues of the
terminal-only `BuildResult` adequacy (`prefixStoreAvailable`, `sim_step`,
`source_run_simulates_canonical`). Payoff: the sequential run is obs-equivalent
to every schedule, and source outcome = `sourceOutcomeAtTerminal`.

### Layer 4 — paper-facing claims + audit (Theorems / Spec)
`claim_schedule_discarded_is_unobservable` et al. in `Theorems/Claims.lean`;
`#check` pins in `Spec.lean`; axiom footprint `[propext, Classical.choice, Quot.sound]`.

## Why "the player does not care" is provable (mechanism, for the roadmap)
`observe` is footprint-local (only a player's ready-commit `guard.choiceReads`).
Reading a field makes its writer a prerequisite (`nodeTarget_mem_prereqs_of_read`,
`prereq_lt`), so two mutually-concurrent events can never both be in one observer's
footprint — observation factors through the dependency down-set shared by every
linearization. The per-swap version is already proven (`two_event_swap_observations`,
`two_event_swap_after_prefix_with_tail_observations`, `EventGraph/Batch.lean`).
