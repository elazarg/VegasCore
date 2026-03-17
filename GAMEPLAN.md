# StratLet Design: Effectful Protocol Extensions and Game Assumptions

## 1. Goal

StratLet is organized around two independent layers:

1. **Effectful protocol extensions**: executable protocols with named decision points and explicit information restrictions, extended with *abstract* observable effects (events) that are recorded during execution.

2. **Games**: a protocol (possibly effectful) paired with explicit, common-knowledge assumptions (utilities, constraints, analysis goals). Assumptions are syntactic artifacts used for reasoning and automation; they do not change execution.

The intent is to make the bridge from “mechanism program” to “game-theoretic object + solver/checker pipeline” automatic and auditable, without hardcoding domain meaning (e.g., “transfer”) into the operational semantics.

---

## 2. Layer A: Effectful Protocol Extensions

### 2.1 Purpose

Provide a generic way to attach observable “things that happened” to protocol executions. These observables serve as the stable referent for downstream interpretation (utilities, conventions, enforcement models) without committing the protocol semantics to any particular domain.

### 2.2 Baseline protocol contract (assumed)

StratLet assumes an existing protocol calculus with:

* **Decision sites** identified by stable IDs (`YieldId`).
* **Information restriction** at each decision site via explicit views/projections.
* **Randomness** (`sample`) and deterministic binding (`let`/`bind`).
* **Observation/filtering** (`observe`) according to the existing model.
* **Profiles** that resolve decision sites, and a rewrite `applyProfile` supporting partial profiles.
* **Extension Lemma**: total profiles extending partial profiles preserve evaluation after applying the partial profile.
* Canonical semantics into a weighted finite-support distribution (`WDist`).

This document does not prescribe the internal encoding of the baseline calculus; it only relies on the contract above.

### 2.3 Effect extension interface

An effect extension is parameterized by an **abstract event type**:

* `Ev : Type`

Optionally, for downstream counting/filtering, require:

* `[DecidableEq Ev]`

No other structure is assumed at the protocol layer.

### 2.4 Extended protocol language

Define an extended protocol language (conceptually “Protocol + emit”) that:

* preserves all baseline protocol constructs unchanged, and

* adds a single observational instruction:

* `emit : Ev → Protocol⁺ Ev Γ Unit` (or an equivalent statement form)

Design constraint:

* `emit` is observational only: it does not branch, sample, or fail. It only records an event.

**Important:** the effect extension is *not required* to care about the specific baseline protocol definition. The extension should be implemented as a thin layer over the protocol interface, not by baking `Ev` into the core inductive unless that is already the project’s preferred pattern.

### 2.5 Trace

Define:

* `Trace Ev := List Ev`

A trace is produced during evaluation and is the canonical record of performed effects.

### 2.6 Canonical semantics

Extend evaluation to return both the usual terminal value and the trace:

* `eval⁺ : Profile → Protocol⁺ Ev Γ τ → Env Γ → WDist (Val τ × Trace Ev)`

Operational meaning:

* `emit e` appends `e` to the current trace.
* all other constructs behave as in the baseline semantics, with trace threaded through.

### 2.7 Required meta-theorems (effectful protocol layer)

The following must hold for the extended language:

1. **Lifted Extension Lemma**
   If a total profile extends a partial profile, evaluation is unchanged after applying the partial profile rewrite (now in the trace-returning semantics).

2. **Information locality preserved**
   Adding `emit` does not weaken the locality guarantee at decision sites: decision resolvers remain functions only of view-projected environments.

3. **Emit transparency**
   Any baseline rewriting pass that only transforms decision resolution (e.g., `applyProfile`) leaves emitted events structurally intact (up to definitional equality or a simple lemma).

### 2.8 Non-goals (effectful protocols)

* No built-in interpretation of events (“money”, “transfer”, etc.).
* No enforcement semantics or conservation laws at this layer.
* No equilibrium or rationality assumptions.

---

## 3. Layer B: Games as Protocol + Assumptions

### 3.1 Purpose

Define games as analysis artifacts that attach explicit, common-knowledge assumptions to protocols. These assumptions interpret traces (and optionally returned values) as utilities and constraints and provide the interface for game-theoretic reasoning and solver integration.

### 3.2 Game artifact

Define the primary analysis object as:

* `Game Ev := { protocol : Protocol⁺ Ev Γ τ, assumptions : Assumptions Ev }`

(Or more generally: allow any protocol satisfying the baseline contract; `Ev` may be absent if no effects are used.)

Optionally include explicit control/player structure if it is not recoverable from protocol syntax:

* player set/type used for analysis,
* mapping from decision-site IDs to players (if needed as separate metadata).

### 3.3 Assumptions bundle

Assumptions are explicit syntax (common knowledge) and do not affect execution. At minimum:

1. **Players**
   A finite player index used for analysis (e.g., a finite type `ι` with `Fintype`, or a finite set of `Player`).

2. **Utility specification**
   A per-player syntactic object that evaluates against the protocol outcome:

   * the trace `Trace Ev`,
   * the returned value `Val τ` (optional but allowed),
   * the player identity.

Utilities must not require access to hidden runtime state unless that state is made observable via events or returned value.

3. **Conventions / admissibility (recommended)**
   A syntactic predicate over traces describing what histories are meaningful/enforceable under the intended interpretation (e.g., constraints relating events). This layer is where “transfer vs print” distinctions live: not in operational semantics, but as explicit modeling commitments.

4. **Analysis goal (optional)**
   Declarative metadata intended for tooling (e.g., “compute/check ε-equilibrium on a finite instantiation”). This is not operational.

### 3.4 Private parameters and valuations

Assumptions must support models involving unknown private values (e.g., bidder valuations). The design requirement is:

* Utilities (and conventions) may refer to explicit private parameters indexed by players.
* How private parameters connect to protocol behavior is left open, but must be explicit:

  * either parameters are instantiated externally (finite analysis),
  * or the protocol contains constructs that introduce private information (e.g., sampling with restricted views) and emitted events/choices relate them to observable behavior.

This flexibility is intentional; it avoids prematurely committing to a specific private-information mechanism while keeping the assumptions explicit.

### 3.5 Expected utility

Expected utility is defined exclusively from:

* the canonical semantics of the effectful protocol, and
* the utility evaluator induced by assumptions.

Shape:

* `EU(G, σ, env, i) := EV (eval⁺ σ G.protocol env) (fun (v, tr) => U(G.assumptions, i, v, tr))`

Conventions/admissibility are handled at the game layer, not by altering execution semantics. If a trace violates a convention, it is treated via the chosen modeling rule (typically utility penalties or restriction of admissible strategies), but not by conditioning the execution distribution unless explicitly intended and documented.

### 3.6 Deviations and equilibrium notions

Equilibrium notions quantify over deviations in **profiles** subject to:

* legality at decision sites (action sets),
* information locality (views),
* any additional constraints declared in assumptions.

No equilibrium definition depends on a special execution semantics beyond `eval⁺`.

### 3.7 Finite fragments and denotation

Standard game-theoretic representations (EFG/NFG/MAID) are produced only for explicitly identified finite fragments. A finite-fragment predicate must capture the finiteness/decidability conditions needed for extraction and evaluation.

For finite-fragment games:

* define `toEFG : Game Ev → EFG` (and optionally others),
* establish a correctness statement relating expected utilities computed from:

  * canonical semantics + utility interpretation, and
  * the denoted representation under translated strategies.

All such results are conditional on the finite-fragment predicate.

### 3.8 Non-goals (game layer)

* No claim that assumptions are objectively “true”; they are explicit modeling commitments.
* No requirement to implement solvers in Lean; solver integration is external, with internal checkers for finite instances.

---

## 4. Separation guarantees

The architecture enforces:

1. **No dependency from protocols to games**
   Protocol and effect-extension code does not import assumptions or equilibrium reasoning.

2. **Single canonical execution semantics**
   Execution meaning is entirely captured by `eval⁺ : … → WDist (Val × Trace Ev)`.

3. **Assumptions are interpretive only**
   Assumptions influence analysis by interpreting outcomes and constraining deviations, not by changing operational behavior.

---

## 5. Implementation milestones

1. Implement the effect extension with abstract `Ev` and `emit`, and lift evaluation to `WDist (Val × Trace Ev)`. Port/prove the lifted Extension Lemma.
2. Define the assumptions bundle (players, utilities over trace/value, conventions/admissibility).
3. Define `Game Ev := protocol × assumptions` and expected utility from canonical semantics.
4. Define a finite fragment predicate and a first denotation to EFG for that fragment.
5. Provide one end-to-end example demonstrating:

   * effect events used to expose the relevant observables,
   * utilities referencing those observables and private parameters,
   * a finite instantiation suitable for extraction/solver/checking.

Stop after (3) is stable and the lifted Extension Lemma holds. Proceed to denotations only once the protocol/assumptions contract is frozen.
