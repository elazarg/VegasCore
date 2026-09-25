# Sequential equilibrium: research plan and claim boundary

## Objective

Prove an actual source-to-native theorem for a useful class of games under a
small, explicit service contract. Keep source syntax and the compilation tower
unchanged until a concrete proof needs a change. The full native SE theorem is
**open**; the results below identify a first target and its acceptance tests.

The minimum target fixes the source program, utilities, service and compiled
game **before** choosing an equilibrium:

> For every source sequential equilibrium, there is a sequential equilibrium
> of that fixed native game with the same joint initial-type/public-result law
> and the same net payoff law.

This is forward equilibrium-outcome implementation. A fixed playerwise policy
compiler is stronger and remains desirable, especially for the first fragment.
Reflection of every native equilibrium is separate. Matching expected utility
alone is weaker. Choosing new fines or a new target game for each equilibrium
does not meet this target. A game compiler may use the declared utility bounds.

## What is already established

| Question | Checked result | Boundary |
| --- | --- | --- |
| Can disclosure incentives be controlled at all? | Every SE of the finite private-state sender/terminal-receiver class extends under sufficient disclosure charges, with exact state and net payoff laws. Range bounds fix one game and playerwise compiler for all source SEs. | The charge is specified in utility; this is not yet a native monitor implementation. |
| Can players themselves supply the deterrent? | In that class, statewise constant-sum payoffs require no disclosure charge: an informed receiver's optimal response deters the sender. | No general multistage or multiplayer theorem. |
| Can ordinary pending-message observation detect the native attack? | The actual unsupported certificate is reportable before ledger inclusion; sampling and conditional report-delivery bounds are checked. | Coverage, liability, timely adjudication and collection are not supplied by observation alone. |
| Can every covert signal be detected? | A shared pad permits signaling inside lawful observable support, defeating every alarm with zero false positives. | This is a detection limit, not a claim that every such channel destroys SE. |
| Does a larger fine solve off-path credibility? | Local conditional incentive bounds are checked. | General consistent continuation completion is open; a sunk fine cannot be counted again as a future cost. |
| Do zero-sum or CE results already close SE? | The paper service preserves zero-sum equilibrium value, including native CCE value. Equal normal-form CE content can coexist with different SE outcomes. | Value is not outcome-law equality; the finite reactive service needs its own bridge. |

The [artifact map](../ARTIFACT.md) identifies the Lean declarations. The
[enforcement design](disclosure-enforcement-design.md) gives the finite theorem
and its exact scope. No result here establishes coalition preservation.

## First priority: one monitored native decision game

Start with the terminal-receiver strategic pattern already proved. Reuse the
existing raw response menu, passive foreign observations and at-most-once
inclusion. Do not replace the runtime by the abstract disclosure experiment or
delete the transmissions the monitor is supposed to deter.

The [native pilot audit](research/se-native-pilot.md) proposes two source reveals:
Bob opens or withholds a preinstalled `true` commitment to encode his guess;
Alice subsequently opens her hidden bit. Correct guesses pay both players;
failure of Alice's final opening carries a source penalty. Her opening must be
proved optimal in every native continuation before collapsing that last choice
to the checked decision-game pattern. Native initialization of these bindings
is part of the proof; seeding a continuation alone is not a complete compiler.

Allow Alice an extra native transmission before Bob acts. An ordinary watcher
can sample and replay the original envelope for inclusion. The proposed fine
uses the resulting rejected-call receipt. This needs a proof that these early
Alice packets are rejected while every legal source choice has an unpunished
implementation. Report inclusion before Bob's move also exposes information:
prove Bob's posterior and optimal continuation after it. Collecting the fine
at termination does not erase the earlier report.

| Obligation | Concrete acceptance test |
| --- | --- |
| Faithful permitted behavior | Every source choice, including withholding and failure, has an unpunished realization; reconstruct source observations and remaining choices at every admitted decision. |
| Complete treatment of native responses | Include malformed packets, early ordinary openings, evidence forwarding, silence, retries, identifiers and timing. Classify each as source behavior, irrelevant behavior with a proof, or a detectable departure. |
| Conditional deterrence | Bound the gain and additional future net collection at each sender information set and departure. An average monitoring rate is insufficient. Preserve attribution and available collateral. |
| Native sequential equilibrium | Construct optimal continuations after received evidence, not obedience to the source policy after its information assumptions fail. Supply one common fully mixed sequence for all beliefs. |
| Exact result | Prove joint initial-type/result and net payoff-law equality for every source SE in one fixed compiled game. Account for all strategic players and all their native deviations. |

The pilot watcher is a strategic player with zero utility throughout: its
chosen reporting policy can be rational by indifference. This is a deliberately
limited existence target, not a guarantee that every native equilibrium reports
or an economic implementation of paid watchers. Sampling, timely inclusion and
collectible loss remain explicit service assumptions. A deposit also needs a
stated relation to utility. An oracle variant would assume the reporting policy
instead; keep these two claims distinct.

## Broader routes, ordered by the evidence needed

1. **Generalize a successful native fragment.** Only after the pilot closes,
   extend to another source decision or a genuinely necessary service feature.
   The proposed general first-departure/rare-tremble theorem is useful only if
   the actual permitted native game implements the source action restriction.
   Its continuation completion may select policies from the entire source
   assessment, giving the minimum theorem rather than a playerwise compiler.
2. **Retain unavoidable ambient evidence.** If lawful traffic carries useful
   information that cannot be soundly sanctioned, expose that capability in
   the source interpretation using named game facts and evidence possession.
   This is one semantic environment, not new game syntax or an extra runtime
   language. Prove its correspondence to actual delayed, partial observations;
   the existing synchronous communication experiment does not establish it.
   Ordinary-source equilibria still need a separate extension theorem.
3. **Competitive games without monitoring.** The two-player zero-sum route
   needs both law-preserving Nash-to-SE repair and a Nash bridge into the same
   finite native game. Keep the written repair proof and checked ingredients;
   do not build more repair machinery before testing that runtime bridge.

There is no single weakest assumption across these routes: restricting games,
adding an enforcement service and changing the source communication environment
are different choices. Compare their proved scope and operational cost.

## Scope controls and ownership

- `GameTheoryExtensions/`: finite equilibrium, consistency, information and
  sanction arguments; no blockchain assumptions or GameTheory submodule edits.
- `Interaction/`: actual observations, response laws, reporting and conditional
  probability adapters; no game-specific conformance rule.
- `Vegas/`: source choices, packet conformance, service instantiation and
  source-to-native laws. Put decisive finite witnesses in the existing test roots.
- The paper claims only closed theorems. Keep the ordinary Nash/Bayesian edge
  distinct from the reactive runtime under investigation for SE.

No new compiler flags or tower levels are justified by this plan. In particular,
packet shape, validity, submission readiness and publication are different
proof obligations; calling them all "conformance" does not discharge them.

## Deferred work and reading guide

Treat these as follow-up research, not dependencies to expand the pilot:
strategic watcher incentives and side contracts; CE and coalition deviations;
possession-based cryptographic refinement and shared keys; threshold release,
mediators and reverse firewalls; unbounded interaction; computational or
approximate sequential equilibrium.

Noise, batching and canonical traffic belong to that last quantitative route.
Batching ledger inclusion does not erase pending observations. Canonical fields
remove only the choices they actually control. A noisy channel can still have
profitable information value; exact SE needs conditional incentives at every
relevant information set. A future approximation theorem would need utility
bounds, channel/observation bounds and any claimed costs or strict margins.
No SNR threshold is currently assumed or proved to preserve native SE.

For details, read only the relevant audit:

- [Proof routes](research/se-proof-routes.md): quantifiers, missing mathematical
  lemmas and decisive runtime tests.
- [Conformance audit](research/se-conformance-audit.md): actual counterexamples,
  proposed adversarial tests and operational assumptions.
- [Runtime assumptions and primary literature](research/se-runtime-assumptions.md):
  ledger checks versus model restrictions, incentives and stronger setups;
  cryptography and noisy-channel future work.
