# Sequential equilibrium: proved fragment and next boundary

## Objective

The [monitored guessing theorem](../VegasTests/MonitoredGuessingCompilation.lean)
proves actual source-to-native preservation for the initialized two-reveal game
described below. Source syntax and the compilation tower are unchanged.
General SE preservation for VegasCore remains **open**. The next task is to
identify a larger game class justified by these concrete operational proofs.

The [ideal-sanctions note](research/se-ideal-sanctions.md) gives a general
finite-game extension theorem with a written proof, plus the precise checked
ingredients and remaining Lean assembly. It also tests forcing future actions
to fail: failure must impose a sufficient continuation loss, and excluding a
sender with no remaining source actions cannot undo its influence on others.

The checked fragment fixes the source program, utilities, service and compiled
game **before** choosing an equilibrium:

> For every source sequential equilibrium, there is a sequential equilibrium
> of that fixed native game with the same joint initial-type/public-result law
> and the same net payoff law.

The checked theorem additionally supplies one fixed playerwise policy
translation: Bob's completion depends only on his own source policy, while
Alice's and Watcher's policies are fixed. This translation is noncomputable.
Reflection of every native equilibrium is separate. Matching expected utility
alone is weaker. Choosing new fines or a new target game for each equilibrium
does not meet this target. A game compiler may use the declared utility bounds.

## What is already established

| Question | Checked result | Boundary |
| --- | --- | --- |
| Does monitoring reach the actual native game? | One fixed playerwise translation preserves every SE of the initialized guessing program and its joint initial-bit/public-result/net-payoff law, for fixed `D ≥ 2`. | Full bounded raw menus and the specified 14-command service; one early transmission, one passive monitoring opportunity, collectible charge, costless indifferent watcher; noncomputable policy completion. |
| Can disclosure incentives be controlled at all? | Every SE of the finite private-state sender/terminal-receiver class extends under sufficient disclosure charges, with exact state and net payoff laws. Range bounds fix one game and playerwise compiler for all source SEs. | The charge is specified in utility; this is not yet a native monitor implementation. |
| Can players themselves supply the deterrent? | In that class, statewise constant-sum payoffs require no disclosure charge: an informed receiver's optimal response deters the sender. | No general multistage or multiplayer theorem. |
| Can ordinary pending-message observation detect the native attack? | The actual unsupported certificate is reportable before ledger inclusion; sampling and conditional report-delivery bounds are checked. | Coverage, liability, timely adjudication and collection are not supplied by observation alone. |
| Can every covert signal be detected? | A shared pad permits signaling inside lawful observable support, defeating every alarm with zero false positives. | This is a detection limit, not a claim that every such channel destroys SE. |
| Does a larger fine solve off-path credibility? | The native pilot completes Bob's new information sites with one consistent sequence and proves Alice optimal after every earlier liability. | General continuation completion is open; a sunk fine cannot be counted again as a future cost. |
| Do zero-sum or CE results already close SE? | The paper service preserves zero-sum equilibrium value, including native CCE value. Equal normal-form CE content can coexist with different SE outcomes. | Value is not outcome-law equality; the finite reactive service needs its own bridge. |

The [artifact map](../ARTIFACT.md) identifies the Lean declarations. The
[enforcement design](disclosure-enforcement-design.md) gives the finite theorem
and its exact scope. No result here establishes coalition preservation.

## Monitored native decision game

The proof uses the existing raw response menu, passive foreign observations and
at-most-once inclusion. It evaluates the actual reactive runtime, retaining the
transmissions that monitoring deters.

The [native pilot audit](research/se-native-pilot.md) specifies two source reveals:
Bob opens or withholds a preinstalled `true` commitment to encode his guess;
Alice subsequently opens her hidden bit. Correct guesses pay both players;
failure of Alice's final opening carries a source penalty. Her opening is
proved optimal in every native continuation. The proof establishes this directly,
including arbitrary previous messages and already incurred charges. Native
initialization uses the source setup law through `Vegas.SourceProgram.Setup.eventInputs`
and `Vegas.EventGraphRuntime.State.initial`; it is part of the theorem.

Alice has an extra native response before Bob acts. An ordinary watcher samples
its envelope with probability one half and replays it for inclusion. Every such
Alice packet is rejected before Bob's publication. The additional charge uses
that receipt; legal opening and withholding have unpunished implementations.
Bob sees pending traffic and any included report. The proof supplies optimal
responses at all his information sites and one common consistency sequence.
Every early submission has utility at most `1 − D/2`; silent play gives each
type a nonnegative payoff. These are conditional, whole-policy comparisons.

| Generalization obligation | Concrete acceptance test |
| --- | --- |
| Faithful permitted behavior | Every source choice, including withholding and failure, has an unpunished realization; reconstruct source observations and remaining choices at every admitted decision. |
| Complete treatment of native responses | Include malformed packets, early ordinary openings, evidence forwarding, silence, retries, identifiers and timing. Classify each as source behavior, irrelevant behavior with a proof, or a detectable departure. |
| Conditional deterrence | Bound the gain and additional future net collection at each sender information set and departure. An average monitoring rate is insufficient. Preserve attribution and available collateral. |
| Native sequential equilibrium | Construct optimal continuations after received evidence, not obedience to the source policy after its information assumptions fail. Supply one common fully mixed sequence for all beliefs. |
| Exact result | Prove joint initial-type/result and net payoff-law equality for every source SE in one fixed compiled game. Account for all strategic players and all their native deviations. |

The watcher is a strategic player with zero utility throughout: its
chosen reporting policy can be rational by indifference. This is a deliberately
limited existence target, not a guarantee that every native equilibrium reports
or an economic implementation of paid watchers. Sampling, timely inclusion and
collectible loss remain explicit service assumptions. A deposit also needs a
stated relation to utility. An oracle variant would assume the reporting policy
instead; keep these two claims distinct.

## Broader routes, ordered by the evidence needed

1. **Generalize the native fragment.** Extend to another source decision or a
   genuinely necessary service feature, keeping the extra proof obligations explicit.
   The general first-departure/rare-tremble theorem is useful only if
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
