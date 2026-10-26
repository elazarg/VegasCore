# Common source semantics and phase-contract migration

The owner chose permanent public exit with commitment-phase retries and
program-declared exit transfers. This document specifies that policy and its
checked migration boundaries. It does not claim that adding payment data
already replaces the existing continuing-source evaluator or proves the full
source/phase decision correspondence. The common result observation and monetary
interpretation can be checked independently of that remaining adapter.

## Chosen operational policy

Use permanent public exit with commitment-phase retry, matching the existing
phase contract's operational behavior:

1. An actual binding omission or failed publication excludes its owner
   permanently. An accepted unusable binding remains latent until publication;
   it does not immediately cause exit. An owner who has exited receives no
   further decisions. Later owned events complete as failures when their
   dependencies become ready.
2. A new miss in a commitment phase voids the current phase's surviving
   bindings. Restore the phase-entry semantic checkpoint and retry surviving
   owners under a fresh attempt namespace. If no owner survives, drain and
   advance. Previously excluded automatic failures do not trigger another
   retry.
3. Other players continue. Public chance and source dependencies retain their
   existing meanings. Failed disclosure and guard checks follow the current
   publication-site ownership rule. Changing guard failure to charge the guard
   subject instead requires a separate source/compiler correspondence.
4. Rollback restores semantic bindings and their live accepted handles, while
   retaining the physical clock, candidate catalogue, exclusion set, network
   history, receipts, and player/environment recall. Retired attempts remain
   visible in the archive and their packets cannot regain validity.
5. A player's information includes retained observations and its own previous
   choices, including those in a retired attempt. No quotient by source Config
   alone is assumed. Actual handle and action transport must be proved.

The existing code implementing the runtime side is
[PhaseApplication](../Vegas/Pending/PhaseApplication.lean), especially
`PhaseRuntimeState.restore`, `PhaseRuntimeState.settle`, the public/player
views and retired-packet rule. These definitions supply the behavior to match;
they are not already a source-language correspondence proof.

## Payments and derived analysis views

Program evaluation determines ordinary transfers. An exit transfer is explicit
source settlement data, rather than a compiler-selected utility. Valuation is
separate analysis data. A constant exit transfer gives constant utility only
under an explicit exit-valuation hypothesis. No rule computes a private
valuation's minimum or cancels arbitrary externalities.

The program declares an integer exit-transfer vector. Upon physical exit, that
player's declared amount replaces its ordinary ret transfer; other players
retain the evaluated program payments. The current absent-readout zero
convention applies to nonexited players and is explicit. Audit deductions are
subsequent monetary effects, not changes to valuation. Existing generic cash
adapters remain valid for arbitrary real-valued amounts and audits.

Derive the intended analysis game by restricting to successful commitments and
openings. Recovery, exclusion and proposal constructions remain labelled proof
devices where required. Each view needs its operational and information
correspondence; defining exit does not prove preservation of every equilibrium
of the full failure game.

## Why the failure choice is substantive

The existing source evaluator records a failed publication and continues to
offer later choices to the same owner. This applies even to value-only
commitment admission: disclosure may still be withheld. The phase contract
permanently excludes that owner and automatically services its later events.
A port must therefore compare the actual legal decision and observation
interfaces, not just the intended successful terminal law.

The retained plain Nash family quantifies over full admitted source policies,
unilateral deviations and actual settlement laws. It cannot be retired on the
strength of an intended-only SE theorem. Any failed correspondence must leave
the affected result available until its disposition is explicitly decided.

## Reviewable migration order

- Share one terminal-observation carrier across asynchronous client laws and
  both phase SE environments, retaining original inputs, complete typed terminal
  state, public result and the whole vector. Prove lossless recoding of the
  existing pair observations.
- Use one quasi-linear cash inversion theorem under supportwise valuation
  factorization, including correlated audit deductions. Keep the original
  utility law alongside the realized monetary law.
- State and check the chosen source failure/retry and settlement rules. Prove
  intended-view, automatic-completion and observation correspondences.
- Port the retained Nash and SE scopes with explicit statement comparisons.
  Retire a parallel contract only after its required ports and concrete
  incentive-bearing instances pass.

The two SE environments keep their distinct sufficient assumptions: conditional
independence and adaptive physical service on the sequential side, correlated
inputs and the reserved tape with complete pending observation on the concurrent
side. The common language and result carrier do not identify those environments.

## Checked implementation surfaces

Setup carries the required integer exit-transfer vector. Its
[cash reader](../Vegas/Source/Settlement.lean) implements the chosen payment
override. [Compiled cash](../Vegas/Compile/EventGraphCash.lean) evaluates the
actual native payoff instructions and agrees pointwise in every execution
mode. [Physical phase cash](../Vegas/Game/PhaseCash.lean) uses the actual excluded
set and participates in the existing audit settlement without changing charges.

The [source phase game](../Vegas/Game/SourcePhaseGame.lean) reuses the existing
source exit/retry protocol and information model. Its utility adds this cash to
independent valuation of the whole source history. Existing automatic completion,
retry closure, recall and termination proofs belong to that same kernel. An
[actual initialized withholding prefix](../Vegas/Examples/SourcePhaseFailureContinuation.lean)
checks exclusion, loss of later strategic choices, declared cash and retention
of a separately supplied valuation.

These surfaces give the chosen policy an actual source game and compiled cash
interpretation. They do not identify the continuing-source analysis game with
it. Existing intended-SE preservation is a different claim from preservation
of every equilibrium of this full source phase game. The complete operational
and information correspondence needed for that further port remains explicit.
The [correspondence status](source-phase-correspondence.md) gives checked
endpoint and source Nash-recoding results and the remaining policy-law work.
