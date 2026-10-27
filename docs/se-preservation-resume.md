# Resuming concurrent sequential-equilibrium preservation

This is the entry point for continuing the partially observed concurrent-runtime
research. The objective is still a simple commit–reveal language implemented on
an idealized but credible blockchain. Rollback, fixed windows and audit design
are means to that objective. They are not the specification to preserve.

**There is no checked end-to-end theorem for the proposed broadcast runtime.**
There is also no impossibility result for the current concurrent compiler with
complete pending observation removed, or for all services with correlated
delays. A failed proof transfer is not such a counterexample.

## What is established, and what remains a proposal

| Artifact | Status and scope |
|---|---|
| Existing sequential preservation results | Mechanized under their stated service, information and settlement hypotheses. See the [checked-result index](../README.md) and [runtime refinements](se-runtime-refinements.md). These hypotheses still matter. |
| Existing concurrent preservation result | Mechanized with complete pending observation and the reserved service. It does not supply preservation for a partially observed mempool. |
| [Direct-ledger-audit derivation](se-broadcast-preservation-derivation.md) | Detailed finite hand construction, with substantial service and observation assumptions. Its concrete runtime, compiler adapters and end-to-end proof are not implemented. |
| [Runtime design](se-runtime-design.md) | Reuse and implementation plan, including known information, copy and clock risks. It is not an implemented runtime. |
| [Paper proposition](../Paper.lean) and [generic result carrier](../Vegas/Game/SourceGameImplementation.lean) | Define the desired preservation conclusion without asserting it. They impose no operational constraints. Under finite source histories, the source game itself can witness this generic conclusion; it is not yet a broadcast target. There is no admitted broadcast theorem. |
| [Experiment ledger](se-preservation-experiments.md) and [constructive ledger](se-preservation-constructive-experiments.md) | Checked local results, accepted reuse and concrete counterexamples, with their individual scopes. They do not close the concurrent runtime gap. |

The intended quantifiers fix the source setup and backend laws, then choose a
compiler/implementation and its parameters **before selecting a source SE**.
Every source SE must have an implementation SE preserving the joint law of
initial data, typed/public outcomes and realized net payoffs, with no exclusions
or charges on its supported paths. The implementation must be derived from the
specified execution engine and contract, not an arbitrary game with readers.

Nothing in this checkpoint changes the [fixed checklist](se-async-checklist.md),
its boxes, the manuscript or the owner's decisions. The recommendation for the
paper is to use the checked sequential results and treat the proposed partially
observed concurrent construction as future work. Removing or revising the
manuscript's concurrent subsection is a separate editorial decision. The
[open paper-audit items](paper-audit-open-items.md) are a separate task as well.

## Read these first

1. [Asynchronous preservation](se-asynchronous-preservation.md): the actual
   objective, contract control and backend boundary.
2. [Direct-ledger-audit derivation](se-broadcast-preservation-derivation.md): the
   primary mathematical assembly and order of quantifiers.
3. [Broadcast runtime mathematics](se-broadcast-runtime-mathematics.md): the
   finite message model, service, observations, settlement and raw deviations.
4. [Runtime design](se-runtime-design.md): the shared engine and two concrete
   controllers; where reuse stops and proof obligations begin.
5. [Mechanization inventory](se-asynchronous-mechanization-inventory.md): existing
   declarations and missing operational adapters.
6. [Fresh-service alternative](se-asynchronous-support-weakening.md): the timing
   and reset argument used by the primary derivation.

The [support-based theorem](se-asynchronous-preservation-theorem.md) is a
different timing route, with separate delayed-support and reporting hypotheses.
The [strategic-reporting](se-strategic-reporting-mathematics.md) and
[evidence-summary](se-evidence-summary-mathematics.md) notes are tools for broader
message models, not prerequisites of the primary all-recording construction.
Do not combine the hypotheses of these routes implicitly.

## Assumptions that carry the primary argument

* The source has finite histories: finite initial and reachable sample support,
  finite strategic domains, and finitely many players. Initial private values
  may be correlated.
* Commitments and authentication are ideal. Messages have a bounded, typed,
  nonnested grammar. There is one broadcast/submission operation; showing the
  same authenticated bytes without creating a submission job is not another
  available action.
* Every authenticated current-session body within the raw traffic bound has
  immutable, eventually public recording, even if its inner game call is stale,
  malformed or rejected. There is one fresh publication job per body. The two
  available full construction routes assume independence between distinct
  bodies' service. A delay bound alone does not imply this independence.
* Actual partial observations satisfy source factorization, freshness and reset
  conditions. Unlabeled counts, metadata and service-state signals do not become
  admissible merely because they are content-blind. Their conditional laws must
  satisfy the same obligations.
* Capacity and funding cover every deviation within each author's finite raw
  traffic allowance, including post-exclusion traffic. This is a bounded-load
  premise, not a solution to arbitrary flooding or shared congestion.
* The contract controls windows, readiness barriers, exclusion, rollback and
  final audit. The backend controls publication and reception. A compiler
  cannot manufacture the backend guarantees by inserting delay instructions.

The direct audit needs no trusted monitor: evidence is in the ledger by the
final audit. Its availability premise is therefore the all-recording service,
not a claim that permissionless reporting alone ensures evidence delivery.
Separately funded publication and the retained deposit must be accounted for in
the net-payoff law; a gas or nonce model is not silently covered.

## Obstacles and the scope of their conclusions

| Issue | What the arguments establish | Where to resume |
|---|---|---|
| Complete pending visibility | It supports archive reconstruction and deterministic replay in the existing proof. Removing it breaks that proof, not necessarily preservation. | [Private-mempool research](se-private-mempool-research.md) |
| Forgetting observations | A rich-information SE need not descend to a coarser game, even if its limiting strategy is legal there. A common consistent perturbation sequence needs the actual information constraints. | [Coarsening mathematics](se-private-mempool-mathematics.md) |
| Delays and late sends | Padding can drain submissions made before a cutoff only under the appropriate publication guarantee. It does not prevent new post-failure disclosures. Late sends must remain legal deviations. | [Proof routes](se-private-mempool-proof-routes.md), [post-exit deterrence](se-post-exit-deterrence.md) |
| Public sender order and forced flushing | A restricted benchmark is available, but its public schedule/full processing cannot be assumed for the desired mempool. It is not the target backend. | [Scheduled-service benchmark](se-publication-scheduled-benchmark.md) |
| Failure semantics | Global abort simplifies continuation information but is not shown necessary. Forced exit and rollback remain viable design candidates. Source-level quit-handler floors do not by themselves solve runtime information. | [Quit handlers](se-quit-handler-preservation.md), [abort construction](se-private-mempool-compilation.md) |
| Refunds and payoff floors | Refunding can make failure profitable; deterrence needs the appropriate base/net payoff and reserve inequalities. The Odd–Evens budget example is not a universal settlement theorem. | [Compilation and budget analysis](se-private-mempool-compilation.md), [post-exit deterrence](se-post-exit-deterrence.md) |
| Evidence availability | Public verification does not ensure someone retains, forwards and publishes evidence. Monitor availability and strategic reporting are different hypotheses. | [Audit feasibility](se-asynchronous-audit-feasibility.md), [monitored lanes](se-asynchronous-lanes-and-audit-service.md) |
| Independent service | Required by both current full construction routes; not proved necessary for preservation. Correlated outages and shared congestion require new arguments. | [Support weakening](se-asynchronous-support-weakening.md), [timing policy](se-asynchronous-timing-policy.md) |
| Announcing signed bytes without submission | The primary audit no longer sees every forbidden disclosure. Neither the reporting tools nor the direct-audit proof automatically cover this extension. | [Broadcast runtime mathematics](se-broadcast-runtime-mathematics.md) |
| Copies and retries | A second copy must not buy a fresh inclusion draw, cause premature execution through another sender, or retry a rejected body. Canonical-envelope provenance needs proof. | [Runtime design](se-runtime-design.md) |
| Within-slot activations | Reusing one-envelope responses may suffice, but the information, raw-budget and order comparison remains unproved. Randomizing order alone is not a proof. | [Runtime design](se-runtime-design.md) |
| Phase readiness | Completing an event can timestamp the next phase early. Delaying normalization alone does not implement fixed public windows; gate readiness at phase installation. | [Runtime design](se-runtime-design.md) |
| Conditional errors | Small unconditional error need not be small at a rare information set. Bounds and free-site completion must use actual information and a single consistency witness. | [Private-mempool mathematics](se-private-mempool-mathematics.md) |
| Late-leak impossibility | Checked negative results have particular game, service and quantifier scopes. They do not rule out every compiler or every correlated backend. | [Runtime refinements](se-runtime-refinements.md), [fixed checklist](se-async-checklist.md) |

A useful partial idea for correlated service is a shared sequence of processing
epochs with a maximum gap and monotone ingress. If earlier submission cannot
lose eligibility or another player's reserved capacity, its first eligible
epoch is no later than that of a later submission, pathwise, even when all
players share the epochs. This proves an own-packet timing comparison. The
candidate also processes all eligible packets within its reserved raw budget;
it does not solve the desired realistic partial-service problem or supply the
common-assessment/reset argument. Preserve that distinction when revisiting it.

The broader [research survey](se-preservation-research-survey.md) covers
Multitubes, UniformEquilibrium, GameTheory reuse, stopped potentials, power
certificates and related literature. The [correlated-prior note](se-correlated-prior-research.md)
concerns a different independence question: private source data, not service
delays. Do not conflate them.

## Suggested restart sequence

1. Decide the paper scope separately. Recheck the open paper-audit items against
   the manuscript and exact Lean statements; do not remove or weaken a theorem
   merely to make the research branch look complete.
2. Settle the service question on paper before building a general runtime.
   Specify one shared-delay or shared-builder model, its actual observations,
   finite capacity and raw actions. Try conditional policy transport and reset
   under that model. If seeking a counterexample, fix a source SE and rule out
   every implementation SE with the required joint law; an unsuccessful prompt
   strategy or comparator is insufficient.
3. Mechanize one tiny operational instance using the existing execution engine:
   two players and one commit–reveal block, with actual reception, late sends,
   copies, rejected recording and settlement. Derive its finite game and readers
   from execution. Check preservation at off-path information sets as well as
   the honest run.
4. Add a subsequent commitment decision after failure/reset. A single block
   cannot test the hardest memory issue; retaining multiple active players after
   exclusion may require a third player. Include old pending bodies and a fresh
   attempt. Make these examples consumers of the same concrete definitions.
5. Only then extract common operations and generalize. Keep the existing
   sequential controller as a regression consumer. Separate supplied network
   laws, chosen contract parameters and raw resource bounds. Reuse the network's
   pending-or-published invariant, scheduler private memory, service-plan clock
   and ledger recording of rejected calls. Do not build a general contract
   language, a new engine or an EVM key/funding validator to state this theorem.

The missing work is operational definition and proof, not merely replacing an
admission. The generic proposition is deliberately unasserted. A concrete
theorem must expose its service/observation hypotheses and derive the target
protocol, information, audit and readout from the implementation.

## Recovering the working material

The branch is `formalize/broadcast-se-preservation`; the saved research
checkpoint is tagged `research/se-preservation-2026-10-27`. Use a separate
checkout when other work is active. The public repository contains the
maintained mathematics, bibliography pointers, design and checked code.

Private correspondence, scratch arguments, work logs and local verification
harnesses are intentionally outside Git. The local research archive has a
`se-preservation-2026-10-27` directory containing restoration instructions, a
hashed source ZIP and verified Git bundles for VegasCore, GameTheory and the
separate private Overleaf repository. The ignored checkpoint pointer in
`ephemeral/` identifies its absolute location. The manifest records exact Git
revisions, archived files and omissions. This backup is local, not remotely
replicated; the public guide and checkpoint tag are pushed to GitHub.

Restore the private ZIP to a scratch directory first, never over active work.
It includes alternative and superseded drafts; the reading order above identifies
the maintained route. Treat archived scripts as source to inspect, not commands
to execute indiscriminately. Generated Lean caches are omitted: use the pinned
toolchain, manifests and submodule revision to rebuild. The isolated
`check-source-preservation.py` harness is the relevant local check for the
generic carrier, aggregator and Paper file; the older broadcast-admission
harness targets obsolete declarations.

Run the [repository checks](../README.md#build-and-validate) when changing code.
The checkpoint's documentation checks are not a new proof of the construction
and do not substitute for a full build. Keep the [checklist methodology](se-async-checklist.md#methodology):
only checked theorems close its obligations.
