# Completing the sequential-equilibrium preservation proof

This plan closes the open boxes of the [checklist](se-proof-checklist.md):
S3–S5, E1 and E2. The [handoff](se-handoff.md) describes the fixed theorem,
the semantic decisions and the checked interfaces. Work within a milestone is
checked with targeted `lake --wfail build Module.Name` builds; each milestone
ends with the full warning-strict build and the repository gates. No step
introduces an admission, an axiom or a hypothesis that restates an unproved
compiler fact.

## Target

The final theorem fixes a `SourceServiceSpec`, a parameter readout, a utility
of initial parameters and public outcomes, and the audit backend of R4 (sample,
authenticity, coverage probabilities). For every sequential equilibrium of the
source information model it gives a sequential equilibrium of the bounded raw
runtime whose joint law of initial parameters, public outcome and realized
settlement equals the source law of initial parameters, public outcome and
payoff.

It composes two theorems:

- **S5** (a theorem still to be written): every source
  SE has a sequential equilibrium of the permitted native model with
  `(runBehavioral target).map service.readout =
   (runBehavioral source).map protocolReadout`.
- **R4** `sourceService_audited_raw_equilibrium_extends` (checked), with
  `observe` the parameter/public-outcome readout. Its `RevealService.baseUtility` is by
  definition the S5 utility evaluated on `sourceReadout`, and its invariance
  under raw normalization is `sourceParameterReadout_normalization`.

S5 instantiates
`exists_sequentialEquilibrium_limit_of_local_comparisons`
(`GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean`) with:

| Argument | Supplied by |
|---|---|
| source sequence | `sourceService_consistent_supported_sequence` (as in S2) |
| target sequence | `(TimedApproximant.ofSource ...).assessment` at each stage, with `rosterTiming` at weight ½ |
| target mixing and Bayes consistency | `TimedApproximant.mixed`, `ofSource_bayes` |
| bounded horizon, decision recall, clock | `ResponseMenu.bounded`, `ResponseMenu.decisionRecall`, `roster_menu_common_depth` |
| finite histories | native: `ResponseMenu.finite_history` instance; source: `IsFullyMixed.finite_history` of stage 0 with `Setup.protocol_bounded` |
| initialized laws | `sourceServiceTimedProfile_readout_law` |
| local comparisons | M1–M5 below |

Instantiate the limit theorem's `DecidableEq` instances classically, because
every local-comparison statement uses `open Classical` for `withLaw`.

## Milestones

Sizes: S up to about 150 lines, M up to about 500, L beyond.

### M1. Classification of native decision sites (M)

State one theorem classifying every native information site of the permitted
model into exactly one kind, with the facts each kind needs, all derived from
the information state itself:

1. actorless event (public sampling);
2. foreign visit: the event's actor is another player;
3. owner visit to a binding event, binding recorded in own recall;
4. owner visit to a binding event, binding not yet recorded;
5. owner visit to a disclosure event, opening already sent, or no available
   opening (`rosterOpening? = none`);
6. owner visit to a disclosure event with an available unsent opening.

Kinds 3–6 are decided by the view's service grant and the owner's recall, so
every history of an owner site has the same kind.
`SourceServiceSpec.exists_decisionPhase` supplies the event; the grant and
recall facts come from `SourceServiceSpec.infoOf_decision`.

### M2. Foreign visits (checked)

Foreign sites are discharged by belief-independent continuation equality: no
foreign information law is needed. The gate holds:

> Different legal foreign responses induce the same next-boundary
> configuration law under the actual timed owner policy, although they induce
> different network observations.

Foreign legal responses are transport-only (`foreign_response_transport`).
They preserve the application and the owner's current recall
(`replay_response_preserves`, `respond_recall_other`), so the owner's slot
posterior under `runInteractionPlan_policyMixture` is the same after every
foreign response. Each fixed slot then has an application-only law: a slot the
owner still reaches completes the event with the source lottery
(`binding_slot_config_law`, `reveal_slot_config_law`), and any other slot
leaves only replays (`scheduled_window_waiting`, then
`replay_phase_application_law`). After the owner's submission every remaining
response is transport, and the pending submission alone settles the event
(`recorded_phase_invariant`, `recorded_disclosure_phase_invariant`).

The checked comparisons are `TimedApproximant.foreign_binding_comparison_eq`
([SourceServiceForeignComparison](../Vegas/Game/SourceServiceForeignComparison.lean))
and `TimedApproximant.foreign_disclosure_comparison_eq`
([SourceServiceForeignDisclosure](../Vegas/Game/SourceServiceForeignDisclosure.lean)).
The disclosure case rests on `ResolutionWindowState`
([ReactiveResolutionWindowState](../Vegas/Pending/ReactiveResolutionWindowState.lean)),
the network state at every retained decision of a disclosure phase, supplied
by `SourceServiceSpec.disclosure_decision_resources`. An unavailable opening
needs no separate case: `EffectiveDisclosures`, inherited by the residual
profile through `RevealSource.inherits`, makes the source withhold whenever
the opening would fail.

### M3. Owner-site combinator (M)

Shared by M4 and M5. Fix an owner site. All its histories share one source
view (`SourcePrefixCheckpoint.source_view_eq_of_observe_eq`). The quantifiers
come in this order:

1. choose one admitted source alternative for the whole site, from
   `exists_admitted_local_law` at the common view, before any hidden history;
2. for every history of the site, require both identities: the prescribed
   native continuation equals the prescribed source continuation (the
   normalized profile) at the decoded state, and the alternative native
   continuation equals the continuation of that one alternative;
3. conclude that the native prescribed and alternative laws are the prescribed
   and alternative laws of the same mixture of original source deviations,
   from `sourceService_owner_assessment_comparisons`.

The native belief is the `ofSource` assessment's Bayes belief. Where the
prescribed native law is not the source prescribed law (disclosure), use only
the source side of this result: the mixture components bound source gains.

### M4. Unsent binding (L)

Exact simulation (mixture branch, zero error).

1. From a `DecisionPhase` at an unrecorded binding, derive the premises of
   `sourceServiceTimedPolicy_binding_response_continuation`:
   `sourceService_decision_boundary`, `sourceService_binding_decision_resources`,
   and the roster counts. Restate that theorem over `TimedApproximant`.
2. Every legal owner response is a submission of some value or transport
   (`sourceService_response_supported`). After transport, the conditioned
   value law is the source kernel `q`, because value and timing are independent.
   A local native lottery `λ` therefore yields the source local law
   `v ↦ λ(submit v) + λ(transport) · q(v)`, and the prescribed native lottery
   yields `q`.
3. Apply M3.

### M5. Disclosure owner sites (L, largest)

- **Kind 5:** zero gain by `comparison_eq_of_phase_invariant`. For an absent
  opening use `sourceServiceTimedPolicy_active_reveal_absent`. A sent opening
  is checked: `TimedApproximant.recorded_disclosure_comparison_eq`.
- **Kind 6:** error branch.
  Keep two baselines apart. With `V_true` and `V_false` the continuation
  values after disclosing and withholding at this view, averaged under the
  native belief:

  - source prescribed value `B = q·V_true + (1 − q)·V_false`;
  - native prescribed value `B' = p·V_true + (1 − p)·V_false`, where
    `p = deferredRemaining q timing count`.

  1. Typed continuation after opening now (`openingWindow_active_expiry` for an
     unpassed selected slot; a passed slot gives replay) and after transport,
     each as a source Bernoulli continuation.
  2. Source side: apply M3 with the admitted alternatives "disclose" and
     "withhold" at the common view. This gives `V_true − B` and `V_false − B`
     as expectations of original source deviation gains. The source local law
     at the view is `q`, so `B` is the `q`-mixture of the two values.
  3. Bound every original source deviation gain uniformly by a vanishing error
     with `exists_uniform_policy_gain_bound` (`UniformPolicyLimit.lean`). It
     covers whole-policy deviations at any source site with a fixed fuel, so it
     bounds these mixtures directly; no remaining-fuel conversion is needed.
  4. Native side: the prescribed native law discloses eventually with
     probability `p`, from the timing posterior
     (`sourceServiceTimedMixture_replay_window_posterior_initial`) and
     `scheduledChoice_remaining_probability`. A native local lottery discloses
     eventually with some probability `r` in `[0, 1]`, the same at every
     history of the site, so its value is `r·V_true + (1 − r)·V_false`.
  5. `deferredRemaining_regret_le`, with `rosterTiming_prefix_le` at weight ½
     (remaining mass at least ½), bounds the native gain relative to `B'` by
     twice the bound of step 3.
  6. The limit theorem takes one error for all sites and players: twice the
     sum over players of the step-3 errors. It is nonnegative, so the
     zero-error comparisons of M2, M4 and kind 5 remain valid.

### M6. S5 assembly (M)

Combine M1–M5 into the local-comparison hypothesis for every stage, site and
lottery; apply the limit theorem; state the S5 theorem. This closes S3, S4
and S5 together. S3 accounts for foreign and implementation-only visits by
belief-independent continuation equality (M2), as the checklist records.

### M7. E1 composition (S)

Compose M6 with R4 as described under Target. Check that `rosters`,
`opportunities` (the E1 statement takes `ActorOpportunities`; R4 takes its
`ActorOpportunities.binding` projection) and the deposit agree. Pin the theorem in `Paper.lean`
as a delegating restatement.

### M8. E2 validation and claims (M)

- Full warning-strict build and every repository gate.
- Dependency walk from the final theorem: no draft or test module in its
  closure, standard axioms only.
- Update README, `ARTIFACT.md`, the stack document and the paper sources with
  the exact assumptions: authentic partial audit, positive conditional
  coverage, protected service, collectible fixed deposits, bounded interaction,
  a finite response interface, and no cryptographic or EVM refinement.
- Commit and push after review.

## Ordering

M2 is checked. The critical path is M1 → M3 → M4, M5 → M6 → M7 → M8. Within M5, steps 2–3 and 5–6 do not depend on the
operational steps 1 and 4.

Parallel lanes must not run Lake builds concurrently. A build deletes the
oleans it replaces, so a concurrent check fails on missing imports. A separate
git worktree avoids this, but needs its own Mathlib cache and project build,
which costs several gigabytes on C:.
