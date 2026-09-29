# Completing the sequential-equilibrium preservation proof

This plan maps the [checklist](se-proof-checklist.md) boxes S3–S5, E1 and E2
to the proofs that close them. The [handoff](se-handoff.md) describes the fixed theorem,
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

- **S5** `SourceServiceSpec.exists_native_sequentialEquilibrium` (checked): every source
  SE has a sequential equilibrium of the permitted native model with
  `(runBehavioral target).map service.readout =
   (runBehavioral source).map protocolReadout`.
- **R4** `sourceService_audited_raw_equilibrium_extends` (checked), with
  `observe` the typed source readout `sourceReadout`. Its `Vegas.baseUtility`
  is by definition the S5 utility evaluated on `sourceReadout`, and its
  invariance under raw normalization is `sourceReadout_normalization`.

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

### M1. Classification of native decision sites (checked)

`SourceServiceSpec.exists_siteKind`
([SourceServiceSiteKind](../Vegas/Game/SourceServiceSiteKind.lean)) gives
every native information site its recall, view and granted event, together
with a `DecisionSiteKind` computed from those three alone, so every history of
a site has the same kind. The kinds and their comparisons:

| Plan kind | `DecisionSiteKind` | Comparison |
|---|---|---|
| 1. actorless event | `chance` | `sample_comparison_eq` (checked) |
| 2. foreign visit | `foreignBinding`, `foreignDisclosure` | `foreign_binding_comparison_eq`, `foreign_disclosure_comparison_eq` (checked) |
| 3. own binding, recorded | `recordedBinding` | `recorded_comparison_eq` (checked) |
| 4. own binding, unsent | `unsentBinding` | `unsent_binding_comparisons` (checked) |
| 5. own disclosure, sent | `recordedDisclosure` | `recorded_disclosure_comparison_eq` (checked) |
| 5. own disclosure, no opening | `absentOpening` | `absent_opening_comparison_eq` (checked) |
| 6. own disclosure, opening available | `availableOpening` | `available_opening_gain_le` (checked) |

Only coverage is used by M6. The kinds are mutually exclusive by construction:
each is fixed by the event's node, the actor, the recorded bit and
`rosterOpening?`.

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

### M3. Owner-site combinator (checked)

`TimedApproximant.owner_comparisons_of_continuations`
([SourceServiceOwnerComparison](../Vegas/Game/SourceServiceOwnerComparison.lean))
is shared by M4 and M5. It fixes an owner site of the `ofSource` approximant of
a fully supported, Bayes-consistent source assessment, a local native lottery,
and one admitted source alternative chosen for the whole site. Its hypotheses
are the two per-history identities, stated at the source state decoded at the
start of the event's phase (`TimedApproximant.decodedState`):

- the prescribed native continuation is the prescribed source continuation of
  the normalized profile;
- the native continuation under the local lottery is the continuation of the
  normalized profile updated by the alternative.

It concludes that the native prescribed and alternative laws are the
prescribed and alternative laws of one mixture of original source assessment
comparisons, via `sourceService_owner_assessment_comparisons`.
`expect_sub_eq_of_eq_bind` turns this into the mixture branch of the
limit theorem's local comparison.

The caller supplies the alternative, from `exists_admitted_local_law` at the
site's common source view (`SourcePrefixCheckpoint.source_view_eq_of_observe_eq`),
before choosing any hidden history. Where the prescribed native law is not the
prescribed source law (disclosure), the caller cannot establish the first
identity and uses only the source half, `TimedApproximant.owner_source_comparisons`:
the source continuations averaged under the native belief are the laws of one
mixture of original source comparisons, so their gains are mixtures of source
gains.

### M4. Unsent binding (checked)

`TimedApproximant.unsent_binding_comparisons`
([SourceServiceUnsentBinding](../Vegas/Game/SourceServiceUnsentBinding.lean)) is
the exact simulation (mixture branch, zero error). Per decision,
`TimedApproximant.unsent_binding_decision` gives the native continuation of
every legal owner response: a submission fixes its value
(`BindingSource.submission_readout`); a transport response rules out only the
current timing slot, so every remaining slot completes the binding with the
source commitment lottery `q` (`TimedApproximant.unsent_binding_transport_config_law`).
The prescribed native lottery therefore averages to `q`. On the source side,
`SourceServiceSpec.exists_bindingSource_step` unfolds the source continuation
one binding step. It also gives the source step of any owner action, and shows
that the owner's source action law has value marginal `q`. The local native
lottery `λ` is simulated by the source local law that plays the submitted value
after a submission and the prescribed source law after a transport response;
`owner_site_source_histories` supplies the source histories on which
`exists_admitted_local_law` realizes it. M3 then gives the common mixture.

### M5. Disclosure owner sites (checked)

- **Kind 5 (checked):** zero gain by `comparison_eq_of_phase_invariant`. A sent
  opening: `TimedApproximant.recorded_disclosure_comparison_eq`. No available
  opening: `TimedApproximant.absent_opening_comparison_eq`
  ([SourceServiceAbsentOpening](../Vegas/Game/SourceServiceAbsentOpening.lean)).
  Without an authentic opening in view the resolution menu offers no
  submission, and the timed compiler responds only by transport at every point
  of the phase (`sourceServiceTimedPolicy_absent_transport`), so the application
  stays fixed and all traffic published (`transport_phase_application_law`).
- **Kind 6 (checked):** error branch,
  `TimedApproximant.available_opening_gain_le`
  ([SourceServiceAvailableOpening](../Vegas/Game/SourceServiceAvailableOpening.lean)).
  Every local lottery gains at most `error / lower` when every original source
  comparison gains at most `error` and the timing law leaves mass at least
  `lower` after each of the owner's visits but its last. With `V_true` and
  `V_false` the source continuation values after disclosing and withholding,
  averaged under the native belief, and `c` the owner's earlier visits:

  - the source prescribed value is `q·V_true + (1 − q)·V_false`, from the
    boundary unfold of `exists_revealSource_step`;
  - the native prescribed value is `p·V_true + (1 − p)·V_false` with
    `p = deferredRemaining q timing c`, from the timing posterior at the
    decision and `deferredRemaining_hazard_value`;
  - a native lottery has value `r·V_true + (1 − r)·V_false`: the opening
    completes the disclosure (`RevealSource.opening_config_law`), and a
    transport response defers it with `deferredRemaining q timing (c + 1)`
    (`TimedApproximant.available_transport_expect`).

  Both disclosures are legal source choices at the common source view,
  because an authentic opening makes both effective
  (`RevealSource.disclosure_mem_support`, from `SupportsEffectiveChoices`).
  So the source alternatives "disclose" and "withhold" exist
  (`exists_admitted_local_law`), and `owner_source_comparisons` makes
  `V_true − B` and `V_false − B` mixtures of original source gains, where `B`
  is the source prescribed value. `deferredRemaining_regret_le` then bounds the
  native gain. The per-decision laws are the record
  `TimedApproximant.AvailableOpeningLaws` (`available_opening_decision`).

### M6. S5 assembly (checked)

`SourceServiceSpec.exists_native_sequentialEquilibrium`
([SourceServiceEquilibrium](../Vegas/Game/SourceServiceEquilibrium.lean))
combines M1–M5 into the local-comparison hypothesis for every stage, site and
lottery and applies the limit theorem. The comparison error is twice the sum
over players of the uniform source gain bounds of
`exists_uniform_policy_gain_bound`. It is nonnegative, so zero-gain sites use
the error branch and unsent bindings the mixture branch; a disclosure with an
available opening gains at most twice its player's bound, because
`rosterTiming_prefix_le` at weight ½ leaves remaining mass at least ½. Relative
to GameTheory's current finite SE definition, finiteness is no new premise:
finiteness of the source information histories is an explicit instance that
the definition already requires to state the source SE, and finiteness of all
source histories is derived from consistency and the bounded source horizon
(`IsFullyMixed.finite_history` with `Setup.protocol_bounded`). This closes
S3, S4 and S5 together.

### M7. E1 composition (checked)

`SourceServiceSpec.audited_raw_sequentialEquilibrium_preserved`
([SourceServiceCompilation](../Vegas/Game/SourceServiceCompilation.lean))
composes M6 with R4 for one `SourceServiceSpec`. R4 takes its rosters, network,
bounds and `ActorOpportunities.binding` projection; the S5 utility is the
parameter-and-public-outcome utility on `sourceReadout`, so it is R4's
`Vegas.baseUtility`. `Paper.lean` restates it as
`Vegas.Paper.source_audited_raw_sequential_equilibrium` with its axiom pin.

### M8. E2 validation and claims (checked up to the push)

- Full warning-strict build and every repository gate pass.
- The dependency walk from `Vegas.Paper.source_audited_raw_sequential_equilibrium`
  reaches no draft, test, example, experimental or prototype module; its axioms
  are the standard three.
- README, `ARTIFACT.md`, the research map, the stack document (with its
  assumptions table) and the paper (Theorem `thm:sequential`) state the exact
  assumptions: authentic partial audit, positive conditional coverage,
  protected service, collectible fixed deposits, bounded interaction, a finite
  response interface, and no cryptographic or EVM refinement.
- What remains is to push after review.

## Ordering

M1–M8 are checked; what remains is the push after review.

Parallel lanes must not run Lake builds concurrently. A build deletes the
oleans it replaces, so a concurrent check fails on missing imports. A separate
git worktree avoids this, but needs its own Mathlib cache and project build,
which costs several gigabytes on C:.
