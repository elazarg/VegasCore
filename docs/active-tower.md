# Active compilation tower

This is the current proof boundary. Each layer is game-bearing when it has
players, observations, or policies; the layers below it do not acquire
strategic meaning merely by being executable. A later runtime can add detail by
introducing a new edge and proving its own correspondence laws.

| Layer | Owner | Active artifact | What is proved now |
| --- | --- | --- | --- |
| Probability and game forms | `GameTheory` | `FinDist`, `GameForm`, profiles | The pinned library's probability and equilibrium definitions. |
| Runtime-independent transport | `GameTheoryExtensions` | `MixtureSimulationOn`, `UtilitySimulation`, selective-stopping bounds | Exact observation-law simulation transports arbitrary observation utilities. Utility-specific deviation bounds compose and imply same-error Nash/ε-Nash equivalence at compiled profiles. Selective-stopping bounds require a continuation comparison at the information used to stop. |
| Vegas semantic substrate | `Vegas.Foundation` | typed environments, visibility, values, obligations | Type/visibility and finite-domain infrastructure. No strategic preservation claim. |
| Checked source | `Vegas.Core` | `VegasCore`, `WFProgram`, `SourceBehavioralPolicy`, `sourceGameForm` | Intrinsically typed sequential source syntax; guarded source policies; written-order source execution and payoff evaluation. Nullable `yield` supplies an explicit `Option.none` value. |
| Graph compilation | `Vegas.Compile`, `Vegas.Game.SourceGraph` | canonical graph, declared-read policy runner, `WFProgram.sourceGraphSimulation` | Typed source compilation; exact whole-program terminal-environment law; uniform single-policy backtranslation of every unilateral declared-read graph deviation, with opponents unchanged. A concrete certificate proves Nash and same-error ε-Nash equivalence at compiled profiles for all checked core programs and finite player sets. |
| Graph strategic presentation | `Vegas.EventGraph.Strategic` | behavioral frontier game and canonical declared-read policy game | Under `CommitInformationLocal` and one ready commitment per player, compiled canonical policies preserve the complete observed outcome law of every behavioral profile; every unilateral canonical replacement is exactly one behavioral graph deviation. This is an event-graph theorem, not yet a source-language or message-runtime theorem. |
| Sealed native protocol | `Interaction` | message pool, ideal commitment service, `SealedProgram`, policy runner | Commit and reveal are separate protocol actions. A compiled source site is its registration slot and has the canonical handle `(owner, node)`: the first private registration fixes its only stored value, and an unregistered handle is rejected. Arbitrary finite native traffic—including malformed payloads, retries/replay, delivery, inclusion, and withholding—either stutters or takes a valid graph step. The environment sees the full pending pool; player views expose their own inbox/sent messages and the public ledger. Hiding is proved for protected pre-disclosure traffic. |
| Resolving native protocol | `Interaction` | `SealedResolution`, shared policy-runner rounds | Per-node relative deadlines, nullable resolution, and continuing execution are implemented. Before the first timeout, validator/event projection is exact. Private bindings persist under arbitrary policies and resolution. Every round advances the clock once. Termination is checked without service; periodic inclusion capacity provides deadline-relative service. For the admitted Vegas fragment, completed public settlement has a legal source realization even after defaults. The single-checkpoint `SealedTimeout` model instead records final failure and does not implement this continuation. |
| Vegas compiler edge | `Vegas.Compile` | `SealedCompilation`, sealed decode/refinement/source modules | One sealed rule per graph node; native prefixes decode to reachable graph states; terminal prefixes reconstruct a written-order source run. Under roster coverage, periodic inclusion capacity, a sufficient window, and a whole-period termination budget, all-compiled play has the exact original written-source outcome law in the actual stopped pending-message driver. |
| Pending-message strategic edge | `Vegas.Game` | `SealedCompilation.RoundModel` | Constructed source/native coupling, actual timeout-checkpoint information, retained focal registrations, and same-error Nash equivalence under timely service, normal utility agreement, and explicit conditional timeout utility comparisons. For payout-valued utilities, a source-only `VegasCore.QuitPayoutBound` supplies both utility premises. |

The ideal commitment service provides more than an abstract hiding-and-binding
interface. For the compiled protocol, a source site is the numeric slot itself,
so there is one canonical owner/slot handle. Its first authenticated private
registration is permanent, and commitment validation requires that registration
to exist. Thus this registered-site host neither admits multiple competing candidates at
one source site nor accepts a candidate that may later prove unopenable. A
lower-level commitment protocol with either behavior needs a strategic
refinement to this functionality; a codec or representation theorem alone is
insufficient.

The same sealed rules and shared message runner also have a candidate-service
instantiation, `SealedResolution.candidateApplication`. Source-site, candidate,
and message identities are distinct. A player may prepare several candidates;
the first eligible acceptance selects the site's handle. An unprepared handle
is accepted as permanently unopenable, and failed opening attempts leave
deadline resolution responsible for the programmed default.

`runPolicies_candidate_lookup_of_not_fresh` proves immutable candidate meaning
under arbitrary player and environment policies. The source settlement APIs
use only public event provenance and public timeout safety; they have no private
service parameter. `SealedCompilation.candidate_publicPayout_source` therefore
supplies a legal written-source payout witness for every completed candidate
policy run. `candidate_publicPayout_source_choice` supplies one witness recording
the timeout owner's source default and matching the actual payout. Neither
theorem fixes the opponents' source policies. Completion is an explicit premise;
candidate-host termination and causal deviation coupling are not
inferred from these safety results. The Nash theorem below still uses the
registered-site service.

`SealedCompilation.candidatePolicies_law` separately proves exact equality of
the two hosts' complete finite execution laws for the generated source policies.
The embedding retains the public pool, receipts, clock, timeouts, local histories,
and native trace; it represents registered values as openable candidates. The
compiler proves that every commitment it submits was privately prepared, and
the pool preserves this fact through delivery, replay, and inclusion. No
fairness or timeout-free premise is needed for this host equality. Retyping
environment policies is surjective, so it excludes no adaptive candidate-host
environment. The equality does not cover arbitrary candidate-player deviations.
Both hosts instantiate `MessageApplication.RoundDriver`, whose single bounded
loop stops at completion. `candidateRounds_law` transports the full honest
execution law through this stopping rule. Under roster coverage, periodic
inclusion capacity, a sufficient window, and a whole-period termination budget,
`candidate_honest_round_payout_law` proves that the actual candidate driver
completes without timeouts and has exactly the written source payout law.
The payout is reconstructed from public initial fields and opening events.
This honest law has no incentive hypothesis and does not establish candidate-host
Nash preservation.

`SealedFragment.candidateAcceptanceLaw_read_bound` proves a causal information
bound for this host. With fixed assigned honest choices, an arbitrary randomized
focal policy and full-pool environment have the same joint law of focal history,
view, and owner-scoped candidate catalog through first acceptance or timeout
when honest values agree on source-earlier disclosures. The cut permits multiple
preparations and competing candidates; it does not stop at private preparation.
The catalog is proof-facing data, not an extra player observation.
`extractedCandidateSourcePolicy` uses this bound to construct a legal
written-source replacement from fixed native response functions, shared across
all source decisions. It selects the accepted candidate's opening, not the
first preparation. Absent or unopenable selections use a legal fallback;
an openable source null value remains distinct from those cases. The actual
selected meaning is nonfresh and persists through the rest of the native trace.
`extractedCandidateSourceRun_consistent` proves that every supported complete
source realization agrees with these replay selections, with unchanged
opponent policies and no assumed source-input equality. The exact joint
prefix law through first timeout is proved below for fixed native response
functions. Candidate-host stopped-round coupling and the incentive bound for
fallback runs remain open.

Generated policies satisfy `candidatePolicy_memory` under arbitrary opponent
and environment policies: each honest owner's command cache agrees with its
candidate catalog, including across delayed delivery, replay, and timeouts.
Before timeout, `runPolicies_candidate_openings` ties every successful opening
to its actual accepted handle and immutable value; acceptance alone need not
imply openability. Shared event-value read reconstruction lets
`candidate_registration_kernel` identify the local fresh-slot draw from
event-value agreement. `extractedCandidateSourceRun_accepted` discharges that
agreement at every checkpoint of the pre-timeout replay. The public log selects
one authenticated handle per source site; its acceptance-time meaning equals
its meaning at the common timeout checkpoint. Focal values therefore agree
with the extracted source choice, while generated honest submissions retain
their source-site identity and assigned values through delivery and replay.
`extractedCandidateSourceRun_registration_kernel` consequently identifies each
fresh honest draw with the original source kernel at the complete source
realization's declared inputs. No cache, accepted-value, or read-environment
agreement premise remains. This local kernel theorem supplies the
original-probability comparison used in the joint native prefix law.

`candidateReplay_prefix_eq_iff` characterizes a complete replay prefix by its
recorded honest preparations, retaining pending traffic, competing candidates,
and unopenable acceptances. `candidateReplay_cylinder_probability` computes
its mass under any correlated assignment law. On the written-source side,
`extractedCandidateSourceRun_replay_likelihood` expresses that prefix's mass
as the expected original-choice likelihood under a normalized reference source
execution. `restrictedCandidateSourceRun_replay_prefix` proves that every
reference realization reproduces the prefix, including when the original
profile assigns it probability zero. Both hosts use the same
`recordedChoiceRestriction` and source event/probability calculation.
`restrictedCandidateSourceRun_registration_probability` identifies the original
source decision probabilities throughout that reference law with native
preparation probabilities. The checkpoint is a pre-timeout replay snapshot at
which the policy supports that preparation, as proved by the shared
`MessageApplication.commandCheckpoint_selected_of_new_fact` and candidate opening
provenance. It need not be the snapshot of the actual preparation invocation.
`extractedCandidateSourceRun_replay_prob_eq_product`
then evaluates the source cylinder mass as a product of these fixed native
preparation factors. Both hosts use the same source-product calculation.
`candidateReplay_registration_factor` proves that each actual honest preparation
invocation has its checkpoint's probability, using their shared source occurrence
and declared reads. `CommitmentCandidates.preparationWeight` counts openable
tracked handles; acceptance of an unprepared handle leaves this product unchanged.
The generic single-coordinate product calculation is shared with registered
commitments. `candidateReplay_prefix_prob_eq_product` derives native trace mass
from the shared message-runner likelihood theorem, including zero-probability
prefixes. `extractedCandidateSourceRun_native_prefix_law`, audited as
`pending_candidate_source_native_prefix_law` in `Paper.lean`, identifies the
complete native prefix law through first timeout with the extracted source run's
replay law. The original opponents' policies remain unchanged. Focal and
environment responses are arbitrary fixed functions; invocation schedules are
arbitrary finite lists. No service premise is needed for this prefix result.

`extractedCandidateSourceCoupling` attaches the actual native continuation to
that prefix using the shared `MessageApplication.couplePrefix` construction.
It preserves the source realization and the joint prefix/full-trace law,
including all post-timeout behavior. The continuation reads the retained native
histories, not the source realization. On supported timeout-free completed pairs,
`extractedCandidateSourceCoupling_public_store` proves agreement on every typed
public field with that exact source realization; the payout agreement follows
without a private-service decoder or a separately chosen settlement witness.

`exists_randomized_candidate_source_coupling`, audited as
`pending_candidate_randomized_source_coupling` in `Paper.lean`, predraws arbitrary
focal and environment policies through the shared joint-response theorem. Its
finite response-pair mixture is fixed ex ante and may be correlated. The resulting
coupling has the actual complete native trace law, a source marginal that is a
finite mixture of legal focal replacements with unchanged opponents, and
pointwise public payout agreement on normal completion. This is a finite-schedule
coupling theorem, not a completed-game payoff bound after timeout.

The remaining candidate steps are stopped-round coupling, arbitrary-deviation
round completion, exclusion of a first honest timeout under deadline-relative
service, and the source-only utility comparison. The honest completion theorem
does not supply these arbitrary-deviation progress guarantees.

## End-to-end target

The immediate unproved result is **source-to-candidate-message equilibrium
preservation**, not a collection of intermediate theorem names. It must concern
the actual `candidateApplication` and the generated `compileCandidatePolicy`,
with arbitrary native unilateral policies. Candidate binding and completed
settlement correspondence alone do not establish it.

Fix a checked source with an admitted `SealedCompilation`, its initial
environment, configured default, and payout valuation. Keep the current
fragment explicit: homogeneous values, universally accepting guards, no
sampling, and no initially private binding requiring publication. Fix a finite
player set and a round driver with roster coverage, sufficient timeout windows
and termination budget, and deadline-relative timely service for unchanged
players. The environment may adapt its unreserved wire actions to its actual
view, including the pending pool, but has no private candidate-table access.
Candidate ownership and immutable accepted meaning are properties of this ideal
host, not cryptographic conclusions.

Write `S` for the written-source game, `R` for that candidate-message round game,
`C` for the pointwise generated policy translation, and `pS` and `pR` for the
source payout and actual public runtime payout. The intended result has two laws:

1. **Honest execution (proved):** every compiled profile completes without timeout and
   `Law(pR; R(C σ)) = Law(pS; S(σ))`.
2. **Arbitrary deviations (unproved):** assuming the source-only `QuitPayoutBound`, for
   every source profile `σ`, player `i`, and randomized native replacement `τi`,
   there is a finite mixture `μ` of legal source replacements such that
   `E[uᵢ(pR); R((C σ)[i := τi])] ≤ E[sᵢ ∼ μ] E[uᵢ(pS); S(σ[i := sᵢ])]`.
   All other players retain their original source policies in every mixture
   component. No runtime incentive comparison or desired simulation is supplied
   as a premise.

These laws give Nash and same-error ε-Nash preservation and reflection at
compiled profiles. The inequality, rather than exact deviation-outcome equality,
allows selective withholding subject to the stated source settlement condition.
`QuitPayoutBound` requires each player's designated quitting settlement to be a
global minimum over legal source executions; it is stronger than ordinary
ex-ante quit dominance. The proof must derive completion, acceptance-time source
decisions, and the unchanged-opponents law from the actual driver and compiler.
Its concrete composition certificate and paper audit should delegate to those
proved laws, not accept them as caller obligations.

The registered-site host already has the source-payout strategic result. The
candidate host has immutable accepted meaning, completed public settlement
witnesses, and the original source payout law for honest stopped-round execution.
Its randomized full-trace coupling and pointwise normal payout agreement are
also proved. The completed-round deviation utility bound is the next proof task.
More general source
continuation criteria, guarded choices, sampling, heterogeneous values, and
cryptographic or ledger refinement are further scope requirements; their exact additional assumptions must be
determined, not represented by guessed theorem signatures. An obstruction must
be stated against a specific model and guarantee.

`paper-claims.json` is a manuscript coverage inventory, not this proof plan.
Unverified entries keep unsupported prose visible without prescribing a proof
architecture or restoring inactive interfaces. Reference code is only reading
material and contributes nothing to the audit. The paper's broader scope remains
the goal; the candidate-message theorem is the next concrete milestone.

## Pending-message strategic boundary

`SealedCompilation.compilePolicy` implements a written-source policy in the
native principal-scoped interface. Local reconstruction reads only initial
source-visible inputs, public application events, and the owner's registration
history. The checked registration-memory invariant holds under arbitrary
opponent and environment policies. Fresh registrations use exactly the
declared-read source kernel; occupied slots publish an opaque handle without
resampling. Every emitted opening already satisfies the public publication
barrier, and no compiled-policy packet is a cleartext commitment.

The whole-program honest law is
`SealedCompilation.exists_honest_round_source_coupling`: original source
denotation, actual stopped native marginal, normal completion, and pointwise
source decoding under the service conditions above. Unilateral native
deviations have the checked source/native coupling described below. This gives
a finite mixture of legal source deviations, not exact source/native outcome
equality after timeout. General utilities use the checked timeout-checkpoint
comparison; payout utilities can discharge it entirely from the source-only
`QuitPayoutBound` described below.

`SealedFragment.replay` evaluates the shared native runner with assigned honest
values and fixed deterministic deviator/environment policies. Its checked
`replay_eq_iff` characterizes each full execution by exactly the honest
registration coordinates it records. This holds for every finite invocation
schedule and thus for every invocation prefix. It concerns proof-facing records,
including private commands; it does not expose those records to players. The
support-transfer and registration-origin lemmas also allow randomized native
deviator and environment policies. The knowledge-indexed native relation
preserves public observations, pool operations, and validation receipts while
allowing unknown registered values to differ. The compiled-policy comparison
and submission barrier supply its local policy premises.

`SealedFragment.resolvingBindingLaw_read_bound` proves a whole-prefix
registration read bound in the continuing deadline runtime. Substitute complete
assignments for honest source draws, leaving the focal native policy and the
full-pool environment arbitrary and randomized. If the assignments agree at
honest handles disclosed before the focal source decision, the law of that
decision's first registration is equal, cut off at the first timeout or finite
horizon. This includes private history, clock, readiness, pending traffic, and
rejection-receipt effects in the lockstep argument. It does not assume fair
service. The conditional binding invariant holds on every native policy prefix;
the compiled command premises are derived from it, not supplied by a caller.
The cutoff reads the first timeout snapshot after its tick, which preserves
the private service. Absence of registration is separate from registration
of the nullable source value.

`SealedFragment.resolvingAcceptanceLaw_read_bound` extends the information bound
through public commitment acceptance, first timeout, or the finite horizon.
It equates the focal player's entire local history and current view, including
interaction after private registration. The local publication proof uses only
the public prerequisite log: future honest openings cannot be submitted while
the focal commitment remains incomplete. Private-value immutability is a
separate property of the service. Both read bounds use the same native command
coupling, and neither requires fair service. This strengthens the information
boundary of the current functionality; it does not yet admit competing or
unopenable candidates.

The theorem supplies the causal read bound for assigned-value replay.
`SealedFragment.resolvingReplay` fixes native deviator/environment responses
and selects the unique trace of that same runner. `SealedCompilation.extractedSourcePolicy`
uses one such pair of responses at all source decisions. Its inputs are actual
declared-read source fields: the compiler proves that every earlier public
graph output retains a public source binding. Recompilation recovers the
extracted graph policy, and `extractedSourcePolicy_law` identifies its local
action law with the replay registration when disclosure inputs agree.
Absent registrations use an explicit legal fallback, which is separate from
both registered nullable values and timeout settlement.

`SealedCompilation.extractedSourceRun` is the canonical graph realization of
written-source play under this policy and the original opponents.
`extractedSourceRun_source` identifies its complete source-environment law
with that independent source denotation. In every supported terminal
realization, `extractedSourceRun_consistent` proves all focal choices equal
the values extracted by replay of its honest assignment; disclosure-input
agreement is derived from actual source reads and reveal semantics.
`extractedSourceRun_locked` retains every focal source-owned registration
present at the common first-timeout snapshot, including speculative ones.
This concerns private bindings: the snapshot follows its timeout tick, so
its newly defaulted public fields need not match those source values.
`extractedSourceRun_registered` extends that agreement to every player's
source-owned registrations. Honest slots retain assigned values; native
registration provenance rules out private entries introduced by traffic or
timeout defaults. `extractedSourceRun_opened` proves that every included
opening at a selected pre-timeout replay checkpoint has its complete source
value, including when a later part of the same run times out.

`sealedPlayerStore_source_reads` transports every successful local read to
the complete source realization under binding, registration-agreement, and
own-cache/service agreement premises. `commitCommand_source_kernel` then
identifies the fresh registration kernel at those source inputs.
`SealedResolution.RegistrationMemory.runPolicies` proves own-cache/service
agreement under arbitrary resolving-runtime policies, including post-timeout
execution. The event/history projection preserves that cache.
`extractedSourceRun_registration_kernel` applies these facts at every selected
pre-timeout replay checkpoint: an actual fresh honest registration identifies
its source node and successful declared reads, proves the private slot empty,
and identifies a compiled source policy's law with its kernel at the complete
source realization's inputs. The compared policy need not generate that
realization. No cache correctness or read-availability premise is left to the caller.

`assignmentRealization` realizes every honest assignment using legal deterministic
source policies and the same extracted focal policy. Its honest commitment values
are the assigned values, and replay of its node values is exactly replay of the
original assignment, including post-timeout snapshots. This is a choice of a
supported result of the existing source execution, not an additional evaluator.
`assignmentRealization_registration_kernel` therefore covers every assignment,
including assignments having zero mass under the compared source policy. Its
audit is `Vegas.Paper.pending_honest_registration_kernel`; the zero-probability
regression distinguishes realization from support under the compared policy.

`SealedFragment.resolvingReplay_prefix_eq_iff` characterizes stopped resolving
replays by their recorded honest registrations, including when the cutoff
discards a suffix whose honest values differ. The cutoff may inspect the full
proof-facing snapshot; it does not change player observations.
`resolvingReplay_cylinder_probability` identifies the probability of each
stopped trace with its honest-registration cylinder mass under any joint
assignment law. Independence of those coordinates is not assumed. This is
a replay law, not yet the marginal law of the original honest kernels.

`Vegas.denoteSource_prob_eq_prod` factors the probability of every written-source
terminal environment into its actual conditional draw probabilities and a final
environment-consistency check. It includes samples, guards, and dependent
choices, even for queried environments of probability zero.
`MessageApplication.tracePolicies_prefixThrough_prob_eq_prod` factors the actual
stopped-native trace law into invocation probabilities and snapshot-consistency
checks. The original runner continues; the discarded suffix integrates to one.
`invoke_player_prob_of_step` identifies a player invocation's factor with its
chosen command's probability, including rejected or state-preserving commands.
The paper audits these laws as `source_point_probability` and `native_prefix_probability`.

`SourceChoiceRestriction` fixes selected legal source choices and leaves all
other kernels unchanged in a normalized reference execution. The checked
`denoteSource_restriction_probability` computes the original event probability
as an expectation of the original forced-choice likelihoods under this
reference law. The constant-likelihood corollary performs the source cylinder
summation, including zero-mass cylinders and dependent choices. These are
ordinary source profiles and probability queries, not new source constructs
or runtime layers. The reference changes honest kernels for the summation
only; it is not the source deviation or the source marginal of the coupling.

`SealedCompilation.recordedChoiceRestriction` constructs this reference profile
from the prefix's private commitment service, fixing only occupied honest source
slots. Unoccupied slots retain their original kernels, the focal policy is
unchanged, and recompilation gives precisely the corresponding graph kernels.
`restrictedSourceRun_source` identifies its law with ordinary restricted source
execution. `restrictedSourceRun_replay_prefix` proves that every supported
reference realization reproduces the entire recorded native prefix, including
pending messages, histories, clock, and receipts. The cutoff is arbitrary; this
support theorem does not assert probability agreement after timeout. The service
is proof-facing data, not an additional observation available to a player.

`restrictedSourceRun_registration_kernel` compares the original source kernels
throughout this reference support with their laws at the same recorded native
input, before first timeout. All reference realizations are covered, including
those with zero original probability. Changing the assigned honest values leaves
the selected registration slot unchanged; its draw law still comes from the
original source policy.

`restrictedSourceRun_registration_probability` identifies each such factor with
the probability assigned by the written-source policy at its recorded source
view. It covers every queried value, including zero-mass choices, and permits
the compared policy to differ from the profile generating the reference law.
The compiler supplies the source occurrence and its view through terminal field
agreement. The paper audit is `pending_registration_source_probability`.

`extractedSourceRun_replay_iff_restriction` identifies the restriction event with
the exact replay cylinder on the original source law. The proof projects recorded
choices from the terminal source environment and identifies their compiler fields;
the native service fixes exactly the same honest source slots.
`extractedSourceRun_replay_probability` transports the cylinder probability through
the checked source/graph law. `extractedSourceRun_replay_likelihood`, audited as
`Vegas.Paper.pending_source_cylinder_likelihood`, computes that mass as the original
forced-choice likelihood averaged over the normalized restricted source law.
These equalities allow arbitrary cutoffs, dependent choices, and zero-mass events.

`restrictedSourceRun_weight_eq_product` proves this weight constant throughout
the reference source law. Each occupied honest slot has a pre-timeout registration
checkpoint, supplied by the native provenance theorem
`SealedResolution.registrationCheckpoint_selected`. At that checkpoint the
original native kernel supplies the corresponding source factor. Focal and
unoccupied source slots contribute one.
`extractedSourceRun_replay_prob_eq_product`, audited as `pending_source_prefix_product`,
therefore expresses the source cylinder mass as an explicit product of original
native registration probabilities, with the reference expectation eliminated.

`replay_registration_factor` identifies each actual fresh honest invocation
with its selected checkpoint's original kernel. The two snapshots may differ;
their successful reads agree with the same complete source realization.
`replay_prefix_prob_eq_product` counts each tracked first registration once.
Submissions, retries, delivery, inclusion, and ticks leave the product unchanged;
focal registrations have unit weight. The calculation allows zero factors.
`extractedSourceRun_native_prefix_law`, audited as
`Vegas.Paper.pending_source_native_prefix_law`, proves equality of the complete
native prefix laws through first timeout. Its other marginal is the ordinary
written-source execution with the extracted focal policy and unchanged opponents.
This is a whole-prefix probability theorem, including the pending pool and
histories, for fixed deterministic focal and environment responses.

`exists_randomized_source_coupling` predraws the focal and environment response
pair jointly, preserving their dependence, and retains the whole native policy
trace. The continuation theorem attaches the actual post-timeout suffix from
the selected checkpoint. `exists_randomized_stopping_round_source_coupling`
therefore has the actual round driver's native marginal and a source marginal
that is a finite mixture of legal unilateral source deviations against unchanged
opponents. This coupling supports utility domination; it does not assert exact
source/native outcome equality after a timeout.

The backend admits homogeneous commit/reveal programs with unrestricted guards,
including multistage choices whose information includes earlier public values
and their owner's prior commitments. Nonempty choice-information sets are
justified by the reachable-store invariant, not erased from the source.
Samples, nontrivial validation guards, and disclosures of initial private
fields still require further compiler support.

The coupling covers arbitrary native unilateral policies using the player's
inbox, public ledger, sent messages, receipts, and local command history. The
environment may use all pending payloads. Its randomized backtranslation
preserves joint response dependence rather than independently resampling honest
source choices after disclosure.

Pending-message visibility is explicit dissemination: delivery copies a still-pending
packet into a player's inbox without including it. A later player invocation can
react before inclusion. Arbitrary invocation schedules admit submission, delivery,
reaction, and inclusion interleaved in that order. The completed-round strategic
theorem uses the more structured driver: all player calls, then wire-service calls,
then a tick. A packet delivered in its service phase can be acted on next round
while still pending. Neither interface gives players synchronous global access
to the entire pool. The external wire policy is adaptive but fixed; player-builder
coalitional control is not a unilateral player deviation in this game.

An inclusion check alone cannot protect against observing a pending opening.
The compiled policy checks the publication barrier **before submission**:
every source-earlier commitment is publicly complete, hence accepted on a
pre-timeout run. Consequently, replay before the focal choice is accepted can
encounter only honest openings already available
in that choice's source view. The checked whole-run read-boundedness theorem
connects this local barrier to the extracted source policy.

For selective quitting, exact outcome-law simulation and Nash preservation
are separate targets. `SealedCompilation.RoundModel.isεNash_iff_of_checkpointDominance`
provides the latter for the actual pending-message round game under timely
service, normal source/native utility agreement, and a conditional comparison
at each supported timeout-checkpoint observation. The coupling jointly retains
the actual native result and local information; its legal source completion
retains every focal registration in that history. Its source-policy mixture
is fixed ex ante, not selected by the checkpoint observation. Arbitrary native
deviations are bounded by legal source deviations, with a margin times timeout
probability in the quantitative theorem. `timeoutCheckpointDominance_of_locked_cap`
reduces the comparison to native caps and bounds over all commitment-compatible
terminal source configurations. `checkpointUtilitySimulation` packages
comparisons valid at every profile as a composable certificate. A uniform cap
below every source utility yields `utilitySimulation` as a sufficient case.
These incentive conditions still require proof for the program's chosen
utilities; ordinary source quit dominance does not establish them.
`SealedResolution` supplies per-node relative deadlines and nullable defaults,
then permits later application actions. Its round driver uses the shared
message runner and separates adaptive wire choices from fixed clock ticks.
A concrete checked-source test identifies its resolved public values with a
legal written-source execution. The source-policy translation shares its node
selector and sample-once command generation with the untimed policy. It skips
timed-out nodes, discharges their prerequisites, and reconstructs own missing
commitment fields using the default; an existing private registration is
retained. Before timeout the two policies agree exactly on the projected
event/history input. Checked multistage-source regressions continue after both
a missing commitment and a missing opening. Post-default read availability,
finite termination, and periodic service excluding honest timeouts are checked.
The honest outcome theorem counts every source player's conditional draws and
uses only environment predrawing, retaining the original source profile.
Public initial data and opening events reconstruct the public store, with
typed-field agreement on normally decoded runs. The public payout evaluator
uses that store without reading the private commitment service, and
`publicPayout?_eq_source_of_terminal` proves equality with the decoded source
payout on normal runs. `publicPayout?_eq_source_of_complete` also supplies a
legal written-source execution and equal payout after defaults, using reveal
uniqueness derived from source accounting. `RoundModel.play_publicPayout_source`
applies this to every supported outcome of the actual game without a service
assumption. This public-settlement witness may change private choices and is
not the commitment-preserving witness in the strategic coupling.
`RoundModel.play_publicPayout_source_choice` strengthens settlement correspondence:
if a player owns a native timeout, the same legal source witness records that
player choosing the configured default and yields the actual public payout.
`VegasCore.QuitPayoutBound` is a sufficient condition over written-source
executions alone. It certifies the designated quitting payout as a global
minimum for each player: all legal outcomes give that player at least its bound,
while legal outcomes recording that player's configured default give it at most
the same bound. Arbitrary valuations of the programmed payout are allowed. In
`RoundModel.isεNash_iff_of_sourcePayoutBound`, the compiler derives normal utility
agreement and every timeout comparison, leaving only the source certificate and
deadline-relative service as premises. The statement uses the actual native
policy game and preserves the approximation error. `sourcePayoutSimulation`
packages this concrete edge as a generic, composable `UtilitySimulation`;
its strategy compiler is the generated sealed-policy translation. It does not assume a
native settlement bound or a deviation simulation supplied by the programmer.
More general commitment-dependent and conditional source continuation tests
remain open; the uniform certificate is stronger than ex-ante quit dominance.
The checkpoint is first
timeout, not necessarily the last opportunity at which the player could avert it.
Malformed messages are rejected without a source step. Fair deadline resolution
must implement the programmer's quitting settlement; a rejected attempt alone
does not do so. In particular, withholding a committed `some a` cannot be
identified with a full source environment where its deterministic reveal copied
`none`. The coupling must retain the locked source choice and compare its legal
continuation with the runtime settlement. Ordinary ex-ante strict dominance of
the source quit action does not establish this comparison at finer stopping
information. The strategic interface is the instantiated `UtilitySimulation`,
not an assumed exact-outcome `MixtureSimulationOn` for selective quitting.

The source-to-declared-read-graph strategic edge is discharged independently of
these pending-message obligations. Its full source-environment outcome law
allows samples, validation guards, and heterogeneous fields. This does not
extend the admitted fragment of the sealed backend or grant its policies the
same information boundary as the graph kernels.

The pending-message compiler and its source-only payout theorem currently apply
to the admitted `SealedFragment`: one homogeneous runtime value type, no sample
nodes, and guards certified to accept every value of that type. Arbitrary
nontrivial validation guards, chance nodes, heterogeneous sealed values, and a
strategic refinement from commitments with multiple or potentially unopenable
candidates are not established by these results. The candidate host's checked
binding, source-settlement, and honest payout laws do not discharge that strategic refinement.

## Deliberate non-claims

The tower currently has no cryptographic reduction, implementation of authenticated identities,
block-production/fairness theorem, unconditional public-mempool Nash theorem, EVM
execution/refinement theorem, or contract settlement theorem. Those are future
runtime edges. The `archive/fused/` directory contains the former fused
application-plan development as readable research material; its results are not
imported by the active tower or counted by `Paper.lean`.
