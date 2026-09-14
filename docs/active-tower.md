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
| Sealed native protocol | `Interaction` | message pool, ideal commitment service, `SealedProgram`, policy runner | Commit and reveal are separate protocol actions. Arbitrary finite native traffic—including malformed payloads, retries/replay, delivery, inclusion, and withholding—either stutters or takes a valid graph step. The environment sees the full pending pool; player views expose their own inbox/sent messages and the public ledger. Hiding is proved for protected pre-disclosure traffic. |
| Resolving native protocol | `Interaction` | `SealedResolution`, shared policy-runner rounds | Per-node relative deadlines, nullable resolution, and continuing execution are implemented. Before the first timeout, validator/event projection is exact. Private bindings persist under arbitrary policies and resolution. Wire scheduling cannot trigger extra clock ticks; every round advances the clock once. General termination, fair-service, and source-settlement theorems remain open. The single-checkpoint `SealedTimeout` model instead records final failure and does not implement this continuation. |
| Vegas compiler edge | `Vegas.Compile` | `SealedCompilation`, sealed decode/refinement/source modules | One sealed rule per graph node; native prefixes decode to reachable graph states; terminal prefixes reconstruct a written-order source run with matching bindings and payoffs. The policy runner has the same support-level source theorem. |
| Strategic adapter | `Vegas.Game` | `SealedCompilation.StrategicCertificate` | A concrete target game may supply an honest law and a finite-mixture backtranslation; generic transport then gives the Nash/ε-Nash theorems. The certificate is an explicit obligation, not an automatic consequence of prefix refinement. |

## Current strategic gap

`SealedCompilation.compilePolicy` implements a written-source policy in the
native principal-scoped interface. Local reconstruction reads only initial
source-visible inputs, public application events, and the owner's registration
history. The checked registration-memory invariant holds under arbitrary
opponent and environment policies. Fresh registrations use exactly the
declared-read source kernel; occupied slots publish an opaque handle without
resampling. Every emitted opening already satisfies the public publication
barrier, and no compiled-policy packet is a cleartext commitment.

These local policy laws are not the whole-program honest or deviation law.
The mathematical coupling and its remaining Lean obligations are described in
[pending-message-strategic-proof.md](pending-message-strategic-proof.md).

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

The remaining probability argument must instantiate this restriction with the
honest registrations in each native prefix, identify its event with the replay
cylinder, and prove its weight constant using the fresh-kernel agreement.
That constant must equal the actual native prefix product. The general
source summation and native factorization are checked; this compiler-specific
equality is not. Randomized responses must also be predrawn
consistently across honest assignments, and the post-timeout native suffix must
be attached with its actual continuation law. Pointwise choice agreement alone
does not establish these probabilities for dependent source decisions.

The backend admits homogeneous commit/reveal programs with unrestricted guards,
including multistage choices whose information includes earlier public values
and their owner's prior commitments. Nonempty choice-information sets are
justified by the reachable-store invariant, not erased from the source.
Samples, nontrivial validation guards, and disclosures of initial private
fields still require further compiler support.

The active code does **not** yet prove whole-program strategic preservation for
the pending-message policy game. The immediate coupling must give the actual
native execution marginal and a source marginal that is a finite mixture of
legal source deviations, against unchanged opponents. The deviator may use its
inbox, public ledger, sent messages, receipts, and local command history; the
environment may use all pending payloads. Extraction must preserve the dependence
between honest draws rather than resample them after disclosure.

An inclusion check alone cannot protect against observing a pending opening.
The compiled policy checks the publication barrier **before submission**:
every source-earlier commitment is already bound. Consequently, replay before
the focal choice is bound can encounter only honest openings already available
in that choice's source view. The needed whole-run read-boundedness theorem
connects this local barrier to the extracted source policy.

For selective quitting, exact outcome-law simulation and Nash preservation
are separate targets. The latter can use `UtilitySimulation` if every runtime
deviation is no better than a legal source deviation. The native fixed-opening
utility bound is checked, but its whole-program continuation instance is not.
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
a missing commitment and a missing opening. The general compiler admission,
source outcome evaluator connection, post-default read invariants, and
service/termination proofs are still missing. The mathematical note gives
those arguments and constructs the source/native coupling for the nullable,
unique-direct-reveal fragment;
the whole-program proof is not yet implemented in Lean.
Malformed messages are rejected without a source step. Fair deadline resolution
must implement the programmer's quitting settlement; a rejected attempt alone
does not do so. In particular, withholding a committed `some a` cannot be
identified with a full source environment where its deterministic reveal copied
`none`. The coupling must retain the locked source choice and compare its legal
continuation with the runtime settlement. Ordinary ex-ante strict dominance of
the source quit action does not establish this comparison at finer stopping
information. The immediate final interface is the existing `UtilitySimulation`,
not an assumed exact-outcome `StrategicCertificate` for selective quitting.

The source-to-declared-read-graph strategic edge is discharged independently of
these pending-message obligations. Its full source-environment outcome law
allows samples, validation guards, and heterogeneous fields. This does not
extend the admitted fragment of the sealed backend or grant its policies the
same information boundary as the graph kernels.

## Deliberate non-claims

The tower currently has no cryptographic reduction, authenticated identities,
block-production/fairness theorem, public mempool scheduler theorem, EVM
execution/refinement theorem, or contract settlement theorem. Those are future
runtime edges. The `archive/fused/` directory contains the former fused
application-plan development as readable research material; its results are not
imported by the active tower or counted by `Paper.lean`.
