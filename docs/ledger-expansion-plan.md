# Compilation tower: implementation plan

This is the implementation plan for [compilation through operational games](compilation-design.md).
The [ledger design](ledger-expansion-design.md) specifies detailed event,
service, and security obligations. [Runtime models](runtime-models.md) records
what is proved. The plan is not a theorem inventory or a promise that the
strongest proposed preservation claim will hold.
The non-binding [road ahead](a-road-ahead.md) discusses alternatives for
factoring features and reaching the concrete target; its proposals can change
without being treated as completed gates.

## Scope and work order

The implementation objective is at least the draft's feature breadth and
strategic depth through faithful public interaction, with a visible path to
concrete runtimes. The private-window manuscript is an existing checked
baseline, not a substitute endpoint for this objective. In particular, a
single homogeneous commitment example does not recover the draft's guarded,
finite-domain, chance-bearing, multistage compiler result.

The acceptance inventory has two axes:

| Requirement | Public-message path | Required endpoint |
| --- | --- | --- |
| Independent source meaning | Source-to-graph connection, terminal native support, and an exact completion/public-outcome law for every eligible application plan under arbitrary source profiles and the generated reference service | The actual supported source's choices, information, nonresponse consequences, and outcomes are the comparison endpoint. |
| Source coverage | Structural binding/chance/public-choice/conditional-publication compilation, arbitrary-traffic support refinement, whole-source strategy lifting and reference execution, with explicit initial-read and binding-origin eligibility | General supported finite typed programs with guards, chance, and multistage dependencies; implementation conditions are explicit and exercised. |
| Hostile interaction | Raw traffic, local delivery, replay, addressed public inclusion, ideal binding/hiding; initialized disclosure settlement against arbitrary opposing policies under the stated slotted service | Whole interaction, failure, deadline and observation behavior under the theorem's complete player/environment policy classes. |
| Strategic comparison | Release-time hiding/choice independence; completed-owner mixtures for the chance-free fragment; exact responder-deviation laws and source bounds for disclosure with a fixed pure owner under resolving service; selective-publication and withholding obstructions | Compiled-profile law plus arbitrary unilateral-deviation comparison, with the corresponding source-outcome bounds and equilibrium results. |
| Substantive application | The private-window sealed offer and a public-message compiled-prefix fixture | The generated protocol application and handlers use the same public-message compiler path; reference strategies and their guarantees are related separately. |
| Further lowering | Separate local backend proofs | A named generated-handler path instantiates that application semantics; subsequent realization obligations are explicit. |

An obstruction must identify the incompatible property/model pair and guide
an implemented alternative, supported fragment, or weaker guarantee. It does
not by itself satisfy a missing positive compiler or application requirement.
Do not make eligibility circular by requiring the claimed deviation theorem
as an input certificate. Do not promise exact preservation for a model whose
admitted censorship or withholding contradicts it.

Build the shared operational/strategic runtime connection before expanding
backend breadth. Keep the minimal Vegas core and its well-formedness discipline.
Do not reproduce the rich Kotlin language in Lean.

The compiled artifact tower consists of protocol representations: graphs,
public-message applications, contracts, wire formats, and target code. Lifting a
source profile constructs reference runtime strategies for proofs in parallel
with that tower. It neither emits client software nor removes arbitrary native
policies from the deviation space.

The first delivery is a public-message model with recipient-local observations,
a real core-to-model compiler slice, and checked strategic evidence about that
execution. A weaker positive result or a precise obstruction is acceptable
evidence at a research gate. A disconnected runtime, a restated preservation
hypothesis, or a trace example alone is not completion.

### Whole-program forward-law checkpoint

`ApplicationPlan.service_source_public_law` relates the independent source
denotation to the shared application's completion and public terminal readout
for every eligible `ApplicationPlan`. Its proof-side `ForwardCheckpoint` carries:

- The original plan/profile's `ProfileContinuation` to the current suffix.
- The exact source/graph prefix (`CoupledAt`) and native `State.Refines`.
- Support in an initialized run under the same original lifted profile.
- Alignment of the service's actual environment-history length with the
  unexecuted emitted-instruction suffix.
- `RemainingCachesEmpty` for the unexecuted suffix.
- `AcceptedBindingPrefix`: canonical accepted handles for every generated
  binding before the current source prefix.

The initialized-run witness supplies message-identifier freshness, memory
coverage, registration consistency, and typed registration provenance; these
are derived rather than stored again in the checkpoint. Static binding
origins locate an earlier binding for each conditional; the dynamic accepted
prefix supplies its handle. The checked snapshot bridge then recovers the
source value without a separate evolving snapshot-value invariant.

The chance, binding, public-choice, and conditional head theorems preserve this
checkpoint on every supported successor. Structural induction composes them
with the existing `denoteSource` equations and the shared runner's append/bind
laws. The result compares the joint `(finished, readPublicTerminal?)` law with
the source law mapped to `(true, some public outcome)`. `readPublicTerminal?`
alone remains only a field reader; `CoupledAt.finished_public_readout` supplies
both termination and the exact public projection. Sealed source values remain
proof witnesses and are not decoded from public runtime memory.

The entry theorem assumes `InitialControllerReadsPublic`: only source-initial
fields in generated player-controller footprints must be public. This is a
backend condition, not source well-formedness, and does not provision sealed
initial inputs. It also assumes `HasBindingOrigins`, because a conditional
endpoint needs an actual earlier generated binding; an ordinary public write
does not synthesize a commitment handle.

`ApplicationImage.serialService` and `serviceInvocations` supply a concrete
source-ordered reference service on the shared runner. The service indexes
emitted instructions by its own environment-history length. It invokes chance
at sample heads and otherwise includes the instruction owner's most recent
submission if it remains pending, without inspecting payload contents. Its exact
post-submission command and history-count laws are checked. The forward proof
establishes their premises from empty environment history and the image-derived
invocation list while retaining the same original lifted source profile.

This finite service advances its index even after a wait or rejected request;
it is not a fairness, retry, or withholding-resolution mechanism. Those need a
separate service and its proof, rather than additional invocation steps silently
inserted into this exact script.
Arbitrary environments retain the safety guarantees for runs that finish;
they do not imply completion or equality with the terminating source law.

### Resolution and open deviations

The disclosure application has a complete one-sided strategic instance in
`VegasTests/DisclosureResponderDeviation.lean`. Under its actual resolving
service, any raw responder deviation against a fixed pure owner is simulated
by one written-source behavioral responder policy. The same service preserves
compiled pure-profile laws; source worst-case outcome bounds transfer without
a completion premise, and the responder's epsilon-best-response property
transfers with the same error for source-outcome utilities. The response window
is positive and the horizon is at least `window + 3` cycles. The public coin
marginal is proved invariant under adaptive traffic, rather than inferred from
terminal support.

This instance does not discharge the general generated-application service
gate below. Extending it to owner deviations or randomized private owner
choices requires the joint binding/signal law and the corresponding source
information restriction; matching each terminal witness alone is insufficient.
Do not infer whole-game equilibrium preservation from responder-only adequacy.

`ApplicationPlan.withholding_no_source_public_law` establishes a code-level
obstruction to upgrading the reference law by service assumptions alone.
Undecorated binding and fallback-free ordinary-public-choice nodes require an owner-authored
message. Replacing that owner by permanent waiting leaves the program unfinished
under every environment policy and finite invocation schedule. The theorem
retains completion in the outcome; it does not rule out weaker observations or
an extended implementation with genuine source-certified fallbacks.

Conditional publication supplies a source-certified decline entry point.
`ConditionalPublicationSite.expiry_include_source_coupling` relates an actual
included, overdue expiry packet from any sender to the existing source decline
and exact source continuation. The packet must actually be submitted: the
environment's inclusion capability cannot author it.

Ordinary public choices can be annotated with a
`SourceDecisionSite.PublicFallback`:
a typed public source expression whose value is universally guard-legal. Its
compiled optional expiry code uses the same application interpreter, and an
actual overdue inclusion has the annotated source continuation. This is a
designated source-legal backend resolution, not inferred programmer intent or
equality with the original owner's policy. The annotation and source accounting
remain separate. See [timeout compilation](timeout-compilation.md).

Source-certified binding defaults are emitted as optional typed timeout code.
`PublicFallback.expiry_include_source_coupling` relates an actual pending,
overdue expiry inclusion to the original source commit with the evaluated
fallback. Public defaults have exact typed refinement and direct local readout;
opaque bindings retain their separate frozen-snapshot provenance. The generic
conditional-publication classifier and generated conditional instructions handle
both dispositions. The selected cleartext/opening policy law and actual included
source continuation are checked at ready conditional checkpoints. Whole-program
settlement under the block service below remains a proof obligation. Binding
and public-choice timeout decoration commute; the combined artifact preserves
the no-expiry reference
profile law, while each pass retains arbitrary-traffic graph refinement.

The remaining implementation order is:

1. Compose exact source checkpoints and unchanged-player cache/readout
   invariants across arbitrary successful resolutions. Public-choice and opaque
   binding phases already preserve the unchanged owner's source kernel after an
   arbitrary initialized prefix, given a coupled source checkpoint, fresh own
   caches, and immediate inclusion. The public-choice sampling law retains the
   original draw jointly with arbitrary finite native continuations, including
   payload-dependent delivery and retries, without requiring inclusion.
   `ApplicationConditionalOwner` provides the corresponding first-emission and
   joint-retention laws for conditional and repeated conditional disclosure,
   with explicit accepted disposition and canonical-handle requirements. Compose
   this retained sample with resolution and the next source checkpoint; repeated
   polling must not draw afresh. Completed-node prefixes
   and accepted dispositions are already policy-independent invariants; they
   do not identify an unchanged player's source choice kernel.
   `WindowedContinuationReadout` proves actual owner readout after a supported
   windowed prefix, including expiry traffic. Only that owner must retain the
   block-gated reference policy; opponents and the environment remain arbitrary.
   Its memory-coverage and typed-registration invariants are derived from the
   actual run. The coupled source checkpoint is still an explicit premise,
   to be maintained by the blockwise source-law induction.
   `WindowedConditionalOwner` supplies the conditional and copied-conditional
   owner kernels in this same runtime, preserving the sampled choice jointly
   with the full subsequent execution. Accepted disposition, canonical handles,
   fresh cache, and source readiness are explicit local requirements.
2. Supply a resolving service with observation-local request production and
   admitted inclusion capacity. `ApplicationPlan.windowed` provides stable
   public activation origins, strict expiry, and arbitrary-run source-outcome
   safety. Observation erasure also gives the exact source law for the
   expiry-free reference profile and serial service on this instance.
   `WindowedApplication.relayWhenWaiting` lets an existing principal originate
   an overdue expiry using its actual public view and history. The three
   `relay_*_accepts` laws compose this submission with inclusion and the actual
   handler, retaining sender identity, ledger entries, and receipts. This is a
   local reserved service, not a whole-program settlement theorem. Prove timely
   ordinary opportunities when valid requests compete with expiry and ensure
   an available relay under each admitted unilateral deviation.
   The service design in `WindowedApplication.blockSchedule`, `blockPlayer`,
   and `blockEnvironment` assigns each emitted instruction a fixed block:
   two ordinary polls per roster member, ordinary inclusion or chance, a
   clock-advance slot, and one relay/inclusion pair per roster member. All
   environment commands are gated by that block's instruction address.
   Reference player policies use their actual local history length to separate
   ordinary polls from relay-only polls. Once an instruction resolves, its
   remaining slots cannot operate on the successor. The arbitrary deviating
   policy is substituted **after** this reference-policy construction; its
   native commands and observations are unrestricted.
   Required assumptions are a duplicate-free roster covering the owners,
   an unchanged relay member for each admitted focal deviation, canonical
   history alignment, and source-certified default handlers. Inclusion capacity
   and clock progress are supplied by the stated service, not by player code.
   The whole-block obligations are slot alignment, preservation of source
   kernels under inert polling, resolution, and absence of successor effects.
   History-count alignment and resolved-block public-state isolation are checked.
   Other-player polls preserve an owner's entire policy input, so their raw
   traffic cannot bias that owner's next command kernel before delivery or
   inclusion. The local relay law retains the actual packet, ledger and receipt.
   `WindowedBlockSettlement` proves the clock slot and support-total relay-segment
   settlement from per-state eligibility; its binding specialization derives
   the concrete accepting expiry and matching source successor from a ready
   source checkpoint and the designated public fallback. The expiry author is
   independent of the source owner.
   Whole-block progress and source-kernel composition are separate obligations.
   The generated two-owner regression in `VegasTests.WindowedBlockService`
   executes the entire first block: a silent owner is resolved by the other
   player's genuine expiry submission, and the remaining slots preserve the
   successor's activation time. It checks the policy runner, not a fabricated
   checkpoint. `WindowedBlockSample` retains each source chance draw jointly
   with arbitrary preceding raw player polls and the full subsequent block
   execution; its public checkpoint is unchanged by the aligned suffix.
   `WindowedBindingOwner`, `WindowedPublicChoiceOwner`, and
   `WindowedConditionalOwner` recover each unchanged owner's exact source draw
   at its actual windowed checkpoint, including prefixes with expiry. Their
   joint laws retain the draw with the real subsequent execution and cache.
   They require source refinement, the relevant empty owner cache, and correct
   block alignment; deriving those premises at successive blocks remains part
   of the whole-program proof.
3. Compare arbitrary player replacements on that same execution. Start with a
   final conditional disclosure under an actual resolving phase, then compose
   across prior bindings, chance, and later decisions. A support witness for
   each terminal result does not provide one legal source-policy law.
   Backtranslation must construct decisions causally from source information.
   Choosing a source policy after observing a final runtime outcome can couple
   that policy to future chance or unchanged opponents' random choices; such a
   terminal-witness construction is insufficient. The required law retains
   unchanged-owner and chance kernels jointly with the previously extracted
   focal decisions.

For the fixed block service, the causal proof separates three obligations:

- Present the focal principal's calls as decisions and all unchanged calls as
  their existing stochastic kernels. The native theorem
  `MessageApplication.exists_native_policy_mixture_runPolicies` supplies a
  finite mixture of pure native replacements with exactly the original full
  execution law, keeping opponents and the environment fixed in every branch.
  It applies to an arbitrary finite invocation schedule and starting execution.
  The internal presentation uses
  the actual focal history and current view, and reuses the shared runner's
  transitions; it is an analysis adapter, not another runtime.
- At a focal-owned block, unchanged players only wait or relay. After fixing
  the focal pure policy, the resolution is deterministic from the starting
  checkpoint. `WindowedBlockDeterminism.runPolicies_block_eq_pure` proves
  point-mass execution of the complete fixed block from its actual aligned
  checkpoint, for any pure raw focal policy and arbitrary base policies of
  the gated opponents. This determinism theorem does not itself prove that
  the block resolves. An unopenable binding uses a legal source witness selected at
   that binding, not after future chance; `State.BindingsRepresent` deliberately
   constrains recovered typed snapshots but permits absent or ill-typed ones.
   `WindowedBindingBlock` recovers the source value from the actual acceptance-time
   snapshot, using a checkpoint-local legal value when recovery fails. With
   the emitted timeout selector tied to a source-certified public fallback,
   every accepted message is classified as an authenticated binding submission
   or an expiry installing that fallback. The expiry case uses the actual
   activation-relative deadline. Premature expiry and other payload constructors
   are rejected. This classification concerns the actual handler and does not
   assume a canonical deviating policy.
  At an unchanged-owned block, its source kernel must remain exact even though
  the focal principal can still submit arbitrary traffic during its own polls.
- Prove that the focal history needed by a pure policy is determined by that
  policy and the prior source-visible footprint. Source contexts retain prior
  public fields and the player's own fields. The proof must account for
  rejected traffic, public activation, serial numbers, and private registration
  without assuming equality of hidden opponent state. This locality statement
  is essential to turn a runtime resolution into a legal source policy.

`WindowedCheckpoint` records a supported prefix of the actual repeated-block
runner, source refinement and continuation, empty remaining caches only
for unchanged owners, and a fresh activation origin at the current public clock.
Freshness is an inductive boundary invariant: it holds initially and after
successful resolution, and inactive block padding preserves it. Clock
advancement within an unresolved block preserves consistency but can consume
the window; consistency alone does not give an ordinary-service opportunity.
Completed binding dispositions are derived from that
initialized execution: opaque bindings have their canonical generated handles,
and timeout resolution may supply a public default. Requiring an opaque handle
at every completed binding would exclude source-certified timeout execution.
The generated `WindowedBlockService` regression retains the public default
jointly with the successor's activation and clock. The focal replacement is
installed after the reference-policy gates and may prepare future messages.
Serial freshness, no-delivery provenance, consistency, and history alignment
follow from reachability. The canonical zero-block checkpoint is constructed
from a checked program. The certificate contains no pairwise information
agreement or extracted-action locality premise.

The checkpoint's `completed_instructions` and `activeAddress?_head` derive
instruction completion and active admission from the source cursor. The
`sample_block` theorem in `WindowedSampleCheckpoint` derives handler lookup
and slot alignment at that cursor and compares an entire emitted chance block
with the source chance kernel, jointly retaining the native successor.
Every supported final state of that block refines the corresponding source
successor; histories, pending traffic, and private preparation remain in the
native law. Its `sample_bind` continuation theorem constructs the successor
checkpoint, including initialized reachability, unchanged-owner cache
freshness, and a fresh activation origin, and composes the block with any
continuation that agrees at those checkpoints. The focal policy remains
unrestricted throughout the block; only unchanged reference policies are
shown to wait during sample polls.
Player-owned source-policy reconstruction is a separate obligation.

At an opaque binding, `WindowedBindingBlock` classifies arbitrary accepted
traffic, including certified expiry, and retains the legal source successor
and its fresh activation through actual relay resolution.
`WindowedCheckpoint.binding_block` constructs the actual initialized successor
checkpoint after the complete generated block, including refinement, source
continuation, an explicit sequential source step, fresh activation, and future
unchanged-owner caches. It requires
a source-certified fallback selected at that binding, a duplicate-free roster,
and one roster relay distinct from the focal player. The focal replacement
remains unrestricted. This is a supported-execution result for the fixed block
service, not yet a source-policy or deviation-law theorem.
`WindowedCheckpoint.publicChoice_block` constructs the corresponding
commit/reveal successor for publicly validatable ordinary choices, retaining
the guard proof and both sequential source steps. It uses the same service and
relay requirements with the public-choice fallback selector. Its underlying
expiry classification identifies the result with the programmer's exact
source fallback expression.
`WindowedApplication.handle_conditional_source_coupling` classifies an actual
successful raw conditional handler at the generated source head. It retains
the optional source result, guard legality, and the corresponding source
continuation and native refinement. A successful opening itself supplies its
frozen-value evidence; the theorem assumes neither an unchanged owner policy
nor private-readout availability. `WindowedCheckpoint.conditional_block` and
`conditionalCopy_block` extend this classification through the complete block
service. They construct initialized successor checkpoints, retain the optional
result and guard legality, and prove the explicit adjacent source steps.
Their extra static premise is the root image's binding-origin certificate;
the same duplicate-free roster and unchanged-relay requirements apply.
They establish supported source successors, not the distribution of the
unchanged owner's disclosure decision.
`WindowedCheckpoint.block_caches` preserves future unchanged-owner caches
through any generated instruction block. The constructor-uniform
`liftProfileIn_headCommand` classifies commands from an unresolved source
head; the ordinary-poll induction uses the original profile's continuation.
The remaining reference-player slots emit only waits or expiry requests.
The focal replacement is exempt from those command restrictions throughout.
`WindowedBlockSourceCoupling` shares the relay-segment induction over the
constructor-specific source witness and successful-resolution proof. These
cache and resolution results do not yet construct a source policy for an
arbitrary runtime deviation.

`SourceDecisionSite.windowedBinding_two_invocations_source_law`
derives the exact source kernel for two actual block-gated binding-owner polls:
private registration followed by the canonical opaque submission. The local
requirements are successful source readout, an unresolved ready binding, empty
owner caches, ordinary-slot alignment, and selection of the generated binding
controller at the starting public observation. No command or execution-law
equality is assumed. `WindowedApplication.PolicyAgreement.binding_twoPolls_of_ready`
uses that law to prove focal policy-input agreement for every pair of supported
outcomes, allowing different private source inputs and draws for the nonfocal
owner. It also identifies the actual resulting pool.
`WindowedApplication.PolicyAgreement.binding_inclusion_of_ready` extends that
comparison through latest-submission service: it derives the selected envelope
and preserves agreement through its inclusion and acceptance or rejection
receipt. Freshness is local to the newly allocated sender serial; unrelated
pending traffic is allowed. The compiled regression verifies successful
acceptance and the exact source law of the private accepted snapshot, as well
as observer agreement. These results assume agreement before the owner polls.
Deriving it from equal source views through complete blocks remains a separate
obligation.

`WindowedBindingReadiness` derives these controller prerequisites from an
actual `WindowedCheckpoint`: source readout, both empty caches, the root
profile's binding dispatch, and the owner's ordinary-slot alignment. The
source kernel equality therefore needs only the root's public-initial-read
eligibility, a duplicate-free roster containing the unchanged owner, and the
checkpoint, rather than separately assumed readout or dispatch equations.
`binding_polls_source_law_after_others` retains any preceding other-player
polls in the joint native law. Those policies may issue arbitrary commands;
the prefix contains neither an owner poll nor an environment turn, so it
cannot change the owner's policy input. This covers the ordinary roster
prefix before the binding owner, not later delivery or inclusion.
The paired-checkpoint inclusion theorem derives the same prerequisites on
both sides but still requires their starting information agreement. The
generated regression uses the original whole source profile and canonical
initial checkpoint, and checks successful acceptance with the exact source
distribution of the frozen snapshot.

`WindowedCheckpoint.binding_block_agreement` compares the complete binding
block when its owner is unchanged. It derives the owner's exact two-poll
source law at the actual position in the roster; the private draws in the two
executions may differ. The root's public-initial-read eligibility and a
duplicate-free roster containing the owner are explicit hypotheses. The focal
replacement is a fixed pure raw policy, and preceding information agreement
is still supplied, not derived from source views by this local theorem.

The native invariant used in this proof is owner-specific.
`WindowedApplication.runPolicies_other_frame` preserves public state, frozen
snapshots, the owner's prepared slots and allocation counter, and every
existing pending lookup through arbitrary other-player polls. The generic
projection/counter/lookup theorem lives in `Interaction.MessageApplicationLocality`.
Other players may add traffic or rebroadcast messages; the entire pool need
not stay equal to its earlier value. These facts follow from the actual
transitions, not from equality of the owner's observations, which expose
neither preparations nor counters.

`binding_ordinary_submission` derives the canonical packet's fresh identifier
and pending lookup after all ordinary roster polls. `binding_ordinary_inclusion`
then derives actual normal service and resolution from the checkpoint. Binding
admission freezes an optional prepared value, so acceptance itself does not
require a well-typed preparation. Neither theorem assumes successful admission,
an expiry relay, or a fallback selector. The remaining inactive suffix is
handled by `WindowedCheckpoint.after_normal_agreement`, whose schedule bounds
come from the supported normal prefixes. Its player gate covers the resolved
owner too. Regressions instantiate the complete paired theorem at the checked
persistent-disclosure program and exercise raw foreign registration,
submission, and successful replay while showing that the complete pool changes.

The locality comparison is between two supported executions of the **same**
canonical initialized program, source profile, pure raw focal replacement,
block schedule prefix, and block environment. Compare complete-block source
boundaries, not arbitrary native states satisfying refinement. The candidate
invariant equates public memory (including dispositions and clock), activation,
receipts, and the focal history, together with focal-owned private preparation
and relevant frozen bindings. Opponents' hidden registered values may differ.
For this completed-boundary comparison, full pool equality is a viable
invariant: first recall equal published values from the equal successor source
views, then compare the corresponding block executions with those values fixed.
Hidden binding draws can differ, but their submitted opaque handles coincide;
recalled public values fix public-choice and opening payloads. A theorem about
arbitrary intermediate pairs would instead need only equality of the focal
pool view and of the service's identifier-selection data. That stronger
comparison is not required for the completed-boundary argument. Focal input
agreement must be derived from initialized execution and equal focal source
views, not assumed as a restriction on the deviation theorem.

`WindowedSourcePrefix` is a single-run inductive derivation indexed by the
source suffix, source environment, native execution, and block count. Each
edge retains its predecessor, actual full-block support, a `BlockSourceStep`
with the exact source extension, and a genuine successor checkpoint. The
binding constructor retains the canonical acceptance-snapshot or fallback
extraction equation. No information-equivalence premise is stored in the
derivation.

`WindowedSourcePrefix.covers` constructs this evidence for **every** supported
initialized complete-block prefix up to the emitted instruction count. The
replacement is an arbitrary randomized raw player policy. Its static and
service premises are source-certified binding/public-choice timeout selectors
(`BlockFallbacks`), binding origins, a duplicate-free roster, and an unchanged
relay in that roster. The theorem imposes no settlement, packet-shape, or
selected-source-action premise on the execution. `terminates` proves that the
full block count finishes the native graph and yields a terminal sequential
source execution. A generated persistent-disclosure regression discharges the
timeout certificates and covers all emitted instruction kinds. These are
support-level results, not equality of outcome distributions.

Comparing two such derivations remains the whole-prefix information
obligation. Backward source-view recall gives agreement at the preceding
source boundary: public values and focal-owned sealed values must agree,
whereas another owner's sealed values may differ. The constructor's paired
block proof must recover runtime policy-input agreement from that induction
hypothesis. A separate decision representative must pair a supported
pre-decision prefix with its resolution edge, so extraction never selects an
earlier action from a final outcome or a later chance result. That decision
carrier and its connection to source-policy extension remain unimplemented.

The fixed-draw comparisons also need a source-indexed inversion of actual
block support. For chance, public choice, and conditional publication, first
decompose the actual run to obtain its sampled value and its polling/service
branches. The accepted handler identifies the written public field, and
`runPolicies_block_inactive` preserves public memory through the remaining
slots. Independently, the successor checkpoint's refinement, source/store
agreement, and source-extension equation identify that same field with the
edge's recorded source value. Comparing the two readouts pins the decomposed
draw to the recorded value; conditional publication uses the source encoding
equivalence. These inversion lemmas must return actual fixed-branch support
and source-kernel support, not assume them. The existing prefix already
retains the required evidence, so no additional branch certificate needs to
be stored in `BlockSourceStep`. This is inversion of a supported block, not
selection of a source strategy from a final outcome.

The focal-owned block case is checked by
`WindowedCheckpoint.owned_block_agreement`. Given two actual checkpoints and
their preceding `PolicyAgreement`, it proves agreement after every pair of
supported complete blocks owned by the focal player. The raw focal policy is
fixed and pure; all of its commands remain available. Other players use the
original root-profile lifts. Their block gates select only waits or public
expiry submissions, and the environment never requests chance during an owned
block. Initial reachability supplies every history length and the compiler
supplies instruction lookup, including timeout decoration. No settlement,
accepted-packet shape, or final-inactivity premise is needed. The underlying
inclusion theorem permits arbitrary packets: an opening from a different
author cannot inspect that author's private snapshot at a focal-owned active
instruction. Regressions exercise the source-checkpoint endpoint and actual
rejection of such a foreign opening with distinct hidden snapshots.
`WindowedCheckpoint.sample_block_agreement_of_same_draw` compares complete
chance blocks through the same actual supported public draw. It derives the
ordinary player-prefix comparison and the inactive clock/relay suffix from
the original root-profile lifts and fixed pure raw replacement. The endpoint
returns both final information agreement and actual full-block support on
each side; the source chance law supplies that support. It does not assert
agreement between different public draws. `WindowedGatedExecution` supplies
the shared player-only and inactive-suffix inductions.

`WindowedCheckpoint.publicChoice_block_agreement_of_same_draw` compares the
unchanged owner's complete public-choice block with the same source-supported
published value. The two private source views and choice distributions may
differ. The source checkpoint supplies cache freshness, readout, dispatch, and
the exact first-poll source kernel; the generated second poll waits rather than
retrying or resampling. Arbitrary other-player polls preserve the owner's
fresh serial and submitted packet. Public validation derives native acceptance
from source legality, normal service includes that actual packet, and the
remaining clock/relay slots are inactive. The endpoint returns both final
information agreement and membership in each actual full-block execution.
It assumes neither successful inclusion nor final inactivity. A checked
mixed-type program exercises the result with arbitrary raw opposing traffic
and no timeout handlers. Binding and public choice share the derivation of
normal-service selection from actual polling.

`WindowedCheckpoint.conditional_block_agreement_of_same_result` compares
complete unchanged-owner conditional-disclosure blocks with the same supported
public optional result. `ConditionalHead` identifies the existing discharge
and copy constructors; it adds neither syntax nor a well-formedness rule.
The initialized checkpoint supplies the accepted binding disposition, cache
freshness, and source readout. The exact two-poll law draws once from the
source policy, submits the disposition-specific packet, then waits.
Ordinary inclusion derives acceptance for decline, opaque opening, and public
default. An opaque opening uses the actual registration provenance to recover
the frozen source value separately on each side; equality of the two private
verifiers is not a premise. Paired inclusion publishes equal optional results,
and `after_normal_agreement` supplies the inactive clock/relay suffix. The
endpoint retains both actual full-block support witnesses and final focal
information agreement. Its focal replacement is pure and unrestricted.

The checked persistent-disclosure program exercises both source constructors,
source-supported packet retention, and successful ordinary inclusion. Public
choice and conditional disclosure share the complete ordinary-poll comparison
and the runtime-general sample-once packet-retention theorem. Unchanged owners
resolve during normal service; deviating owners still require the resolution
service. Every instruction kind now has its corresponding local complete-block
comparison. Whole-prefix information reconstruction, source-action locality,
and the general deviation-law theorem remain obligations.

Binding-action extraction needs more than an existential successor checkpoint.
`handle_binding_source_coupling` computes the chosen value from the actual
acceptance-time prepared snapshot, using the source-certified public fallback
when the snapshot is missing or ill-typed. `BindingCode.resolvedValue` reads
the accepted frozen snapshot or recorded public default at the expected source
type. The complete `binding_block` endpoint retains equality with this
canonical extraction, including after inactive padding and further private
registration. The shared block-resolution proof transports the certificate
on native application states. `Refines` alone deliberately permits other
source witnesses for unopenable bindings; the extraction equation fixes the
witness used for backtranslation without restricting raw player commands.
`WindowedCheckpoint.binding_block_action_eq` proves the cross-execution
equality of these extracted focal binding actions from preceding information
agreement and equal focal source views. It derives completed-binding provenance
and native completion from an actual successor checkpoint, and projects the
source views to the public environments used by fallback evaluation. No final
action equality, accepted-message condition, or snapshot typing is assumed.
Instantiating `SourcePolicyCheckpoints.action_congr` still requires the
whole-prefix theorem to derive the preceding information agreement, and the
corresponding action-extraction results for public/conditional decisions.

For unchanged private bindings, the emitted handle and admission result are
independent of the hidden draw. For unchanged public choices, conditional
results, and public chance, equality of the source prefix fixes the published
value. Pure focal commands then agree because their actual inputs agree.
Clock/relay commands follow from the common block coordinate and public state.
Pending focal traffic and rejected attempts remain part of this induction;
they cannot be discarded or required to be canonical. The whole-run theorem
must derive any invariant concerning residual honest messages as well.

`ApplicationImagePrivacy` supplies an owner-local state relation retaining
public memory, that owner's prepared slots, and its accepted frozen snapshots,
while allowing other private values to differ. Private registration, binding,
public writes, and raw owner-authenticated handlers preserve this relation.
Non-opening packets also preserve it for any author: opaque binding admission,
public choices, declines, and expiry do not query a private verifier.
`WindowedPrivacy` carries it through ordered relative-deadline admission and
actual inclusion, including observable acceptance/rejection receipts. These
local results do not assume payload typing or legality. The author premise is
required only for opening packets and constrains the comparison theorem, not
the available commands. A replay retains its original author; another owner's
opening packet needs a source-value, provenance, or completed-address argument.
`WindowedApplication.PolicyAgreement.environmentPolicyStep_deliver` preserves
agreement through recipient-local delivery from equal pools, exposing the
actual packet without invoking its handler. It does not establish agreement
for arbitrary delivery strategies or replace the full-prefix comparison.
`WindowedForeignProvenance.runPolicies_repeatedBlocks_foreignAddressed` derives
foreign-message provenance through the actual initialized repeated-block run:
every retained nonfocal message targets an instruction before the completed-block
count, while focal messages remain unrestricted. This result permits an
arbitrary environment policy and does not assume an intermediate pool invariant.
At a source checkpoint, `foreignLedgerCompleted` combines that provenance with
the derived completed prefix. Replaying these foreign ledger packets cannot
change the application. The within-block theorem accounts separately for
messages targeting the current, not-yet-completed instruction.

These obligations concern the specified service. Adaptive delivery or an
additional clock or inclusion policy needs its own information comparison;
finite predrawing alone does not establish that comparison.
The fixed block service contains no pending-message delivery calls. Its
interpreter supports recipient-local delivery, but proving preservation for
that wider service class remains a separate obligation, not an implicit
consequence of the fixed-service theorem.
The absence of delivery is checked for `blockEnvironment`. The generic
`MessageApplication.runPolicies_noDeliveryProvenance` proves that inboxes stay
empty and any known foreign-authored packet is already in the public ledger,
including foreign packets retained in a broadcaster's sent history by replay.
The source-checkpoint provenance result connects those public packets to
completed source addresses. The binding-specific paired inclusion theorem
allows different private draws and proves equal ledger-visible messages and
receipts. The corresponding complete-block and source-prefix comparison must
also account for all intervening focal commands and other instruction kinds.

The required theorem is profile-relative, so the construction need only use
supported **prefix** checkpoints. For a fixed focal pure policy and a source
decision view, select a representative supported prefix with that view and
extract its resolved action. A locality proof must make this independent of
the representative's hidden opponent data. At views absent from that prefix
support, the given reference source policy supplies a total legal kernel.
An induction retaining the joint source/native prefix law then justifies the
construction; it must not select representatives from final outcomes or
condition an earlier action on later chance. This avoids requiring a
canonical completion of every counterfactual hidden source environment.
`SourcePolicyCheckpoints.extend` checks the totalization step: legal extracted
actions that agree at equal source views define a total source policy, with
the reference policy used away from supported views. Instantiating its carrier
and proving action agreement for actual runtime prefixes remain obligations.

Keep the designated fallback expression, its legality certificate, and backend
eligibility separate from core syntax and WF. `Legal` provides some legal action,
not the programmer's specified nonresponse consequence.

No point in this sequence restricts deviators to canonical payloads or lifted
policies. Unopenable bindings, malformed requests, replay, and silence must be
handled by the implementation and the comparison. The observation issue for
an opening delivered before a losing inclusion is recorded in
[timeout compilation](timeout-compilation.md#deviation-law-proof-targets).

A public default's value can be determined from prior public fields and the
compiled expression. The occurrence and timing of the default branch remain
additional public observations: they may reveal withholding behavior. Value
locality alone therefore does not establish the required deviation comparison.

Prefer focused replacement and extraction to a rewrite without a demonstrated
semantic need. There is no API compatibility requirement: update all consumers
and remove obsolete definitions when their replacements are checked. Keep the
existing valid proofs and default warning-free build throughout the work.

## R0. Establish semantic ownership

**Deliverables**

- Refactor the general Vegas game wrapper so its semantic ownership is not
  FOSG syntax. Keep bounded horizon and utility as analysis data or explicit
  capabilities, not requirements on every future operational target.
- Keep the independent source game as the source endpoint. Update names that
  call the compiled graph game the source game where that is not the meaning.
- Make the FOSG adapter a format export using the existing execution and
  information objects, with no new runner. Preserve current source/native,
  request, and serialization results under the refactor.
- Inventory generic game/protocol transformations currently in Vegas, compare
  them with GameTheory's existing APIs, and obtain the appropriate upstream
  architecture decision for additions. Generic backtranslation, outcome-law
  comparison, preference transport, and their composition belong there.
  Concrete Vegas field/decision reconstruction remains in Vegas.
- Move accepted abstractions with their generic tests into the separately
  managed GameTheory repository, then update Vegas callers and its pin.
  No duplicated stable definitions or compatibility wrappers. This plan does
  not authorize changing a GameTheory architectural decision by fiat.

**Gate**

The existing source and native-game audit statements still compile with the
same mathematical endpoints. FOSG is unnecessary for defining those endpoints.
Every proposed extraction has a named owner, actual clients, and a migration
of callers rather than an extra layer of aliases.

**Concurrency**

The API inventory and bounded public-message experiment can run alongside
this refactor. Freeze the shared runtime interface only after R1's hostile
tests; upstream approval must not block learning whether the model is sound.

## R1. Define the smallest faithful message interaction

Implement a runtime-general model with a parameterized application transition.
Use existing probability and protocol machinery where appropriate. The native
event semantics owns all execution; its GameTheory adapter reuses that law.

Initial state and event surface:

- Raw messages with sender-local identifiers and arbitrary payloads.
  Application destinations and encodings can be carried in the payload.
- Recipient-local delivered views and sender receipts; submission does not
  imply delivery to anyone else.
- A pending-message inventory separate from accepted application state.
- Submission, recipient-local delivery, and public inclusion of an existing
  pending message. Inclusion does not invoke its sender's policy. Start with
  a shared published ledger; delayed block receipt is a later refinement.
- Missing-message lookup has an explicit failure result. Application
  validation, withholding policies, clocks, and resolution drivers are
  separate additions when the positive compiler slice requires them.
- Principal-indexed controls. A principal may have several capabilities;
  environmental policies are explicit, and equilibrium concerns the chosen
  game-player principals.
- Explicit finite resource parameters for the first experiments, without
  making finite state or termination fields of the general runtime carrier.

No privacy assumption is attached to the message pool. An event's recipient
projection determines the signal; prove that unrelated hidden state cannot
affect that signal. Unobserved events leave local information unchanged.
Do not append a hidden global step counter or silently broadcast the clock.

The first bounded scripts use enumerated principals and a finite raw payload
alphabet containing malformed inputs. Do not impose globally finite state on
the kernel or add clocks and fees to obtain a finite test. When a theorem
actually requires finite strategy sites, prove a finite reachable cover for
the fields present, including sender-local serials. Bounded event count alone
does not establish that cover for arbitrary payload or information carriers.

Use the design's player-only game family: bundle capabilities by principal,
fix local policies for external principals, and assemble them with the player
profile for the native runner. Policies receive only their native local views.
Use `InformationModel` where its activation and menu interface fits; a direct
`GameForm` interpretation carries the same locality obligation. Public message
inclusion itself creates no hidden sender-activation problem.

**Required hostile tests**

| Test | Required evidence |
| --- | --- |
| A message reaches A but not B | Distinct local views; B cannot distinguish it from non-delivery unless another modeled event informs B. |
| One extra undelivered event | No new information, event count, or clock tick for an uninformed principal. |
| Inclusion of an existing message | The scheduler publishes it without obtaining another action from the sender. |
| Public malformed or duplicate input | Still a possible controller action; execution produces the specified failure and observations. |
| Failed/reverted execution after delivery | The recipient retains what it learned despite unchanged application state. |
| Two messages with different inclusion orders | Both operational traces exist and expose exactly their declared local effects. |
| One actor controls player and builder capabilities | A single principal deviation can change both. |
| A run reaches the test horizon without settlement | The result remains pending, not source quitting or successful completion. |

Compare the operational model and adapter on these executions. Finite testing
fuel must not create a fictional observed terminal event. Application-specific
tests enter with their corresponding layers, rather than expanding the first
pool carrier with unused capabilities.

The first commitment experiment must also admit cleartext submission and
show that inspecting it can reveal a protected value. For compiled traffic,
prove prefix observation equivalence under an explicit ideal service, accepted
opening consistency, and successful opening traces for distinct values.
No forced opening or settlement guarantee follows from these properties.

**Gate**

Executable traces, observation/noninterference lemmas, and a derived game form
all describe this same model. The adapter does not reduce the native adversary
space to satisfy its typing requirements. This gate does not claim source
preservation or a complete ledger.

## R2. Compile a checked core program into that model

**Implemented execution and bounded hiding slices; gate still open**

`SealedFragment.compile` emits a homogeneous unrestricted-commit/reveal
application from actual graph metadata. `SealedFragment.step_refines` and
`run_refines` cover every finite raw native action sequence, and
`WFProgram.sealed_run_source` reconstructs a written-order source execution
with matching terminal bindings and decoded payout evaluation whenever its
decoded graph prefix is terminal.
The `PendingSource`/`PendingExecution` fixtures exercise this compiler path,
including nullable values, opaque pending traffic, graph-derived opening
barriers, and both commitment inclusion orders.
`PendingOutcome` checks completed graph outcomes against native execution for
every nullable input pair and instantiates the terminal source-execution theorem.
The executable fixture uses checked elaboration-time
specialization of the source compiler; a standalone extracted emitter remains
an additional implementation obligation.

`PendingReplay` exercises unchanged-envelope rebroadcast by another player,
duplicate inclusion, and a rejected opening that becomes valid after its
prerequisites complete. Native run refinement covers these actions.
At-most-once application execution holds independently of traffic duplication;
it does not erase the extra public traffic or promise cross-instance isolation.

`SealedProgram.messageApplication` uses the shared bounded policy runner with
principal-scoped controls, polling memories, arbitrary replay, and public
receipts. Its ideal pre-disclosure hiding theorem permits adaptive opponent
and wire-observing environment policies; safe validation gives the same
acceptance and rejection receipts for paired secret values. The finite
invocation list remains fixed. `PendingPolicies` handles continuations without
owner invocations and retains a distinguishing cleartext response on this model.
`PendingRelease` supplies the owner's register/submit/open reference policy from
empty on the same receipt-bearing policy interface and permits further owner
invocations. It compares the first public
release-enabled snapshot of each full native trace; execution continues after
that snapshot. The generic reference-policy theorem checks all graph
prerequisites before submitting an opening. The release readout is not a
different stopped runtime or conditioning on successful release.
`WFProgram.sealed_policy_source` transports native source-support correctness
to every supported shared policy-game execution, retaining receipts in policy
observations while erasing them for source decoding.

`PendingChoiceLock` identifies the opponent's extracted release-time value
with its compiled source field, proves its law independent of the honest
input, and carries that value through later execution and any accepted
opening. Unreached release remains a separate outcome marker.
`PendingWithholdingSource` proves a concrete publication-law obstruction
against every independent source profile: the bound opponent can selectively
withhold after learning the honest opening, while every terminal source result
contains its public binding. A canonical reference-policy continuation succeeds
at
the same reached prefix and service horizon. This is an obstruction for the
specified publication readout, not a universal failure of weaker comparisons.

These comparisons do not complete the gate. The next compiler theorem must
compare unilateral replacements with source policies across the whole
interaction, including post-release behavior, and
account for withheld openings and observable failure. The untimed sealed-message
application has no timeout transition; its timed extension below does not
convert pending execution to source quitting.
General asynchronous activation and player-owned network/builder capabilities
also remain outside the fixed-invocation instance; the precise scope is in
the [runtime inventory](runtime-models.md).

The [timeout compilation design](timeout-compilation.md) specifies the next
component integration. A checked dependency gate exposes the shared mutable
timer's within-call interference and proves progress for immutable deadlines.
Atomic inclusion preserves public messages and prior deliveries when the
application rejects. `SealedTimeout` integrates the original sealed-message
validator with a permissionless expiration call at one named disclosure
checkpoint, a public monotone clock, receipts, and a native bounded policy
game. Its chosen failure policy stops further protocol-event acceptance; it neither assigns
a source value nor implements the richer source's persistent role-specific
abandonment and handler semantics. This real runtime instance still needs
the source-resolution and whole-interaction strategic comparisons.

`WFProgram.sealed_timeout_run_source` and `sealed_timeout_message_policy_source`
extend the reachable-prefix/source-support result over timed native execution
and its policy game. Terminal decoded graph prefixes reconstruct source
bindings and payout evaluation; checkpoint completion or expiration alone
does not imply source termination. These theorems do not erase the extra
information in traffic, receipts, or clock observations.

Before a terminal-law claim, implement and analyze resolution rather than
defaulting unfinished traces to source values in a readout. Preserve the
already-bound choice and distinguish later withholding from an earlier
nullable decline. Choose a source/backend eligibility condition or weaker
strategic comparison that accounts for that difference; adding a deadline
alone does not prove its adequacy. Utility-dependent quitting conditions and
explicit source continuation choices are candidate proof routes, with distinct
claims. Neither requires extending the minimal source syntax speculatively.

The persistent-quitting source gate has an executable two-checkpoint probe:
existing guards eliminate later freedom, and `PublicForcedChoice` proves that
a publicly determined source choice can be selected without consulting its
owner's current policy. The actual written-order source law is checked in
`PersistentDisclosureSource`, including arbitrary whole-program profiles.
This does not complete runtime resolution. `CommitmentAccounting` admits the
retained binding through its certified conditional-publication site. Generated
conditional instructions preserve its same-owner typed identity and validate
later openings against the retained snapshot and source guard. Owner-independent
execution of forced steps with correct observations and whole-program strategy
correspondence remain obligations beyond accounting and these local mechanisms.

The conditional-publication compiler component supplies the local resolution
edge: generated metadata, source/validator correspondence in both directions,
and execution by the actual paired graph kernels. Structural application plans
integrate these instructions, with arbitrary-traffic support refinement and
source public-outcome witnesses for completed executions. Structural source-profile
lifting supplies reference runtime strategies. Its exact randomized law under
the generated serial reference service now covers every eligible plan and source
profile, including completion and the public terminal readout. The next
strategic gate still compares arbitrary target deviations under the stated
service class; the reference law alone does not discharge that comparison.

Conditional endpoint generation is independent of the original binding's
accounting discharge. `ConditionalPublicationSite` combines an adjacent
public-choice occurrence with its opening-or-decline certificate;
`ApplicationPlan.conditionalCopy` uses it for an ordinarily accounted later
copy. The native update preserves the original accepted handle and frozen
snapshot. `GeneratedPersistentDisclosure` supplies the ten-node derivation,
an exact opening execution law from empty-pool initialization, a check that
decline blocks later opening, and completed-run source public-outcome witnesses.
`ApplicationImageReadout` reconstructs the full declared choice footprint from
public memory and private registration history. Its graph/source correspondence
requires cached originals to match their accepted snapshots; compiled source
occurrences supply the typed field metadata. Earlier paired choices come from
their resolved public values, not cached attempted requests: an opening overtaken
by expiration can leave an intended `some value` in history while the accepted
transaction represents `none`.

`GeneratedPersistentDisclosureController` instantiates that readout and the
conditional reference-policy combinator at the second site. The local laws
recover the arbitrary randomized source decision at the concrete opened and declined native
checkpoints, under the original-registration and empty-second-cache premises.
They also check endpoint separation and waiting after a recorded second choice.
These local laws take supplied histories; the separate forward-checkpoint
induction establishes their histories and checkpoints in the generated serial
reference run.

The forward composition establishes private registration before binding
acceptance, then maintains cache/snapshot correspondence and availability of
every source-visible field. Acceptance of an unprepared handle followed by
registration remains permitted operationally and does not satisfy that
reference invariant.
`ApplicationImageRegistration` supplies the unconditional history/preparation
invariant and preservation of an already cached-and-bound snapshot under all
later policy commands. `BindingImageController` and `BindingImageExecution`
construct the two-phase reference policy and prove the full law of consecutive
registration and submission invocations. `ApplicationImageBindingInclusion`
connects actual recorded inclusion to the cached snapshot. The initialized
`GeneratedBindingPolicy` prefix has the exact arbitrary randomized source
snapshot law and a draw-independent environment observation under its specified
inclusion script. `ApplicationPlan.liftProfile` supplies structural source-order
dispatch in the full image, and `ApplicationPolicyLocality` proves coordinatewise
dependence on source policies. `GeneratedApplicationPolicy` composes the binding,
the forced marker, and chance under that same lifted whole-source profile, with
successful inclusions and an exact six-invocation joint law. These are reference
strategies for the open protocol, not generated player software.
`ApplicationPolicyProvenance` establishes the cache/snapshot component generally:
if one player follows the lift, every
accepted handle belonging to it retains its first private registration, under
arbitrary opponents, environment, and finite invocation list. It also supplies
cache existence and graph-field type agreement for accepted bindings.
`ApplicationImageCoverage` proves that completed event fields have stored data
or accepted canonical handles under arbitrary policies. `SourceReadoutAvailability`
combines these execution invariants with native refinement and graph readiness:
the lifted owner can load the complete choice footprint, provided its initial
fields are public. The loader receives no source environment. Sealed initial-input
provisioning remains separate. The forward checkpoint supplies the proof-only
source environment whose view the readout reconstructs, while policies still
receive only native histories and observations.

The exact-law induction uses `ApplicationPlan.ForwardCheckpoint`, retaining the
original plan/profile, its structural suffix, `CoupledAt`, native refinement,
membership in the actual initialized policy run, service-index alignment,
remaining-cache freshness, and the accepted-binding prefix. Coverage, typed
registration provenance, and fresh envelope identifiers follow from run
membership rather than becoming inputs to a second evaluator.
`ApplicationSampleExecution` supplies the source-coupled native chance phase.
`PublicChoiceImageExecution` supplies the source-kernel submission/inclusion law,
and `PublicChoiceSourceCoupling` advances the exact source continuation through
the actual public-choice handler. `BindingSourceCoupling` and
`ConditionalSourceCoupling` supply the corresponding actual-inclusion continuations:
a prepared binding adds its chosen source value, and an opening or decline adds
the chosen optional value and its publication. Readiness follows from the
completed source prefix. The conditional endpoint additionally needs an accepted
binding identity; only opening needs a recoverable frozen value.

`ApplicationBindingOrigins` gives a decidable metadata condition for those
identities: each commitment-backed conditional instruction has an earlier
binding with the matching field, owner, and slot. This is not enforced by the
`ApplicationPlan` index and does not imply that the earlier binding was included.
In particular, publishing a source field through `publicChoice` does not create
a commitment handle. The reference realization theorem therefore consumes a
binding-origin certificate; another backend could instead select a different
representation for already-public values. This is a backend condition, not a
source-WF restriction.
`PublicConditionalOrigin` checks the distinction on a valid source and generated
plan, not just a hand-written image: the first public inclusion stores the value,
but the later commitment-backed endpoint has no accepted handle.

`ApplicationPhaseCaches` lifts codec separation through each full phase;
`ProfileContinuation` keeps the original lifted profile installed while moving
to its `afterSample`, `afterCommit`, and `afterReveal` suffixes. The binding,
public-choice, and conditional phase laws join source kernels to actual
submission and inclusion on complete policy executions. Structural induction
then derives the joint terminal distribution, rather than merely collecting
unrelated per-phase support witnesses.

What remains is the strategic edge: compare arbitrary player replacements and
admitted adaptive environment policies against this reference execution, using
the same opponents and external policy on both sides. The serial witness is not
a fairness contract and does not resolve withholding, retries, or competing
expiry under deviations.

The checked forward theorem uses a serial service under which a competing
expiration does not resolve an endpoint before its chosen owner request is
included. Clock advancement alone
does not reject an opening: the handler accepts it after the deadline if the
endpoint remains unresolved. Arbitrary withholding and resolution service need
their own whole-interaction argument; the forward service script must not be
presented as covering those deviations. Initially sealed owner-visible inputs
also require provisioning beyond the current public-only initializer.

Ordinary adjacent choice/reveal sites have a corresponding local component:
`PublicChoiceSite` derives metadata and guard code from `SourceDecisionSite`,
and the shared `PublicChoice` endpoint performs authentication, readiness, and
validation. The disclosure response handler directly instantiates it, with
checked local source steps and equality of the decoded native and graph
updates. Validation uses only actual guard dependencies, whose publicness and
native store agreement are separate obligations. `PublicChoiceSite.controller`,
used by the proof-level strategy lift, adapts arbitrary source decision kernels
to a shared sample-once controller, with an exact first-submission law at matching
source observations. Its first
real submission records the draw in own command history; subsequent polls can
wait or retry that value. Disclosure's reference native responder policy uses
this component, and its first ready invocation records the source response law. The existing
deterministic settlement guarantees remain checked specializations.
The shared sample-once mechanism also handles private registration commands.
Choice encodings enforce canonicality; endpoint tags separately establish
disjoint decoding and dispatch. `ConditionalOpeningController` composes the
certified source value equivalence with addressed opening/decline requests and
proves their local source law and acceptance conditions. The concrete disclosure
reference owner strategy composes source-profile-derived private registration,
opaque binding submission, and this addressed opening policy. It retains the
initial value in its own
command history, reconstructs the opening view from that cache or an accepted
public default, and reconstructs the complete declared source view. Native routing admits
wrong-tag raw messages and rejects their application effect. The complete pure
benchmark and initialized service proofs use this assembly, with all three
strategic kernels projected from the written source profile.
The application-plan forward theorem supplies the randomized reference-profile
law under `serialService`. The public-runtime strategic comparison remains open:
that law does not establish intermediate-observation equivalence for arbitrary
target deviations.

Generated chance instructions use the exact `EventDist.eval` kernel, with an
address-only environment command and no reroll after completion. This assumes
ideal unbiased entropy, to be realized by a separate target edge.
Conditional endpoints are certified independently of whether a site performs
the unique accounting discharge. Their private guard dependencies prevent
treating later optional copies as ordinary publicly validated choices. The
persistent-disclosure instance exercises the generated repeated endpoints and
whole-run support invariant. When its initial-read and binding-origin
certificates are supplied, the general forward theorem covers its structurally
lifted randomized profile through both disclosure sites.
Initial sealed-input provisioning/defaults and automatic execution of publicly
forced choices remain additional gates, not assumptions supplied by accounting.

`MessageApplication` supplies the common receipt-bearing execution and
observation-local policy boundary, with fixed application chance kernels.
The timed sealed instance has exact state/action/observation/run correspondence,
and its shared policy game retains checked source-prefix support. A separately
specified lottery exercises the same machinery without Vegas imports. These
clients establish runtime reuse, not the full non-Vegas strategic comparison
required by R3.

The timed sealed model uses `MessageApplicationPolicies` directly, including
the source-prefix theorem, binding persistence, and the policy-level
opening/expiry race regressions. Its raw timed step/run remains a reference
semantics used in model-specific proofs; its correspondence to the shared
native runner is exact.

The untimed instance uses the same policy runner for source support,
owner-polling release-time hiding, and binding persistence, with receipts
exposed and replay unrestricted. `MessageApplicationPolicyTrace` records every
invocation, including waits and intermediate policy histories. Its final-state
projection has exactly the `runPolicies` law. Its release split identifies
both an actual prefix and the supported continuation of the same execution.
`PendingRelease`, `PendingChoiceLock`, and the concrete release examples use
this shared instrumentation; post-release execution remains part of the game.
Receipt erasure is used only for source decoding, not as a claim of unrestricted
game equivalence. General public-message deviation simulation and migration of
the retained EVM backend remain separate requirements.

Integrate conditional publication and source continuation through this shared
application boundary. Do not add a separate optional-disclosure runner or
policy evaluator. Chance triggers must invoke the source's fixed law, check
readiness, and prevent rerolling; environment control of their timing does not
give it control of their sampled value. For every potentially silent source
decision, supply an executable legal fallback or preserve unresolved execution.
Uniqueness of a legal action is sufficient for one resolution technique, not a
necessary condition for implementing a designated fallback.
The lifted reference strategy must check disclosure fences before submitting an
opening, not only before its application effect is accepted: recipient delivery
can reveal the payload before inclusion. Retain the actual clock, receipts,
and local message histories in the policy game while proving the comparison.

The concrete `DisclosureApplication` specialization exercises these stages
through the shared runner, with an armed publication window and a continuation
after decline or expiry. Its all-policy invariant gives reachable decoded
prefixes, exact completion flags, and written-source support for completed
outcomes. The complete run from empty also has the independent AST's exact
terminal-environment law for pure source rules and a specified inclusion
script, with the retained secret included in the readout. This proves
settlement for those scripted compiled runs, not under arbitrary native policies
or service policies. Initial and response nonparticipation have source-correct
permissionless expiration handlers, with complete native execution laws for
an absent owner and an absent responder. Initial expiration records a public
default without changing private preparation. Concrete pure reference policies
drive these expirations and recover from public defaults. The slotted service
admits
player reactions after delivery and before inclusion, and its capacity theorem
drains the pool under arbitrary player policies. Under this service and a
positive window, initialized settlement and exact unchanged-player choices are
checked with either deterministic reference policy unchanged. This meets
the [operational integration gate](compilation-design.md#disclosure-integration-exit-gate).
Generate the public protocol application from checked programs and separately
construct and relate reference strategy lifts, keeping disclosure as a regression
instance. Randomized source-profile laws and
unilateral-deviation simulation belong at that reusable compilation edge and
remain unproved for the public service. The
[initial-default design](timeout-compilation.md#initial-defaults-and-privately-prepared-commitments)
separates unsubmitted private preparation, accepted binding, public defaults,
and permanently unopenable commitments. The instance accepts unopenable handles
without a validity signal and freezes their verifier at inclusion. Arbitrary
native continuations cannot repair them; a checked failed-opening/expiration
execution reaches the responder and retains the failed traffic. Creation-time
cryptographic binding remains a realization obligation. The whole-interaction
strategic comparison is still required to complete the strategic gate.

Choose a finite checked core program with two real players, source-defined
nonresponse outcomes, and a later decision that can expose an information
mistake. The pending-commitment experiment motivates a sealed-choice slice:
public handles precede source-authorized disclosure, and opening packets carry
their claimed values while pending. Choose the exact admitted source program
before adding a general protocol/phase language; the independent one-slot
experiment is not such a program and does not discharge this gate.

Prove the release discipline from the reference strategy and generated protocol
application.
Source textual order alone does not imply that both parties' choices become
irrevocable before either opening packet can be observed. An owner/slot binding
check must reject handles used for a different owner/node and replacement after
acceptance, while raw copying and malformed submissions remain possible. A
rebroadcast retaining its original author and context need not be rejected
before its first successful execution. Private registration with
an ideal service is explicit; unrestricted access to its hidden table or
verification oracle is not an admitted opponent capability. Concrete
cryptographic realization is a further compiler edge, not part of this slice.

Provide an actual `WFProgram` term using the existing constructors. Represent
nonresponse by a designated legal source value with explicit continuation and
payout semantics, for example `none` in an optional choice whose legality is
proved. The minimal core has no timeout constructor; the interface's timeout
action must select that value, not manufacture a new source branch.

Keep the concrete reference policy and generated application transition
available for execution. Prove their connection to the independent source game, not merely
to a new hand-defined runtime-aware game. Any graph-level example that does not
satisfy core admission must be labeled as such and cannot discharge this gate.

Use a named service instance, with nonzero delivery delay and at least two
admissible inclusion orders. A zero-cost instance is acceptable if explicit.
Give source timeout resolution a real transition and a reference policy or
environment driver. The
service assumptions must be feasible and must hold under all deviations in
the statement, including allowed spam and late submissions.

The first positive instance uses disjoint player and external builder/network
principals; fix that ownership map in its theorem. R1's combined-capability
test does not make this theorem cover player-owned builders. Use explicit
per-principal resource budgets and reserved service capacity for the initial
bounded inclusion instance. Define how over-quota traffic is rejected or
charged; it must not consume another principal's promised capacity silently.
These are model assumptions, not claims about Ethereum's service guarantees.

Prove settlement within the chosen bound for every admitted unilateral player
replacement and fixed adaptive environment satisfying the service contract.
Account for invisible withhold/wait events in the bound, not just successful
application steps. If this cannot be proved, the endpoint remains a
prefix/pending theorem and cannot be presented as an unconditional terminal law.

**Proof obligations**

1. The lifted reference strategy's requests and actions are executable and
   information-local; the strategy uses no hidden scheduler state. This is a
   proof obligation for the lift, not a claim that it is emitted client software.
2. Actual application execution and decoding agree with the source outcome
   interpretation on completed runs.
3. Extend the checked compiled-profile law under `serialService` only when a
   broader stated service supplies the required progress and resolution facts.
4. Analyze all target unilateral replacements at the same fixed environment
   policy, retaining other compiled principals. Prove a uniform translation,
   a precisely scoped mixture/quantitative statement, or a concrete obstruction.
5. Derive the corresponding source-outcome bound and equilibrium consequence
   only when the established relation supports them.

Include deliberate failure controls: censor a valid request past its cutoff;
expose information before another relevant choice is fixed; change a fee while
holding decoded settlement constant. State which guarantee each behavior
refutes and which assumption excludes it in the positive instance. Do not
assume that every negative control refutes every solution concept.

**Gate**

One actual core-to-public-message compiler path has checked strategic evidence,
with full native-policy quantifiers for the property claimed. If exact law or
Nash preservation fails, record the necessary condition or weaker result.
Do not replace the source meaning or declare all failures equivalent to quit.
If the only result is an obstruction, choose and test a revised service
discipline, supported fragment, or useful weaker property in the same model.
Positive compiler composition and generalization in R3/R4 require an actual
proved comparison; a negative result does not supply that premise. Independent
runtime reuse can still proceed from R1.

## R3. Validate composition, extensibility, and independent reuse

Insert one useful intermediate representation in the working R2 path, such as
raw-envelope validation or an explicit inclusion/receipt layer. Do not create
a dummy wrapper solely to count a layer.

Prove both adjacent edges and recover the original end-to-end statement using
the relevant composition results. Check equality or semantic correspondence
of the final artifact, not just matching theorem types. Include one test in
which exposing new receipt information defeats an overly strong abstraction.
The gate names the exact comparison recovered; finite mixtures cannot stand
in for a uniform translator or a continuation/recommendation correspondence.

Build a second, directly specified non-Vegas protocol using the same runtime
and game adapter, for example a two-party escrow/release protocol with
competing requests. Prove an operational invariant and a strategic comparison
with the same generic machinery. It must compile without importing Vegas.

Enforce the exercised library boundaries in the import checker:

- no Vegas or ledger/VM dependencies in GameTheory;
- no Vegas or EVM dependencies in generic interaction/ledger semantics;
- no game-core dependencies in game-free runtime modules;
- no compiler imports in target-carrier definitions;
- no audit/test imports into production roots.

**Gate**

The new layer composes without rewriting unrelated semantic owners; the
non-Vegas client proves actual reuse. Add physical library targets only for
the modules exercised by these clients. Do not create empty package trees.

## R4. Generalize the supported compiler and information discipline

Generalize the concrete R2 construction only along the dimensions its proof
uses. State core eligibility separately from source well-formedness. The
compiler may reject an unsupported target/fragment pairing without weakening
the programmer's source discipline.

Exercise hidden selection and later disclosure using explicit ideal services.
Before using existing quitting results, relate the service's real public
events, validation, and retry rights to the source decision. Commitments need
explicit handling of invalid openings, copying/related commitments, selective
opening, and payload-dependent extra traffic. Hiding alone is insufficient.

For guards over sealed information, establish implementable validation or
identify the supported fragment. Deferred validation requires the right
source consequences; it must not silently add an invalid-value outcome.
A proof-of-validity service is a separate assumption, not part of ordinary
commitment functionality by default.

Prove arbitrary supported-program statements through the public-message model.
Keep uniform backtranslation, profile-local mixtures, coalition/context
results, and continuation-sensitive results distinct. A finite-domain
counterexample is useful but is not a general completeness classification.

**Gate**

A checked core eligibility theorem, generated target, source-to-target
strategic theorem, and substantive application all use the same semantics.
The runtime may still have explicit ideal services; no deployment claim follows.

## R5. Reconnect contract and EVM lowering to the shared runtime

Extract runtime-neutral and VM-specific semantics from the existing backend
according to dependency, not directory name. Keep Vegas expression/code
compilation and its instances in the Vegas backend integration.

Instantiate the application-execution port with the existing contract
transition, including authentication, validation, rejection/rollback, and
observable results. Then connect storage and wire encodings, oracle interaction,
and a complete generated-handler path to that same target. A single-invocation
contract interface is not a message-pool or ledger model.
Use the existing transition as the port definition or prove a direct
transition-law equivalence if representation requires an adapter; do not add
an independently maintained contract evaluator for the strategic proof.

Whole-handler simulation and independent validation of the EVM model remain
explicit requirements. Existing local instruction proofs can be reused but do
not discharge either automatically. Introduce gas, transfers, external calls,
and other effects as real observations/outcomes when claimed. Rerun strategic
comparisons rather than inheriting them from a state projection.

**Gate**

At least one generated path is related to the public-message execution and its
derived game. The public theorem lists remaining VM/service/crypto assumptions.
A later whole-backend result extends that same path, not a separate tower.

## R6. Add chain realization and quantitative/unbounded analyses

Add named ledger, dissemination, consensus/finality, and cryptographic
realizations as actual clients of the runtime interfaces. Intermediate layers
can be inserted wherever a proof needs them; the tower has no fixed level enum.

Retain observations across reorgs and distinguish dissemination, inclusion,
execution, and confirmation. Account for who can force or prevent a timeout
call and for the resources funding its inclusion. Arbitrary outside contracts
or shared principal roles require the corresponding context/deviation scope.

For probabilistic service failure, compare unconditional laws and derive
explicit utility/error budgets. Do not condition away adversarially selected
failures. Computational security requires a security parameter and efficient
adversaries/tests; do not identify it with exact equality or total variation.

Prefix results remain meaningful without termination. Infinite-path
probability, eventual settlement, and utilities of unresolved runs require
their own semantics and proofs. These are later extensions, not hidden
premises of the finite model.

**Gate**

Each additional result identifies the operational realization and discharges
or narrows an existing requirement. A complete Ethereum model can eventually
instantiate these interfaces only after proving its control, information,
execution, and service correspondence.

## Frontend and manuscript work

Kotlin owns the rich surface language and its handler elaboration. The
[frontend/core contract](compiler-boundary.md) specifies its separate checked
integration boundary. Frontend integration may proceed independently; it is
not a prerequisite to modeling public delivery of an already checked core
program.

Keep the paper written as one coherent account of the current results.
Synchronize formal endpoints, audit statements/pins, registry, and prose when
a result changes. Planned stages are never included in the proved tower.
Do not expand the paper with every architectural helper or elementary witness.

## Verification and handoff at every gate

- Run narrow Lean targets during development and the full default build with
  warnings treated as errors at integration.
- Keep axioms pinned for public claims; no placeholders or local option escapes.
- Run import/direction/cycle, source-option, documentation, and claim checks.
- Maintain executable positive/negative controls alongside general theorems.
- State what changed, the precise checked result, remaining requirements, and
  the next bounded task. Do not mark a gate complete for a conditional theorem
  whose advertised premises have not been supplied by the intended instance.
- Commit and push relevant repositories independently; do not mix generated
  manuscript artifacts or unrelated working-tree changes into commits.
