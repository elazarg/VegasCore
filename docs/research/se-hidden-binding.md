# Hidden unusability: audit limitation, conditional simulation, SE obligation

## Decisive checked facts

An unusable binding is not publicly identifiable in general.
`VegasTests.UnusableBindingAudit.auditTrace_eq` compares actual reactive binding,
inclusion, granted revelation and withholding steps. Valid binding followed by
legal withholding and unusable binding followed by withholding have identical
public snapshots, including phase, input authors, pending packets and receipts.
Their private meanings remain different and fixed. `no_sound_detection` rules
out charging the latter while an audit is silent on the former.

That fact is **not** an SE impossibility. There is now a stronger positive result
than initial Nash simulation, in `Vegas/Source/ValueBindingContinuation.lean`:

- `bindValues_runFrom_publicOutcome_eq` repairs a pure continuation from any
  residual source configuration, preserving its registry, revelations and own
  action histories rather than resetting them.
- `exists_valueBinding_continuation_mixture` repairs every behavioral
  continuation, using one mixture for every configuration in a finite list.
- `exists_valueBinding_belief_mixture` preserves the joint law of any parameter
  of the starting configuration and the public result, for an arbitrary finite
  belief over configurations. The mixture is chosen before the hidden state.
- `exists_valueBinding_continuation_ge` gives a value-only continuation with
  conditional utility at least as high as the original continuation.
- `ValueBinding.admitted` makes every repaired policy legal under every existing
  commitment interface, including value-only admission.

These results cover the full existing source syntax: public chance, subsequent
bindings, deferred guards, disclosure, and withholding. They impose no equilibrium
or reachability premise on the starting belief. Opponents keep the same source
policies and observations. Utility may depend on persistent private parameters
and public results; it may not reward the hidden representation of a future
commitment that the repair deliberately changes.

The native prefix facts are checked in
`Vegas/Pending/ReactiveBindingObservation.lean`:
`reactiveBinding_network` equates the complete network after either private
meaning is fixed; `reactiveBinding_include_other_input` also preserves receipts
and every foreign player's actual recall/current input through inclusion;
`reactiveBinding_activation_other_input` preserves the law of passive reads
under the original observation rule. Initial correlations and previously known
foreign evidence are unrestricted. The owner's own observations need not agree.

`ReactiveHiddenResponse` proves that arbitrary opponent responses preserve the
entire vector of other players' inputs jointly, including forwarding and raw
evidence requests. `ReactiveHiddenEnvironment` couples passive samples and
deterministic clock, grant and expiry commands without deleting pending reads.
`Vegas.EventGraphRuntime.environmentStep_sample_hidden_congr` uses one common
public chance draw to preserve that vector; the sampling law depends only on
typed public reads, even if its declared footprint contains unused fields.
These are checked transition laws, not the stopped-prefix induction below.
`ReactiveHiddenInclusion` also preserves the joint frame through opaque binding
inclusion, withholding, and a valid opening of a binding whose value was not
repaired. Receipt equality follows from public acceptance tests; no additional
observer or second player is assumed. For opening, the unchanged accepted
candidate and stored value are explicit premises. An attempted opening of the
repaired unusable binding is deliberately outside that inclusion lemma.

The checked commit block is now connected to source compilation.
`reactiveBinding_reserved_config` executes the real atomic response followed by
the real reserved selector and obtains the exact graph completion and successful
receipt, for valid or failed binding choices. `reactiveBinding_initialized_config`
derives its local freshness and timing conditions from a first initialized
binding node and a positive deadline. In `Vegas/Game/BindingRepairBlock.lean`,
`reactive_commit_agrees` and `reactive_commit_history` preserve the compiler's
typed store and source-action-history decoding; `reactive_commit_repair` carries
the existing source `Patched` invariant through paired original/repaired blocks,
with unchanged deferred registry and revelation bookkeeping. The next inductive
obligation is to reconstruct retained opponent inputs and the repaired owner's
source view throughout later blocks, not merely to identify the binding output.

`reactiveBinding_reserved_hidden_congr` now proves the joint block law from
prefixes that already contain repairs: network, receipts, public state, service
recall, all nonowners' actual response recall and views, and the owner's remaining
fresh-slot predicate. `reactiveFreshSlot_congr` shows why the compiler continues
to allocate the same opaque handles: an unusable and an openable candidate are
both nonfresh. Inclusion consumes no further candidate. This argument does not
assume an unlimited finite response menu or an additional observing player.

`Vegas/Game/BindingRepairPrefix.lean` packages these facts as an invariant of
the existing source configurations and reactive executions. Its checked
`RepairedPrefix.initial` and `RepairedPrefix.commit` establish initialization
and preservation by an actual commitment block, including native persistent
inputs, typed store/history decoding and the whole opponent frame. The
`decisionView`, `owner_decisionView` and `foreign_decisionView` lemmas recover
the actual compiler-decoded source views. This is not a claim that the owner's
entire raw response history is already reconstructed, nor an induction through
arbitrary subsequent native play.

`Vegas/Pending/ReactiveBindingShadow.lean` supplies the next owner-local piece.
`BindingShadow.rememberCandidate_submit_view` reconstructs the original catalog
after real submissions, including absent or mistyped private opening material.
`rememberCompletion_observation` reconstructs the original private result and
typed own completion; `rememberCompletion_pending` proves that storing this
memory does not expose a field before inclusion. `BindingMemory.restoreRecall_submit`
restores original before-views and actions while taking the emitted envelope
from actual own recall. It does not predict network nonces.

`rawBinding_reserved_config` includes arbitrary private raw material, including
wrong-typed material, with its exact typed result and successful inclusion
receipt. `BindingMemory.repairResponse_include_input` composes the actual
submission and inclusion: the repaired implementation reconstructs the original
complete own input and response recall after both operations. Its memory update
still uses only the current own input and original response.
`BindingMemory.repairResponse_protected_input` carries this
through the actual reserved selector, arbitrary clock padding and expiry of the
already completed event. `rawBinding_reserved_hidden_congr` separately extends
the joint opponent-frame block law to arbitrary raw material on both sides,
including absent and mistyped material. The two results concern the same
deterministic protected block; they do not yet constitute the remaining-plan
induction or a stopped payoff comparison.

`ReactiveBindingFrame` now joins these components as a relation on the same
two actual executions. `Frame.binding` proves that response and
reserved inclusion preserve reconstructed own input, all opponents' views and
recall, network, service recall and allocation freshness together, for usable,
absent and mistyped private binding material. Its
`BindingMemory.Frame.activate` and `BindingMemory.Frame.foreign_response` cases preserve arbitrary passive samples and
arbitrary foreign raw responses. `ReactiveBindingFrameStep` closes clock,
grant and common public-completion constructors. `Frame.inputs` recovers the
entire equal initialized environment, including correlated private parameters.
The shadow's `CompletedAt` predicate records the additional boundary invariant
that private completion overrides concern past events. These are concrete
induction cases, not a claim that the remaining-plan or stopped payoff theorem
has already been assembled.

The frame also preserves every originally successful typed binding in the
actual native stores. The
[binding refinement](../../Vegas/EventGraph/BindingRefinement.lean) is stable
under the relevant typed completions. `Frame.successful_opening` uses it with
the two actual native binding invariants to derive the same accepted handle and
authentic opening value. The native recurrence therefore does not need to
reconstruct a second source interpreter to justify each successful opening.
It also preserves the event sequence of submitted openings in the owner's
actual recall. `Frame.firstOpening` transports the once-per-event response
condition through private binding repair; changing hidden binding material
cannot reset that condition.

`Vegas/Game/BindingRepairOpening.lean` closes the successful-opening provenance
gate. `Patched.success_kept` proves that an originally successful typed binding
is never replaced. `repaired_success_provenance` then derives the same accepted
handle and authentic candidate on both actual native sides from their checked
binding invariants and typed store agreement. This includes foreign owners and
correlated initial states. Preserving every raw openable candidate would be
incorrect: a mistyped original candidate can be openable as raw evidence while
its typed game binding is a failure. Publishing that raw evidence remains a
separate visible departure under the successful typed-opening rule.

`opening_submission` in `ReactiveBindingFrameOpening` includes both owned and
forwarded certificate requests. `BindingMemory.Frame.opening_inclusion` preserves the same actual
receipt and checked result; it does not identify acceptance with publication
success. `foreign_binding_inclusion` in `ReactiveBindingFrameForeign` covers other
players' fixed bindings, and `expire_resolution` in `ReactiveBindingFrameExpiry`
couples the actual due disclosure expiry independently of repaired meanings.

The probability statements use the existing evaluators.
`binding_response_coupling` in `ReactiveBindingFrameLaw` couples the original mixed
policy invocation with the actual private implementation response, followed by
the real reserved inclusion. Every supported pair satisfies the complete frame.
`run_transport_coupling` in `ReactiveBindingFrameRounds` proves a finite induction for
activation/wait windows, allowing arbitrary foreign responses and passive leak
samples while the repaired owner uses silence or replay. It retains private
recalls and scheduler input. This window theorem does not cover new owned
submissions; the binding and successful-opening constructor laws handle those
separately. Combining all constructors with clean checkpoint invariants and
first-departure evidence remains the full-source stopped-run obligation.

[`protected_binding_response_cases`](../../Vegas/Pending/ReactiveBindingStopped.lean)
classifies every bounded effective response at a required protected binding:
a canonical public packet with arbitrary hidden material; an actual signed
noncanonical packet; or a protected inclusion/expiry suffix with public
missed-binding evidence. The last case detects obligation failure from the
ledger and deadline, not from absence in a partial packet sample. The
[retained implementation coupling](../../Vegas/Pending/ReactiveBindingRetainedBlock.lean)
covers the first case using its actual compiled-menu implementation and proves
its off-path fallback unnecessary at that binding.

The [legal continuation theorem](../../Vegas/Pending/ReactiveBindingLegalContinuation.lean)
realizes the private repair as one actual retained continuation against the
unchanged target opponents. The
[implementation trace induction](../../Interaction/ReactiveMenuImplementation.lean)
keeps every intermediate repaired control in a legal retained history, so
checkpoint and classification facts apply throughout the continuation.

The [guarded response classification](../../Vegas/Pending/ReactiveGuardConformance.lean)
checks a claimed typed value against the recorded public guard inputs. An
accepted call with a matching certificate and successful public guards is the
canonical successful opening; the other cases are rejection, invalid certified
format, or publicly failed guards. The
[retained-response theorem](../../Vegas/Pending/ReactiveGuardedResponse.lean)
places the successful case in the actual compiled menu, including its raw
private request aliases. It requires the actual first-opening condition, which
the repair frame preserves. Hidden unusability remains outside the public
audit predicate.

These operational comparisons still need the stopped remaining-plan induction
and the original source conditional-assessment correspondence. In particular,
an attempted guarded disclosure and withholding may have the same public
result while remaining distinct in source own-action recall. The source proof
must account for that difference when comparing continuation incentives.

`BindingShadow.OwnBindings` and `repairResponse_ownBindings` prove that these
overrides concern only the repaired owner's private bindings.
`BindingShadow.complete_unmodified_observation` therefore commutes with the same
actual completion outside the shadow on both sides, including other players'
bindings, chance results and successful, failed or withheld publications. It
does not substitute a public value from private memory.

`BindingMemory.implementation` is an actual private implementation using only
the current own input and this memory. Its reference memory is constant across
every hidden execution in the starting information set, and
`implementation_behavioral_continuation` realizes it as an ordinary behavioral
policy. It records each fresh owned binding uniformly and repairs only unusable
material with a fixed valid value; `repairResponse_usable` checks that a usable
binding's response remains unchanged.
[`repairResponse_submit_input`](../../Vegas/Pending/ReactiveBindingShadowStep.lean) connects this to
the actual pair of original/repaired atomic responses, with exact original own
input reconstruction after missing or mistyped private material.

`ReactiveCompiledMenu` supplies a finite response restriction for every existing
event-code constructor. Retained bindings are exactly typed successes;
`binding_value_compiled` retains every source value, and `compiled_binding_cases`
excludes silent fallback and public replay at covered, ready binding checkpoints.
`canonical_binding_response_cases` separates represented valid material from
unusable material under the same public canonical packet. The latter is a repair
case, not an audit violation. `finite_binding_values` verifies the substantive
finite-domain requirement instead of mistaking a finite wire alphabet for a
finite unbounded source type.

[`compiledPolicy`](../../Vegas/Pending/ReactiveBindingContinuation.lean) realizes the implementation
as an actual retained behavioral continuation. All-input admissibility is
proved: an excluded proposed output is replaced by a fixed locally legal output.
`repairResponse_compiled` proves that canonical hidden unusability uses its valid
repair rather than that fallback. `compiledImplementation_continuation` fixes
one initial private memory uniformly across the starting information set.
The remaining obligation is the stopped-run payoff comparison: exact coupling
before excluded traffic, and actual collectible evidence for a first departure.

`ReactiveBindingAllocation` connects canonical handles to a public counter.
`State.PreparedPrefix.freshSlot` identifies the actual next prepared serial with
the owner's completed-binding count. `rawBinding_reserved_preparedPrefix`
preserves this invariant through actual submission and reserved inclusion,
whether the private material is valid, absent, or mistyped. The initial
invariant is checked. `rawBinding_reserved_all_preparedPrefix`
preserves every player's allocation invariant through the binding block,
including owners other than the current actor. `State.PreparedPrefix.complete_public`
preserves it through chance and publication completions. Assembly across the
actual service remains part of the full induction; the auditor is not given a
private catalog or a claimed freshness oracle.

`binding_response_cases` exhausts all effective
bounded responses at a clean required binding opportunity: a retained typed
value, a canonical opaque packet with unusable private material, a different
emitted packet, or silence/spent replay. It uses the actual post-submission
certificate resolution and physical known-message list. Normalized ownership
and forwarding requests cannot conceal an additional effective certificate
under the same canonical packet. The public check therefore compares only the
event, sender, public-count handle, and absence of a certificate; it never tests
private material validity.

## Finite admission and clean-prefix contract

A nonvacuous finite SE theorem for fresh commitments needs finite legal source
payload domains, not merely finite target packet bounds. Boolean, enum and
bounded-word payloads can satisfy this without changing the source constructs.
In particular, a full
integer commitment menu has no fully mixed finite-support behavioral law under
the current `FinDist` assessment definition. A theorem quantified over source
SEs must not conceal that absence. The finite admission must retain every legal
source value and every legal withholding action; it is fixed before the source
equilibrium is chosen. The target capacity includes these values, one repair
default in each nonempty admitted domain, and fresh canonical handles for every
remaining source binding site. The program's finite event count bounds those
handles. No default depends on the unobserved state of an opponent.

At the starting retained prefix, runtime/source stores agree except for the
owner-private bindings explicitly tracked by `Patched`. Public data, other
players' private cells, accepted handles, completion order, network state,
receipts, and other players' response recall agree. Candidate meanings are fixed
at transmission. Earlier pending and known packets must already be accounted
for by the retained transcript. A preexisting raw opening of the repaired handle
is not harmless: it may reject on the unusable side and succeed on the valid
side. Such a packet belongs to the observable-departure branch below.

The service assumptions must be proved for each compiled construct. The checked
revelation service does not already supply a full-language binding/chance
calendar or an arbitrary ambient-communication schedule. The ordinary target
message space remains available; admission bounds and protected opportunities
are explicit backend assumptions, not exclusions justified by an equilibrium.

At a value-only binding, sending no commitment differs from submitting an opaque
unusable handle. Silence or public replay can miss the binding obligation;
neither is retained as a source value choice. Collection then needs public
evidence of the missed mandatory binding deadline under protected timely
inclusion. The absence of a watcher record is not such evidence. A grant that
designates one required binding response is a sufficient backend discipline;
earlier ambient waiting must remain legal. This does not yet establish fresh
binding preservation under repeated owner visits within the same granted phase.

The actual omission block is checked in `ReactiveBindingDeadline` and
`silent_or_spent_binding_omission`: after the
required response, reserved inclusion skips already published replays, the
specified clock steps reach the deadline, and expiry records `missedBinding`.
That evidence persists under arbitrary later native responses and scheduling.
This establishes the operational case, not a complete collected-penalty or SE
comparison for the full source language.

## Why the repair is local enough, and why the current comparator is too strong

At the start of a continuation, replace any future failed binding with a
canonical valid value. At that binding's later disclosure, withhold instead.
The existing `Patched` invariant reconstructs the deviator's original view and
own actions; every other player's view and own history stays unchanged.
`bindValues_publicOutcome_eq` already proves this for arbitrary related residual
configurations, not only for initial execution.

The transformation edits a whole future policy. It is local to a continuation
and uniform across its hidden states, but it is not a replacement of only the
current action followed by unchanged play. In particular, replacing a failed
binding with a valid value and then leaving a later opening unchanged can alter
the public result. Failure of that one-action comparator is not strategic gain.

Sequential rationality already compares every whole continuation policy. The
checked `ActionRestriction.sequential_equilibrium_extends_of_continuation`
therefore allows an extra target action's future
behavior to be simulated by a mixture of whole source continuation policies,
instead of requiring one legal source action with the old continuation unchanged.
Every mixture component is bounded by source sequential rationality. The theorem
accepts a comparator chosen for the whole posterior, uniformly over its hidden
histories, and quantifies over arbitrary paired profiles without assuming target
rationality.

## Exact remaining native obligations

### Guard-failing source disclosures

Full-source correspondence has a second obligation besides repairing unusable
target bindings. A source disclosure can fail a deferred guard. The compiler's
`reactiveResolutionPacket` then withholds instead of publishing a certificate
that would expose a value hidden by the source failure result. Both source
choices have the same resulting store, registry and revelation bookkeeping,
but their owner's source action memories differ.

The existing `prescribedReactiveImplementation` retains this intention inside
the strategy, and behavioral realization conditions it on actual own recall.
That supplies execution machinery. It does not yet prove that every source SE
survives the aggregation of these private action aliases. The general theorem
must establish the corresponding posterior and continuation-value aggregation;
it must not silently assume every guard succeeds. The guarded source language
needs no extra public failure payload to state this obligation.

An outcome-preserving action transformation alone is insufficient justification:
[Clark, Fudenberg and He, Section 3.2, Figure 4](https://kevinhe.net/papers/induction.pdf)
give games with the same reduced normal form whose sequential-equilibrium
outcome sets differ after splitting a decision. Their example is a warning
against that general inference, not a counterexample to this particular
private-alias elimination.

### Native continuation repair

The conditional source result does not yet prove native SE preservation. The
native adapter must establish the following facts, rather than assume them:

1. From a retained native prefix, a privately unusable binding and the repaired
   source continuation give every **other** player corresponding future views.
   This includes accepted handles, response recall, pending observations and
   deferred-guard effects. The sender's own extra private information is mapped,
   not incorrectly identified with the source information state.
2. Opponents' prescribed policies must continue to agree at those corresponding
   views after the hidden departure. Agreement merely on the originally
   embedded execution histories is insufficient by itself.
3. A later observable departure is handled by the audit/collection argument.
   The conditional source simulation does not cover arbitrary leaked certificates,
   new public signaling, or arbitrary native opponents after such traffic.
4. New private information sites need rational continuations in one common
   consistency construction. Existing action-restriction completion supplies
   that mechanism only after its structural embedding and retained-belief
   hypotheses are actually instantiated.

The generic restriction proof now combines whole-continuation comparison with
its checked consistency completion and one-shot-to-whole-policy machinery.
This closes the generic comparison interface; it does not discharge native
obligations 1–3 or establish a completed full-language SE theorem.

## Stopped-path proof design

The target comparison is universal over paired source/target continuation
profiles; it must not assume target sequential rationality.

1. Repair inside the retained native game using the existing private
   `Implementation` interface. Initialize its memory from the fixed own input
   at the information set; never from the hidden execution. Restore the original
   owner's candidate meanings, private completions and raw response recall from
   that memory and the current own input. Behavioral realization produces one
   policy uniformly over the posterior. The source `Patched` and conditional
   mixture results justify the underlying value/withholding repair; they do not
   require a new encoder from arbitrary raw histories into source views.
2. Couple the original and repaired native execution until the first publicly
   nonconforming transmission. A privately unusable binding does not stop this
   coupling. Its repaired value uses the same opaque handle, and the repaired
   owner withholds when the original binding could not publish. Common public
   chance draws, passive samples, inclusion decisions and protected deadlines
   must preserve the coupled prefix invariant by actual runtime transition laws.
   The coupling preserves all opponents' inputs jointly with the persistent
   private parameters. Separate marginal equality for each opponent would not
   establish the required correlation claim. In particular, both sides use the
   same public chance draw, rather than independently matching its marginals.
3. At each nondeviating player's decision, prove its complete native input is a
   retained input. Then `ExtendsProfile`
   supplies its law. Equality of current ledger states alone is insufficient:
   private response recall, prior leaks and timing are part of that input.
4. If no visible departure occurs, the terminal private-parameter/public-result
   law is exactly the source repair law. Hidden owner representations are not
   required to match.
5. At a first visible departure, condition on the coupled prefix. A fresh
   collectible loss must cover the full remaining payoff range, uniformly over
   later policies and later authentic audit transcripts. This permits arbitrary
   post-departure target play. A penalty already sunk on that branch provides no
   further deterrence; charges are not silently counted twice.
6. Average over the starting posterior and the private implementation law. Retained whole-policy
   sequential rationality bounds every legal repair continuation. Only then use
   the common-consistency completion theorem for the native extra private sites.

Steps 2–3 are the missing native induction. The checked prefix lemmas and source
repair establish ingredients, not this induction or the final comparison.

## Missing required commitments

A missing accepted handle is a separate case from an accepted opaque handle
with unusable private material. The full-source retained menu requires a typed
value at its designated binding opportunity. Silence there cannot be justified
by an audit of emitted messages alone.

The enforcement interface must also consume the public completed-binding and
accepted-handle records. A completed binding with no accepted handle records a
missed requirement; an accepted handle must not be charged by this test merely
because its hidden meaning is unusable. The backend must prove that a timely
legal submission at the required opportunity is accepted before expiry. This
is a service/fair-inclusion obligation, not an inference from a missing partial
watcher record.

The local value-only menu uses an owned, ready public grant to identify the
required binding response. A backend with earlier owner visits must permit
waiting there or provide a separate continuation comparison. Deadline evidence
cannot punish every earlier silent response when a later timely submission
could still meet the obligation. The simplest candidate service places the
binding grant immediately before one protected required response; extending
fresh binding to arbitrary granted rosters remains separate work.

## Guards and copying

Deferred guard rejection is not an unavoidable honest disclosure in the current
compiler: `reactiveResolutionPacket` emits withholding when the proposed opening
does not publish successfully. A raw opening that still carries a rejected
secret is extra traffic and may be audited. The source repair preserves guard
results because guard reads use public data and revelation results; its existing
proof covers the whole obligation registry.

The full-source checker must therefore test successful guarded publication,
not just packet acceptance or certificate format: an accepted opening can still
complete with publication failure. The reveal-only checker is not a substitute
for this guard-sensitive obligation.

This introduces a separate source-to-retained-native proof obligation. When
source disclosure fails its guard, `true` and `false` have the same publication,
but retain different private `OwnAction` histories. The checked
`patched_reveal_own` permits exactly this difference and reconstructs the
original choice with a fixed `ViewMap.afterReveal`. The existing
`prescribedReactiveImplementation` also retains intentions internally, and
`Interaction.ReactiveApplication.Implementation.realize` converts such private
implementations into behavioral policies with the same execution law. These
facts do not by themselves prove that every source SE survives erasure of the
redundant private choice. Its beliefs and continuation values must be aggregated
using one common consistency sequence. The checked private-alias SE theorem
lifts a normalized game into a game with extra aliases; it is not a theorem
reflecting every alias-dependent equilibrium in the reverse direction. No
assumption that all guards pass may replace this missing argument.

There is also a raw-action case within binding repair. A commitment
can carry private material of the wrong type and still expose the same opaque
packet. Its typed binding result is failure, while its private catalog may
support a later certificate for that wrong-typed material. The checked native
submission/inclusion repair now covers this case and reconstructs its private
response records. The stopped induction must retain that information through
later choices until any nonconforming certificate transmission is handled as
an observable departure. Source `Patched` alone does not establish this native
continuation claim.

In the current ideal runtime, binding acceptance requires ownership of the
candidate handle; a third party cannot bind another player's opaque handle as
its own source commitment. Certificates may be forwarded once known. Copying a
publicly disclosed value is source-representable; additional private certificate
disclosure is an information-flow obligation for the audit adapter.

A cryptographic backend that permits copying an opaque commitment without
knowing its value requires a separate analysis or a knowledge/nonmalleability
assumption. The checked conditional repair concerns unusable binding in the
existing ideal semantics and does not establish preservation for that larger
cryptographic action space.

**Conclusion:** no forward-SE counterexample from hidden unusability has been
established. We have proved its lack of conditional source best-response gain.
The remaining issue is a native information/continuation simulation and its
consistent extension, not a demonstrated need to expose malformed commitment
values in the source language.
