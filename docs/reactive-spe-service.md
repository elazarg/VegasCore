# A combined service contract for SPE

## Status and intended claim

This is the candidate contract for the positive reactive SPE argument.
An ideal service enforces submission authorization using public history;
a fixed calendar combines it with uniform, at-most-once inclusion. Its local
response laws are checked. Completion and the full SPE theorem remain open. The
[obstruction inventory](spe-obstructions.md) records the negative results that
motivate each component.

Fix the source interface, playerwise compiler, runtime, observation rule, and
service before choosing analysis utilities. The intended theorem preserves
behavioral SPE for utilities of original private types and public results, at
every proper native subgame. It must cover arbitrary earlier deviations and
arbitrary information-local continuation replacements.

Use the full commitment-forfeiture interface for the first positive theorem.
Omitting forfeiture is a separate source transformation with its own proof.
No equilibrium request changes the source game, and no service requirement
restricts the raw player response menu.

## Components and their responsibilities

| Component | Requirement | Evidence/boundary |
|---|---|---|
| Source history space | Admit irreversible binding failure at its actual decision point | Source interface is implemented; source/native continuation match remains open |
| Binding | A submitted handle's meaning is immutable | Checked reactive safety invariant |
| Submission authorization | An envelope can complete an event only if its predecessors completed before that envelope's original submission | Public-history enforcement and permanent exclusion checked; ledger certificate backend open |
| Author and event | Only the authenticated event owner can complete a strategic event | Checked handler property |
| Replay | Select distinct identifiers, exclude included identifiers, and include each identifier at most once, including rejected calls | Checked network/selector laws and reserved-service at-most-once theorem |
| Inclusion | Use uniform selection for the first candidate service; eligibility is independent of a fresh binding's hidden value | Authorized uniform calendar, exact response menu, and local regularity checked; downstream law open |
| Timing and opportunities | State the remaining activation and inclusion schedule; retain deadlines at continuation roots | Existing reserved service has completion proofs, but does not instantiate this combined contract |
| Information | Preserve partial foreign leaks and reactions; prescribed failed openings reveal no raw candidate | Observation and emission components checked; full reactive continuation law open |
| Recovery | Reconstruct actual accepted choices and original own intentions where justified | Recovery/reconstruction lemmas checked; global optimality open |

These requirements are propositions and implementation obligations on the
corresponding components. They are not independent semantic mode switches.

## Authorization at original submission

[ReactiveAuthorization.lean](../Interaction/ReactiveAuthorization.lean) locates
the first actual submission of an envelope identifier in its author's recall.
The entry records the pre-submission view and the exact emitted envelope.
Replay entries cannot become submission origins.

The checked facts are:

- Every freshly allocated identifier has no earlier origin, at every legal
  initialized history.
- Once an origin exists, it is unchanged along every legal continuation.
- A condition evaluated at that origin is consequently immutable for the
  envelope. Later dependency completion, replay, or private memory updates do
  not renew authorization.
- Under the acceptance contract, a packet unauthorized at its origin cannot
  later have a successful application effect.

The Vegas condition checks the event address and the public completion
identities in that original view. It is independent of hidden binding values,
opening contents, and private memory. A new submission after readiness obtains
authorization; it uses a fresh identifier. These facts are in
[the event adapter](../Vegas/Pending/ReactiveAuthorization.lean).

Private recall is used to **state and prove** the condition. It is not exposed
to the scheduler. The ideal public-history service reconstructs the needed
observation from its own recall; a ledger backend must provide verifiable
evidence with the same meaning.
The [authorization research note](dependency-authorized-submission.md) separates
this ideal condition from authentication, availability, finality, and latency
assumptions needed for a concrete ledger construction.

### Acceptance versus enforcement

The semantic contract quantifies over actual legal prefixes where the scheduler
has a remaining step. If a selected pending envelope has a successful application
effect, its original submission must satisfy the condition. It does not assert
that an authorized envelope is selected or accepted; progress is separate.

The existing Vegas handler checks execution readiness and has no authorization
certificate field. With that handler, a service satisfying the contract must
avoid selecting an unauthorized envelope when the handler would accept it.
A backend that includes such an envelope and rejects it at execution needs an
authorization-checking handler. The semantic predicate alone supplies neither
implementation. The public-history service described below uses filtering.
Authorized packets rejected by the existing handler still consume identifiers
under the at-most-once contract.

In particular, none of the existing reserved-service guarantees should be
read as an authorization theorem.

### An enforcing service using public history

[ReactiveSubmissionAudit.lean](../Interaction/ReactiveSubmissionAudit.lean)
proves exact reconstruction at every initialized legal prefix:

1. Activating a player records the public application observation and that
   player's next envelope serial in the scheduler's own history.
2. The private leak sample changes neither of those fields. Exactly one player
   response occurs before the scheduler can act again.
3. For a submitted identifier, the last activation with its author and serial
   therefore records its original submission observation.
4. Submission advances the serial. Later activations, replay, inclusion, and
   application changes cannot replace that record for the issued identifier.

The **last** matching activation matters: a player may stay silent before
dependencies complete and submit later. A fresh submission uses the later
observation. The theorem authenticates the exact payload against its first
submission entry, as well as reconstructing the observation.

[ReactiveAuthorizedService.lean](../Interaction/ReactiveAuthorizedService.lean)
uses this public check to monitor any scheduler. An unauthorized or unknown
inclusion becomes a wait consuming one service step. It creates no inclusion
or rejection receipt, and leaves the envelope pending. It imposes no restriction
on submissions, replay, activations, or the separate passive observation rule.
It preserves an underlying scheduler's at-most-once guarantee. It does **not**
preserve arbitrary liveness or incentive properties of that scheduler.

This is an ideal service with reliable public traffic history. It assumes that
the service knows the activation and original network submission order. It
does not assert that a miner can infer first submission time from an ordinary
transaction, that miners retain such a history, or that the history can be
verified on-chain. A certificate implementation remains a separate obligation.
No private recall or record of sampled leaks is supplied to the service.

## Authorization isolates each player's current event

There is a stronger checked fact than exclusion of the particular early-opening
example. [ReactiveAuthorizationProgress.lean](../Vegas/Pending/ReactiveAuthorizationProgress.lean)
proves, for every initialized legal history and every scheduler:

1. Every completion identity in an earlier submission view is in the current
   completion cut.
2. An authorized packet addressing an unfinished event therefore addresses a
   currently ready event.
3. Under the graph's information discipline, two distinct ready strategic events
   have different owners. Consequently, while a player has a ready event, any
   authorized packet of that player for an unfinished event it owns addresses
   **that same event**.

The third step uses the existing same-owner ordering theorem in
[CommutationRecall.lean](../Vegas/EventGraph/CommutationRecall.lean).
[Source lowering](../Vegas/Compile/EventGraphAssembly.lean) already supplies the
required information discipline through public-barrier ordering.

Thus the candidate repair does not require global serialization. Different
players' hidden commitments can remain ready concurrently. A player cannot
create an authorized packet for its own later blocked event; broadcasting raw
bytes for that event remains legal. A fresh packet cannot impersonate the owner
of a foreign event, and replay invariance addresses additional copies of
already pending foreign envelopes.

This isolates **executable proposals**. It does not prove that all effects of a
response are confined to one event: raw bytes can be observed, and a scheduler
can react to traffic. The complete continuation argument still has to account
for those effects.

## Authorized uniform calendar

[ReactiveUniformService.lean](../Interaction/ReactiveUniformService.lean)
implements a calendar of activation, selection, application, and wait steps.
Each selection filters by its fixed eligibility predicate, original-submission
authorization, and unpublished status, then draws uniformly over distinct
identifiers. An empty selection waits. The
[Vegas adapter](../Vegas/Pending/ReactiveDependencyService.lean) supplies the
dependency condition and event/owner predicate. Every such calendar satisfies
dependency authorization and at-most-once inclusion, for all player policies.

[ReactiveUniformResponse.lean](../Interaction/ReactiveUniformResponse.lean)
proves the exact local response law. Silence and every replay leave the menu
unchanged. A fresh submission either leaves it unchanged or inserts the newly
allocated identifier. Authorization does not make old candidates' eligibility
depend on the new response. Uniform insertion consequently gives the checked
regularity property, including empty old menus and unauthorized submissions.
The fresh-permission theorem separately ensures that packets submitted by an
active player are checked against its current public application observation.

Application validation may still reject an eligible packet. A calendar intended
for compilation must specify how rejection and timeout finish the event, with
usable owner opportunities and an actual completion bound. The calendar type
alone makes no such guarantee. A rejection or wait consumes its scheduled step;
it does not restart a deadline.

The [early-opening regression](../VegasTests/ReactiveDependencyService.lean)
instantiates a seven-step calendar and proves that the same contested prefix
is a proper canonical subgame root. It evaluates the full five remaining
rounds for the actual compiler and the exhibited early-opening deviation.
The compiler publishes 0 or 1 with equal probability; the deviation publishes
1. With success utilities 3 and 2 respectively, their values are 5/2 and 2.
Both continuations finish. This removes the exhibited improvement; it does
not establish optimality against all replacements or at all roots.

The calendar fixes opportunities independently of responses. Allow foreign activations,
partial observations, and reactions before the designated inclusion. A window
must either reserve a usable owner response before settlement or expose in its
continuation law why an existing pending distribution or failure is unavoidable.
Calling a reserved slot a usable response does not prove that its packet will
be accepted.

All inclusion steps in this calendar use the authorized uniform selector.
Installing a uniform draw only at a final reserved step would leave earlier
adaptive acceptance unconstrained. The existing reactive epoch service allows
adaptive network inclusion and uses latest-packet reserved selection; it is a
different service and retains its separate completion theorem.

Fixed windows are a stronger assumption than local inclusion regularity. They
are an initial construction to prove, not a claim about ordinary blockchain
scheduling. They may later be relaxed only with a proof that the remaining
activation, inclusion, and observation laws supply the same incentive guarantee.
The [inclusion assumption note](inclusion-assumptions.md) discusses non-collusion
and economic motivations separately from formal premises.

## Positive proof to assemble

The next obligation is an event continuation theorem. It must combine:

1. **Current candidates:** decode every retained eligible envelope, including
   source forfeiture and rejected calls, with a justified empty-menu outcome.
2. **All responses:** use the authorization isolation result, author checks,
   replay invariance, and fresh-identifier allocation to classify their effects
   on selection. Raw signaling effects still require the information argument.
3. **Actual future play:** prove the downstream kernel used by the local
   selection theorem, retaining remaining windows, deadlines, observations,
   types, and recall. It cannot be postulated separately for each chosen response.
4. **Recovery:** show the compiled continuation attains the required value,
   including repeated activations and accepted choices different from remembered
   ones. Initialized packet uniqueness alone is insufficient at off-path roots.
5. **Canonical roots:** connect every proper native root to proper source
   continuations with unchanged source opponents and information-local replacements.

The existing
[behavioral root-mixture transfer](../GameTheoryExtensions/Protocol/BehavioralContinuation.lean)
is a sufficient final theorem interface. Exact prescribed law matching can be
stronger than needed when recovery reuses a supported choice. A proof using
utility inequalities instead must establish its own transfer theorem; it must
not choose the recovery compiler after observing the utility.

A sequential example is useful for the first complete continuation proof, but
the service design should retain the per-player isolation property above and
allow concurrent foreign commitments. A full native SPE claim waits for this
composition and the actual source-to-graph-to-runtime map. Authorization and
selection lemmas alone are not that claim.
