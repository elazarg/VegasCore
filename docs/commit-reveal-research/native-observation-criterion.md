# A native observation criterion for serial commit–reveal execution

This is Codex's paper analysis of a candidate restricted game built from the
native runtime operations. It proposes no change to VegasCore's adopted model,
runtime, or checklist. The observation and SE results below are paper theorems;
the existing checked ingredients and the missing native adapter are identified
separately.

The useful positive case does not hide physical transmissions. At a new
logical decision, every earlier lawful plaintext opening already has a public
source result. Opaque commitment envelopes do not depend on their hidden
meanings. These two facts can make the entire physical observation history
have the same replay law across a source information set, even when the
scheduler and observation sampler inspect packet contents.

The important restriction is where a player can choose. Raw waiting
activations remain physical events with remembered observations; in the
restricted game they offer only silence. The result does not establish that
late submission, replacement, retransmission or voluntary disclosure is
unprofitable in the full raw game.

## Native operations relevant to the question

The application separates the submission's private opening material from its
public packet. A binding submission can prepare a candidate's private meaning,
but the transmitted packet is a commitment naming an event and a handle.
`Submission.register_facts` proves that registration preserves the public
application view. The checked `reactiveBinding_network` result proves that
changing the submitted binding meaning leaves the entire network unchanged.
Its foreign-observation companions preserve actual foreign recall and passive
packet observations, rather than removing the packet.

An opening packet carries its event, handle, plaintext value, authentic opening
evidence and readiness token. The token is attached from the public contract
state; it names the event and carries no creation time. It certifies completed
prerequisites. It does not conceal a premature proof. Including a packet
appends its contents to the ledger even if handling rejects it.

The actual environment observation contains the pending and included public
packets, the submitted-envelope history, serial counters, public application
state and receipts. The scheduler also remembers its earlier environment
observations and commands. The passive sampler can inspect the entire pending
packet list. Its selected foreign packets become an observer's private
knowledge; that sample is not added to the environment observation. A player's
policy input retains its own response entries, application observation,
received packets, ledger and receipts. Thus equality of only the latest
receipt would be insufficient.

`Interaction.ReactiveObservation` proves that an activation's private sample
does not change the environment's next public observation, and that equal
native response inputs yield equal activation observation laws. These are
useful coupling steps. They do not by themselves imply that the observation
law is independent of a source-hidden value.

The source compiler's graph has public barriers, not merely data-read edges.
`barrierOrder_public_event` makes every earlier event a prerequisite of a later
public instruction; `barrierOrder_public_prior` keeps an earlier public
instruction before every later instruction. Thus an earlier binding cannot be
bypassed by a later public reveal, including in ordinary concurrent mode.
The sequential specialization adds every earlier source event as a
prerequisite, so exactly one unfinished event can be ready. The native
first-turn protection theorem derives protected admission at the owner's first
ready turn from the opportunity and deadline budget, independently of the
owner's chosen policy. These facts supply the control skeleton for the result
below.

Relevant checked surfaces are
[EventSubmission](../../Vegas/Pending/EventSubmission.lean),
[ReactiveBindingObservation](../../Vegas/Pending/ReactiveBindingObservation.lean),
[ReactiveObservation](../../Interaction/ReactiveObservation.lean),
[ReactiveCanonicalResolution](../../Vegas/Pending/ReactiveCanonicalResolution.lean),
[Sequential](../../Vegas/EventGraph/Sequential.lean), and
[SourceServiceFirstTurnOpportunity](../../Vegas/Game/SourceServiceFirstTurnOpportunity.lean).

## The source class and the restricted physical game

**Source model.** Fix a finite `SourceProgram` and its finite initialized game
with perfect recall. The instruction sequence and owners are public. Source
chance instructions depend on the source-public context. Initial private inputs
and bindings can be correlated, and they may remain private across many later
decisions. Supported initialized bindings are successful. Commitment admission
is value-only: at each commitment the owner chooses any admitted typed value,
not binding failure.

At every legal reveal prefix, TRUE successfully publishes its bound value and
FALSE publishes failure. Both choices remain legal, including at off-path
prefixes. A simple sufficient instance is successful bindings and no rejecting
guards. More generally the condition is that all admitted prefixes satisfy the
guard checks when TRUE is chosen. Terminal utility may depend on all source
publications and public chance outcomes, including withholding failures and
intrinsic forfeits.

This effectiveness condition is substantive. In the general source executor,
a rejected TRUE and FALSE have the same publication but different private own
action histories. The canonical native implementation sends nothing on both
routes. That broader case is discussed below; it is not silently included.

**Physical model for this result.** Use the native sequential graph, its
canonical fresh handles, private candidate registration, authentic opening
material, readiness tokens, ordinary public network, receipts, clocks,
environment commands and passive observation rule. Start with an empty network
and the fixed public assignment of initial handles. Candidate meanings are
private, immutable once fixed, and visible to their owner as in the native
application. No extra private candidate preparations occur.

At the owner's first ready response for an instruction, it chooses exactly one
of that instruction's source actions. A commitment value is registered and
sent in the canonical envelope; TRUE sends the canonical authentic opening;
FALSE sends nothing and remains silent until the instruction expires. Every
other activation has only the action silence. In particular the owner cannot
redraw its source choice after choosing FALSE. Own recall identifies the first
ready turn even when its response was silent.

The retained menu at that response is in bijection with the source menu.
Every admitted typed commitment value has its canonical legal registration
and envelope at the fresh binding-count slot; freshness follows from the
initialized handle assignment and earlier canonical admissions, rather than
from a secret-dependent fallback search. Every TRUE has the authentic opening
material for its immutable bound value and a readiness token, and FALSE has
its distinct source choice recorded in own recall. These coverage requirements
apply at every legal source prefix, including off-path prefixes. No source
action is lost because a native candidate or credential is missing.

The environment is an arbitrary finitely branching native public scheduler
satisfying the asynchronous opportunity, sole-packet protected inclusion,
deadline budget and finite-horizon completion contract for every legal play of
this restricted game. Its delays need not be uniform, independent between
events, or selected in advance. It can read its entire native public history
and current public packets. The passive rule is any finitely branching native
rule on the observer and pending packets. Private samples are remembered by
their recipient and remain absent from the scheduler's input.

The finite horizon bounds all physical waits. The first response is protected,
so every submitted canonical commitment or TRUE opening is included and
accepted before its deadline. FALSE expires as source failure. Public sampling
commands use the source chance kernel once, when their unique ready instruction
is sampled, without retrying an unfavorable draw. Conditional on every complete
physical past, that logical sample has the specified source law.

The payoff is the source payoff of the completed logical execution. There are
no extra fees, discounting, balance-dependent menus, capital costs, outside
trades or rewards for physical timing. No miner or committee is an additional
strategic player. These omissions delimit the theorem; they are not claims
that such effects are absent on a blockchain.

This is a restriction of native operations to a specified first-ready-once
interface. It is not an identification with the project's larger retained
risk menu or all raw actions. Source decisions may depend on every remembered
physical observation in the target; the theorem will construct an equilibrium
that ignores the auxiliary part, rather than prohibit that dependence.

## Paper theorem: full native replay laws are constant on source fibers

**Model for this result.** Use exactly the finite source class and restricted
native physical game above, with canonical envelopes, successful protected
admission, effective TRUE, sequential dependencies and unchanged logical
chance kernels. Retain every physically available observation and own response
entry.

Fix a source history h just before a source decision. Replay the physical
operations with only the source choices and chance outcomes in the prefix h
externally fixed. Stop at the first ready response for that decision, after
sampling its activation observations. Let Q_h be the resulting normalized law
of physical prefixes. The replay samples scheduler commands and private leak
draws; it neither selects an equilibrium nor conditions on future outcomes.
Let J_i be player i's full native response input, including its complete own
recall. Source perfect recall and the compiler decoding recover I_i(h) from
that input on these clean prefixes.

**Theorem, paper proof.** For every player i and two source decision histories
h,h' with I_i(h)=I_i(h'),

\[
 (Q_h\circ J_i^{-1})=(Q_{h'}\circ J_i^{-1}).             \tag{1}
\]

The equality includes physical timing, absence, message identifiers, earlier
private leak samples, receipts, candidate meanings visible to i and every
remembered response view. It holds for all legal source histories, not just
the histories of one selected policy. No payload-blind scheduler or uniform
waiting-time hypothesis is required.

**Proof.** Equal current source information identifies the same instruction,
the entire earlier source-public outcome history, and i's entire earlier own
information and choice history. The source context retains earlier public
cells, and source perfect recall retains the entry observations and own moves.
The two histories can differ in foreign hidden initial data, hidden commitment
values and other information not available to i.

Replay the two prefixes together, using the same scheduler command whenever
its inputs agree and the same selected packet identifiers whenever the
sampler's inputs agree. We prove the following invariants through every
physical step before the decision:

- The two networks have the same pending packets, ledger, submitted-envelope
  history and serial counters; corresponding observers have the same leak
  draws when coupled.
- Public application state, clocks, readiness times, receipts and complete
  environment recall agree.
- Player i's candidate catalogue, application observation, own responses,
  emitted envelopes and remembered response views agree. Foreign private
  candidate meanings are allowed to differ.

Initially the public assignment of handles is fixed, the network is empty,
and i's own initialized data agree. A source commitment always sends one
canonical envelope. Its private preparation can differ between the replays,
but it changes no public view and exposes no opening evidence. Its handle is
the public canonical binding-count slot. Since all earlier canonical binding
calls and inclusions agree, the slot is fresh on both sides; no fallback search
depending on foreign secrets is used. Native message identifiers are determined
by the equal per-author submission counts. Inclusion has the same success
receipt and public effect on both sides, with the hidden bound value still
masked. When i owns the commitment, its chosen value agrees by source recall,
so its own private material and action also agree.

For an earlier reveal, its public result is already part of the current source
information. Effective TRUE and FALSE have distinct results. A successful
result therefore fixes TRUE and the exact typed value on both sides; both send
the same opening, evidence, handle and readiness token. Failure fixes FALSE;
neither sends an opening. A FALSE phase can take an arbitrary random number of
waits before expiry, but both replays see the same public scheduler input at
every such wait. Its expiry produces the same public failure. Protection rules
out the case of a canonical TRUE whose packet is still pending after its
instruction has expired.

Every ready public chance instruction has the same fixed outcome in the two
source prefixes. Its actual sampling kernel depends on equal public source
data. Replay fixes that realized logical edge and samples only the surrounding
normalized runtime processing. It does not condition a scheduler draw on the
next logical chance outcome. Readiness, clock and expiry commands preserve the
invariants by the unique sequential frontier and equal public state.

At an activation the pending lists agree, so the passive rule has the same
law even if it examines packet contents. Use the same selected identifiers.
The foreign packets learned by i, and i's remembered pre-response view, agree.
The private sample does not change the environment input. Silent responses
preserve the invariants. At an earlier own source response, equal source recall
fixes i's actual private submission; at a foreign response, the canonical
envelope cases above apply.

Thus the scheduler inputs agree at every paired step. The same command can be
drawn with the same probability, including a nonuniform or history-dependent
wait. The finite all-history completion bound makes each replay a probability
law, not a subprobability selected by successful arrival. The coupled first
ready responses for the present instruction have equal full inputs for i.
This proves (1). Notice that the scheduler can learn an earlier opening before
its inclusion: its value is nevertheless already fixed identically when
comparing complete source prefixes at a later source decision. This does not
assert that the value was physically invisible during the intervening waits.

## Paper corollary: every selected source SE has a clean preserving SE

**Model for this result.** Use the same complete restricted physical game,
without extra timing choices or costs. The source is finite with perfect
recall; all source chance edges in its legal tree have positive probability.
The runtime implements the same logical menus and chance laws at every full
physical record, finishes in finite time, and preserves source own recall.

**Theorem, paper proof.** Every source SE has an SE of this restricted native
game with the same law of completed source histories and payoffs. At every
first ready decision its strategy plays the selected source policy using the
recovered source information. The policy ignores auxiliary physical data;
its consistent beliefs account for those data. The statement is forward
preservation and does not say that every clean target SE reflects a source SE.
The copied policy is the same for every scheduler and sampler in the declared
class; its full beliefs can depend on the service. A player who does not know
which persistent service it faces needs a specified Bayesian service model and
an analysis of its joint replay channel. Pointwise service theorems do not
automatically supply that Bayesian assessment.

Choose the source SE's one fully mixed consistency sequence sigma_n. Copy
sigma_n at every first ready source decision, and use the only available
silence action at all other activations. Finite native replay multiplication
gives, for a prefix above source history h with physical record omega,

\[
 w'_n(h,\omega)=w_n(h)Q_h(\omega).                    \tag{2}
\]

This holds because each actual source menu and logical chance kernel is
unchanged, while the normalized physical kernels contribute precisely Q_h.
By (1), the probability of each complete auxiliary record z has a common
value q_{i,I}(z) over the source information fiber I. At every legal target
decision (I,z), this value is positive. Bayes' rule therefore cancels it:

\[
 \Pr_n(h\mid I,z)=
 \frac{w_n(h)q_{i,I}(z)}{\sum_{g\in I}w_n(g)q_{i,I}(z)}
 =\mu_{n,i}(h\mid I).
\]

At genuine source decision sites, full target beliefs, including hidden
physical records, are given by
mu_{n,i}(h|I) Q_h(omega) 1[J_i=(I,z)]/q_{i,I}(z). Their second factor is fixed
across n, so the same global sequence converges at those information sets,
including off-path sets. New waiting sites need not have this source-site
formula. Their finitely many belief simplexes are compact; take a common
subsequence on which all their Bayes beliefs converge. This preserves the
already established limits at genuine source decisions and supplies one
globally consistent target assessment. Waiting sites have a singleton menu
and impose no strategic comparison, but their observations remain in later
recall.

For sequential rationality, continue from any complete physical record using
one arbitrary present source-action lottery and copied source continuation.
Erase physical steps. Protected admission, unique expiry for FALSE and the
unchanged conditional logical chance kernel yield the corresponding source
continuation law, from that hidden source history. Average this identity using
the just-derived projected beliefs. The source SE's local comparison applies.
Target perfect recall follows from full own-response recall and the distinct
effective source actions. Finite one-shot deviation equivalence then extends
these comparisons to policies adapting all their later choices to new
receipts or waits. This last step is necessary: it is not sufficient to compare
only continuation policies that ignore the auxiliary data.

Finally logical execution under the copied policy has the source transition
law at every full record. Finite sure completion gives the initialized terminal
law equality directly. The argument uses the source SE's off-path assessment,
not merely source Nash optimality or equality of honest outcome laws.

## Where the general native adapter is still missing

The paper construction requires a history-level identification of each first
ready native response with one source decision, plus a normalized prefix replay
kernel for all lawful source choices. This is more than the existing one-way
checkpoint lemma that equal native observations imply equal source views.
`Vegas.SourcePrefixCheckpoint.source_view_eq_of_observe_eq` proves useful
recoverability; it does not establish (1). The native opaque-binding and
activation congruences give the local induction cases. The source public
history, canonical-slot and first-turn protection APIs supply other cases.
Their assembly into the full coupled replay theorem is not checked here.

The verified
[`PublicScheduler.expanded_sequentialEquilibrium`](../../GameTheoryExtensions/Analysis/Protocol/PublicScheduling.lean)
already allows player-specific token views. Tokens can encode correlated
private receipts from public scheduler randomness. Its checked expansion
uses a fixed number of draws per logical step, recoverable public source
prefixes, public actor determination and unchanged source actions. The native
construction above instead has variable physical lengths, activation/response
pairs, private candidate preparation and TRUE/FALSE transport. The checked
token-view result supplies an SE transfer reference, not a completed native
instantiation.

For guarded programs there is a second adapter obligation. Ineffective TRUE
and FALSE are private aliases whose original intentions can influence later
source policies. The existing source
[DisclosureAliases](../../Vegas/Source/DisclosureAliases.lean) and
[DisclosureNormalization](../../Vegas/Source/DisclosureNormalization.lean)
machinery retains or reconstructs that private history when normalizing
semantic effects. It does not by itself prove that the current native policy
input remembers a silently sampled, rejected TRUE. Either provide an explicit
private-memory implementation and its SE consistency/deviation adapter, or
prove preservation for the effective-action source normalization. Initialized
state-law equality alone cannot justify claiming preservation of the original
full source history law. The effectiveness restriction above avoids this gap.

Extending from clean first-ready-once play to the larger retained risk game
needs a separate rationality/enforcement theorem covering late decisions and
their trembles. Those histories may miss admission, reveal a failed plaintext
opening before another decision, or leave a player with several physical
choices at the same source instruction. Equation (1) is not established on
those histories. Extending further to RAW additionally needs the actual audit,
collection, candidate and response-menu arguments. Clean preservation is an
input to that analysis, not a replacement for it.

## An interpretable weakening and its boundary

**Candidate invariant, not a checked native generalization.** Strict serial
dependencies can be weakened if, before each genuine source decision, every
earlier physically exposed packet field is determined by that player's source
information and the coupled public physical history. Binding meanings remain
opaque; handle selection, packet sizes, evidence and fees must also satisfy
this property. Whenever a plaintext opening can be emitted before an actor's
next logical decision, that actor must already have its value in the source
information for that decision. Physical observations during forced waits can
arrive earlier; they must carry no value still hidden at the next choice.

This is a release-frontier condition, not a declaration that observers never
read pending packets. A public scheduler may react to packet contents when
those contents satisfy the condition. Private samples may be correlated and
history-dependent. Nonuniform waits are permitted when the complete native
inputs can still be coupled and they cannot change logical outcomes or costs.
The serial theorem derives this property from canonical envelopes and source
publications, rather than positing target posterior equality.

Actual barrier-ordered graphs also permit different owners' opaque commitments
to run concurrently between public instructions. Such concurrency is a
promising additional weakening: source-private commitment actions commute and
their envelopes do not reveal the chosen values. Its native SE adapter would
also have to serialize decision histories, not just completion histories,
preserve own recall and treat information about whether another commitment has
already happened. The checked event-graph commutation APIs help, but the serial
replay proof does not automatically prove this stronger claim.

Data-read causality alone does not supply this frontier: a reveal can read an
old initialized binding while being independent of another player's
source-earlier commitment. The actual compiler's public barriers prevent that
reordering. Extra premature proof disclosure remains a separate RAW issue:
rejecting its application effect does not undo the information transmitted.
The complete early-information counterexample is in
[Information and release](information-and-release.md); it is not a failure of
the serial clean interface proved here.

The symbolic commitment envelope is also an idealization. A concrete hash or
ciphertext and its length need a cryptographic hiding refinement and a metadata
analysis; exact equality of symbolic handle envelopes is not an exact hiding
theorem for all concrete bytes. If private values change packet sizes, bids,
dispatch counts, execution bills or available admission, the coupling cases
must be reproved or the theorem narrowed. A secret-dependent receipt can be
payoff-relevant even if the application state update is unchanged, as shown by
the forced-signal result in [Information and release](information-and-release.md).

## Summary card

- **Result:** Paper exact forward SE preservation for finite serial native
  first-ready-once games with value-only commits, successful initialized
  bindings, effective TRUE, protected canonical admission and unchanged
  logical chance laws/payoffs. Retained private state, source withholding,
  full physical recall, arbitrary private leak samples and nonuniform bounded
  waits are included.
- **Primitive information evidence:** Couple canonical envelopes, native public
  environment inputs and full own-response recall across every source decision
  fiber. Previously exposed TRUE values are source-public by the next decision;
  FALSE emits no proof; commitment meanings never enter the public envelope.
- **Excluded choices and costs:** Strategic waiting, retries, premature/off-chain
  release, fee bidding, participation/capacity sabotage, action-dependent
  bills and miner incentives. This is not an SE theorem for full RAW.
- **Checked boundary:** Native opacity, activation, canonical-slot, public
  barrier, source-recall and first-turn protection ingredients; verified SE
  transfer for the token-view scheduler expansion. The native variable-length
  replay assembly and guarded private-intention adapter remain unproved here.
- **Necessary warning:** Data-read causality alone does not imply the release
  frontier. Actual compiled public barriers retain every earlier binding
  before a later public reveal. Uncharged extra proof disclosure is still a
  different RAW information channel.
