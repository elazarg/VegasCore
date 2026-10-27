# Native counted actions under private reception

This note derives the native adapter for the publication-barrier argument in
[the proof routes](se-private-mempool-proof-routes.md). It works with the actual
bounded counted menus, including unusable and wrong-typed preparations, arbitrary
known-packet forwarding aliases, previous counted deviations and retries. It
does not identify literal private views or literal action menus. It identifies
their effective action classes, proves a controlled transition identity for
those classes, and reconstructs the discarded private memory causally.

The statements below are mathematical adapter specifications and proofs.
The cited declarations are existing ingredients; the combined quotient and
readback results have not been assembled in Lean. No new result is claimed for
the unpadded runtime.

## Fixed objects and the publication premise

Fix one compiled graph, runtime, phase plan, bounded raw-value alphabet and
candidate bound, finite horizon, initial source law, and scheduler. The graph
has the existing unique-ready-event-per-owner and phase-order properties.
Use the same objects in the complete-reception and private-reception games.
Only the observation rule differs. The private rule is fixed throughout the
perturbation sequence and has finite support at each actual input.

All histories considered here are initialized histories of the counted menu.
In particular, they may have failed guards, unusable bindings, voluntary waits,
public exclusions and retired attempts. They need not follow the reference
profile. Packet bounds cover all values of every binding/publication output
type; public chance types need no extra wire alphabet. Initial candidates are
retained exactly; no coordinatewise independence of source initial values is
assumed.

The additional publication premise is:

> At every counted binding callback, the set of all submitted opening proposals
> equals the set of opening proposals already in the retained ledger.

The padded-source construction supplies this premise. It is not assumed at
reveal callbacks, and it is not an all-raw claim. A new forbidden opening may
be submitted after a phase barrier. The separate raw-audit extension handles
that larger game.

The local input I consists of the player's complete own recall and current
ordinary view. Write A(I) for its finite counted action menu. Use the ambient
class space

\[
 C=\operatorname{Option}(\mathrm{Raw})\times
       \operatorname{Option}(\mathrm{CommitAttemptPacket}).
\]

The class map c_I:A(I)→C records the typed binding preparation, when present,
and the actual emitted packet. Its definition is
`Vegas.EventGraphRuntime.PhaseProposal.responseClass` in
[PhaseProposalResponseAliases](../Vegas/Pending/PhaseProposalResponseAliases.lean).
Working in this ambient space avoids equating dependent subtype carriers whose
proofs and literal preimages differ between local inputs.

## Literal menus vary; their effective classes do not

The bounded raw syntax is a Cartesian product of bounded calls and bounded
evidence requests. The latter include evidence-none, every bounded owned fact,
and forwarding references to known packets. The candidate catalogue does not
change the raw alphabet. It changes how a request resolves, and therefore
which raw responses survive the count filter. Reception can add forwarding
references. These facts follow directly from
`Vegas.EventGraphRuntime.MessageBounds.submissions` and
`Vegas.EventGraphRuntime.MessageBounds.submissions_mem` in
[ReactiveFiniteResponses](../Vegas/Pending/ReactiveFiniteResponses.lean), and
`Vegas.EventGraphRuntime.PhaseCount.onePacketActions` in
[PhaseCountMenu](../Vegas/Pending/PhaseCountMenu.lean).

For example, an owned request for a wrong-typed candidate can resolve to a
certificate in one execution and to none in another. Attached to a commitment,
the former response is forbidden while the latter can be a permitted alias.
Therefore equality of literal menus is false and is not used.

Let S(I) be the set of serials below the candidate bound whose own prepared
handles are physically fresh. Let sent(I,e) mean that own recall already
contains a packet for the current physical attempt/event. The effective class
menu is exactly as follows.

| Actual situation | Effective classes |
| --- | --- |
| No current owned request | Silence only. |
| Current request already sent | Silence only. |
| Unsent binding e of type t | Silence and, for every s∈S(I), every result r∈{failure}∪Val(t), the class of binding r at handle (i,prepared s). |
| Unsent opening with a surviving successful value v and accepted handle h | Silence and the unique packet opening h to v with its exact certificate. |
| Opening without such a successful value | Silence only. |

For a binding class the emitted certificate is none. Its typed-preparation
component is none for failure and the correctly tagged v for success. For an
opening class the preparation component is none, regardless of unused private
preparation syntax.

Here is a proof of both inclusions, including the bounds.

1. No-request and already-sent menus are literal singletons by
   `Vegas.EventGraphRuntime.PhaseCount.onePacketActions_eq_singleton_of_no_request`
   and `Vegas.EventGraphRuntime.PhaseCount.onePacketActions_eq_singleton_of_sent`,
   in [PhaseBindingIdleMenu](../Vegas/Pending/PhaseBindingIdleMenu.lean) and
   [PhaseSentMenu](../Vegas/Pending/PhaseSentMenu.lean).
2. Every nonsilent binding action names the actual event and a bounded,
   globally fresh own prepared handle. Its optional raw preparation and
   evidence request are otherwise retained. This is
   `Vegas.EventGraphRuntime.PhaseCount.onePacket_binding_shape` in
   [PhaseBindingMenuShape](../Vegas/Pending/PhaseBindingMenuShape.lean).
   Count correctness forces its emitted evidence to be none. Decoding its
   preparation at t gives either failure or one value v. The exact class is
   that of the evidence-none canonical encoder, by
   `Vegas.EventGraphRuntime.PhaseProposal.responseClass_binding` in
   [PhaseProposalCanonicalBinding](../Vegas/Pending/PhaseProposalCanonicalBinding.lean).
3. Conversely, each s∈S(I) supports every typed result. Evidence-none is always
   in the bounded raw evidence menu; the handle is bounded; and successful
   preparations are in the raw alphabet by output-value coverage. The existing
   result
   `Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlots_eq_fresh_of_history`
   in [PhaseBindingSlotHistory](../Vegas/Pending/PhaseBindingSlotHistory.lean)
   proves precisely the universal canonical-encoding legality needed here.
   Failure uses absent preparation, which is always allowed.
4. Every nonsilent counted opening names the actual accepted handle and its
   successful value of the event's declared type. This is
   `Vegas.EventGraphRuntime.PhaseCount.onePacket_opening_shape` in
   [PhaseOpeningMenuShape](../Vegas/Pending/PhaseOpeningMenuShape.lean).
   Its exact certificate is fixed by count correctness. Unused preparation
   and ownership/forwarding syntax give the same class by
   `Vegas.EventGraphRuntime.PhaseProposal.responseClass_opening` in
   [PhaseProposalCanonicalOpening](../Vegas/Pending/PhaseProposalCanonicalOpening.lean).
5. Conversely, the truthful owned-certificate response is bounded and counted
   at an actual unsent successful opening. Its handle is an initial handle or
   an earlier bounded prepared handle; its raw value is covered. This is
   `Vegas.EventGraphRuntime.PhaseCount.phaseOpeningResponse_of_history` in
   [PhaseOpeningCoverage](../Vegas/Pending/PhaseOpeningCoverage.lean).
   No received foreign certificate is required. The theorem does not require
   a successful guard or timely inclusion.

Thus different forwarding menus, wrong-typed owned-certificate capabilities,
or finite alias-preimage sizes do not change the class menu. The canonical
representatives are functions of the actual local input. They are not selected
using a hidden history inside an information set.

## The catalogue mask and its permanent type association

Let T be the signed submitted-envelope list. For each used prepared handle h,
its first own signed commitment in T determines a binding event e and its
declared type t(h). This association persists across rollback because T is
retained. Count correctness forbids every later commitment using the same h,
even at a different event, type or physical attempt. Initial handles are
never prepared-handle binding alternatives.

For a candidate at a prepared handle with associated type t define its mask by

\[
 M_t(d)=
 \begin{cases}
 \mathsf{fresh},&d=\mathsf{fresh},\\
 \mathsf{value}(v),&d=\mathsf{openable}(r),\ r\mathbin{\mathrm{as?}}t=v,\\
 \mathsf{unusable},&\text{otherwise}.
 \end{cases}
\]

All initial candidates are preserved exactly. An unused prepared handle is
fresh on an initialized counted history. Apply the same mask to current,
saved-entry and retired-snapshot catalogues, using the signed association at
the relevant history prefix. A snapshot preceding h's submission has a fresh
entry, so a later association does not change its meaning.

The masked global state z retains:

* the current, saved and retired typed configurations and accepted-handle maps;
* exclusions, phase descriptors, attempt generation, clocks and activation times;
* the masked candidate catalogues;
* ordered pending, ledger and submitted-input lists, next serials and receipts;
* scheduler recall and the protocol's remaining horizon/current actor;
* each owner's emitted-output word and effective class history.

Passive leaked lists and literal private alias syntax are not part of z.
Initial source data may remain hidden to a particular player while being part
of z: z is a physical-state quotient, not an assertion that the state is public.
An owner's catalogue mask is nevertheless computable from its own information,
because its handle/type associations come from its own recalled outputs.

## Controlled successor identity

Suppose two initialized counted histories have the same z. Let i be the current
actor, and choose any counted actions a and a' with the same ambient class d.
The following identity is the required controlled quotient statement:

\[
             \pi(\operatorname{respond}(s,i,a))
          =  \pi(\operatorname{respond}(s',i,a'))
          =  R_i(z,d).
\]

It applies to every counted alternative, not only reference-supported proper
values. The response is deterministic once the class is fixed.

For silence the packet/application state is unchanged, and both sides make the
same protocol, emitted-output and effective-recall bookkeeping updates. For a
binding, both responses use the same fresh
handle and emitted packet. Registration/freeze maps absent preparation to an
unopenable candidate and a supplied raw value to an openable candidate; both
become the same masked result specified by d. Every other candidate is unchanged.
The network appends the same envelope with the common next serial. Own outputs
and class history append the same entries. Literal response recall can differ.
For an opening, registration does not change any candidate and class equality
fixes the full emitted packet. The underlying registration equation is
`Vegas.EventGraphRuntime.Submission.candidateAfter_eq` in
[EventSubmission](../Vegas/Pending/EventSubmission.lean).

Environment commands also have a common projected kernel E(z,k,−). The proof
is by the actual command cases:

\[
 \pi_*\operatorname{Env}_{\lambda}(s,k)
 =\pi_*\operatorname{Env}_{\mathrm{complete}}(s',k)
 =E(z,k,\cdot).
\]

* Inclusion reads the same pending envelope. For a commitment, the packet's
  event is the handle's immutable first binding event, so its typed decoding
  is exactly what the mask retains. Stale/phase-disallowed packets are rejected
  by the same public test. For an opening, count cleanliness at emission ensures
  that its candidate had the exact successful typed value; that candidate is
  preserved, not masked to unusable. Consequently acceptance/rejection and
  the typed configuration changes agree.
* Expiry reads the same readiness, clocks and typed configuration. A sample
  evaluates the same public source distribution. Clock advance is identical.
* Normalization and rollback restore equal typed checkpoints and accepted
  handles, retain corresponding masked catalogues, and update the same public
  exclusion/retirement records. The permanent handle/type association is not
  rebuilt from the restored accepted map.
* Activation samples private reception, which changes only the discarded
  leaked lists. Its projected activation result is independent of that sample.

There is no counted way to expose a wrong-typed candidate omitted by this mask.
A commitment must emit evidence-none. A counted opening must certify its exact
successful typed value; a wrong-typed candidate cannot produce that certificate.
After rollback the old handle cannot be rebound, and latest-binding/current
authorization prevents using it as the surviving opening. Foreign ownership
checks prevent another player from issuing its first certificate, and forwarding
cannot create an absent certificate. The actual signed rules are
`Vegas.EventGraphRuntime.PhaseCount.LatestSignedBinding` and
`Vegas.EventGraphRuntime.PhaseCount.Permits` in
[PhaseCountVerdict](../Vegas/Pending/PhaseCountVerdict.lean).

The scheduler observes no private leaked list. Its public network projection
contains pending, ledger, inputs and next serials; activation leaves that
projection unchanged. This is explicit in
`Interaction.MessageNetwork.publicView` and `Interaction.MessageNetwork.learn`
in [MessageNetwork](../Interaction/MessageNetwork.lean). Hence equal z gives
the same scheduler kernel, including a scheduler represented by one fixed
correlated tape. There is no resampling of that tape at a phase boundary.

The result is strong lumpability of the controlled physical transitions on
counted classes. It is not a theorem that every literal policy factors through
z or that every player's private information equals a projection of z.
Players may use their own discarded memory to choose different classes.

## The reference class law at every perturbation index

Fix one perturbation index n. Write rho for its waiting rate, xi for its
fresh-slot rate, beta for its bad-preparation rate and zeta for its alias rate.
Use the actual source-domain laws in the complete-observation construction.
Assume

\[
 0<\rho<1,\qquad 0<\xi\le1,\qquad
 0<\beta<1,\qquad 0<\zeta\le1,
\]

and full support of every source-domain law. These conditions hold separately
at each positive perturbation index; none is imposed on the limiting profile.

At an unsent binding with nonempty fresh set S, let s_* be the canonical first
fresh serial. The effective slot law is

\[
 \kappa(s)=\xi/|S|+(1-\xi)\mathbf1_{s=s_*}.
\]

The independent typed-result law is beta at failure and (1−beta)V(J)(v) at
success v, where J is the actual enriched source query. The class law is

\[
 \alpha(\mathsf{WAIT})=\rho,\qquad
 \alpha(\mathsf{SEND}(s,r))=(1-\rho)\kappa(s)D_J(r).
\]

If the encoder has no available slot, its output is silence; under the normal
capacity reserve the fresh set at a genuine unsent request is nonempty. At an
unsent successful opening, the two class probabilities are rho and 1−rho.
At a singleton menu the class law is the point mass at silence.

The source query reads the current typed source view and the proposal archive.
Its typed component does not reconstruct raw retired private preparations:
`Vegas.phaseVirtualSourceView?` in
[PhaseVirtualBindingView](../Vegas/Game/PhaseVirtualBindingView.lean) reads the
masked typed store, passes an empty private action word to the decoder, and
applies the source virtual-binding operation. Under the publication premise,
its archive is the retained ledger proposal set. Both components are therefore
the same at paired complete/private inputs with the same masked physical
state. The query is also a function of each actual local input.

The apparent menu tests in the encoders introduce no extra reception dependence.
The fresh-slot theorem above identifies the binding test with S. The successful
opening test disappears by
`Vegas.EventGraphRuntime.PhaseCount.phaseOpeningPolicy_of_history` in
[PhaseOpeningPolicy](../Vegas/Pending/PhaseOpeningPolicy.lean). Its response uses
the own accepted handle and truthful owned certificate. Thus alpha is the same
in both observation models on every counted history, not merely on the intended
equilibrium path.

The fallback in `Vegas.phaseProposalReferenceClasses` must be eliminated, not
ignored. The proof of
`Vegas.phaseProposalBaseClasses_fullSupport_of_counted` in
[PhaseProposalGenuineSupport](../Vegas/Game/PhaseProposalGenuineSupport.lean)
splits into silent, binding and opening cases. The silent and opening cases
already accept arbitrary reception. In the binding case, complete reception is
used through the genuine query and full-support result in
[PhaseProposalQueryDomain](../Vegas/Game/PhaseProposalQueryDomain.lean).
Replace precisely the archive-readback step by the publication premise. The
source control query is already genuine without complete reception; the
original domain-surjectivity argument then gives every typed result positive
mass. Positive beta adds failure, positive xi reaches every fresh slot, and
positive rho reaches silence. Therefore every class has positive mass and the
fallback is inactive on every counted history, including histories with debt.

For a local class d let A_d(I)={a∈A(I):c_I(a)=d}. Its actual alias kernel is

\[
 q_n(a\mid I,d)=
  \zeta/|A_d(I)|+(1-\zeta)\mathbf1_{a=k_I(d)},
       \quad a\in A_d(I),
\]

where k_I is the local selector used by the implementation. The selector and
the fiber size may differ between the two observation models. No equality of
them is needed. The complete literal response law satisfies the exact identity

\[
 \sigma_n(a\mid I)=\alpha_n(c_I(a)\mid I)q_n(a\mid I,c_I(a)),
 \qquad
 \sum_{a\in A_d(I)}\sigma_n(a\mid I)=\alpha_n(d\mid I).
\]

These are the local identities proved by
`Vegas.EventGraphRuntime.PhaseProposal.splitResponseLaw_project` and
`Vegas.phaseProposalReferenceResponses_project_of_counted`, in
[PhaseProposalResponseAliases](../Vegas/Pending/PhaseProposalResponseAliases.lean)
and [PhaseProposalGenuineReference](../Vegas/Game/PhaseProposalGenuineReference.lean).
Their extension to the private barrier histories uses the just-derived removal
of fallback. Since zeta and every class mass are positive, every literal counted
action is positive. The construction is fully mixed in the actual private game.

## Reconstructing the owner's discarded memory

The wrong-typed candidate bytes are private self-generated memory, not a hidden
state that must be guessed by a simulator. Initially the owner has its actual
initial catalogue. Each own commitment response records its literal preparation.
Apply the deterministic registration/freeze operation immediately at that
response. A nonfresh candidate cannot change afterward. Rollback retains it.
Foreign submissions cannot modify another owner's candidate catalogue.

Inductively, the entire unmasked own catalogue is determined by initial own
catalogue and literal own commitment responses. Unused preparation fields and
evidence requests are retained in virtual own recall even when they do not
change the catalogue. Reception history is retained as well. Thus, given the
masked own observations, the simulated private reception draws and simulated
literal own responses, the simulator reconstructs every actual local input I
needed to evaluate q_n at its next step.

This reconstruction uses only observations and responses already available at
that time. It does not infer a hidden checkpoint, use a future response, or
choose separate reconstructions for different hidden histories in one actual
information set. A general transported policy can carry this private memory;
for the reference profile, future class probabilities ignore it except through
the retained source query and emitted-output data.

## Ordered pending readback from complete own recall

The observation rule receives the entire ordered pending list. Knowing the set
of submitted messages is insufficient. The complete player's own recall does,
however, determine that ordered list at each of its activations.

Enumerate the player's activations by k. Let P_k be the pending list immediately
before its complete reception draw, L_k the ledger observed there, R_k its
accumulated leaked list after that draw, and E_k its optional own emitted
envelope at the following response, interpreted as an empty or singleton list.
Let D_k be the new suffix appended to R_(k−1). At the first activation there
are no earlier own outputs and P_0=D_0. At every later activation,

\[
 P_k=\operatorname{filter}_{\mathrm{id}\notin L_k}
           (P_{k-1}\mathbin{+\!+}E_{k-1})
        \mathbin{+\!+}D_k.
\]

Between two consecutive own activations there is no other own submission.
Every additional submission is foreign and has a globally fresh message ID.
Those new foreign envelopes still pending occur in D_k, in their pending order.
Those already included are absent from pending and D_k. Previously pending
envelopes remain in their old order unless inclusion removes them; retained
ledger membership identifies precisely those removals. This proves the formula.
It remains valid for arbitrary inclusion order, not only FIFO processing.

The initial network is empty and inclusion retains envelopes in the ledger.
Complete reception appends fresh foreign pending envelopes in their current
pending-list order. These are the actual definitions of
`Interaction.MessageNetwork.empty`, `Interaction.MessageNetwork.includePending`
and `Interaction.MessageNetwork.learn` in
[MessageNetwork](../Interaction/MessageNetwork.lean). The recurrence therefore
uses no public observation of a scheduler callback and no access to scheduler
private recall. It uses the player's own successive local views and responses.

## Causal reception/alias kernel and source feedback

Given a complete own information history F, reconstruct its ordered P_k by the
preceding recurrence. At each own activation, sample the actual fixed private
observation rule on P_k and update the simulated private leaked list. Use the
complete history's already chosen effective response class d_k, sample the
actual private alias law q_n(−|I_k,d_k), and update simulated recall/catalogue.
The initial own data and masked typed observations are retained. This defines
a stochastic kernel K_n(I|F) on complete information histories.
At the current callback, stop after reconstructing its reception and view:
its response has not yet been chosen. Only past own effective classes are
used in constructing K_n. Thus the kernel is defined before the tested local
alternative and cannot condition its posterior on that alternative.

Each input used by this recursion is available in the complete player's local
history at that time. The retained class d_k is the class of its own action,
not a hidden foreign action. The reconstructed private menu contains d_k by
the class-menu equality. Its q_n fiber is therefore nonempty and normalized.
The recursion uses no unobserved source input. K_n may vary with n because
behavioral alias rates vary; the actual observation rule and scheduler do not.

There is a feedback issue that an open-loop noise argument would miss.
A chosen class changes future packets, admission and source state, and those
changes affect future private observations. The correct proof samples reception
on the updated actual pending list after each controlled transition. It does
not pre-sample a transcript independently of future actions. The controlled
successor identity above supplies the same updated list on the two sides.
Source samples are likewise drawn from the updated common typed state.

For the prescribed profiles, common class law alpha_n lets both executions
choose the same class before drawing their separate literal aliases. Summing
each alias fiber and each private reception kernel gives a common projected
physical path law. For a retained physical history H, the coupled own-history
law has the factorization

\[
 \Pr_n(H=h,F=f,I=i)=\Pr_{\mathrm{fine},n}(H=h,F=f)K_n(i\mid f).
\]

Here H retains the initial draw and the masked physical history; it need not
be observed by either player. The factorization is a consequence of the causal
construction and shared class laws. It is not an assumption that initial
private types are independent, or that private reception cannot depend on
packet contents.

## Every counted one-step literal alternative

Fix an actual private information set I and any literal action a∈A(I), including
a wrong-typed preparation or an unusual allowed evidence alias. Its class d is
constant on that actual information set: packet materialization uses precisely
the local input defining I. For every compatible fine information set F, the
same d has a legal canonical representative, by the exhaustive class-menu
description. The representative is selected at F, never at an unobserved node
inside F.

Force a on the private side and a representative of d on the fine side, then
return to the prescribed profiles. The immediate masked successors agree.
Their future class laws agree at every reached counted history, and subsequent
observation kernels are sampled on the corresponding updated pools. Backward
induction on the remaining finite horizon gives equality of every continuation
payoff that is a function of the retained terminal physical state. The initialized
typed terminal state, original inputs, exclusions and base utility are such
readouts. Counted audit charges are zero.

The same argument applies to the prescribed class mixture in place of d.
The preceding factorization gives the conditional gain identity

\[
 G_{\mathrm{private},n}(I,a)
  =\sum_F\Pr_n(F\mid I)G_{\mathrm{fine},n}(F,d).
\]

If the fine witness retains literal own aliases, first average over compatible
literal fine information sets and choose a legal representative of d at each.
This gives the same bound for the masked fine information. One-step canonical
representatives suffice: the continuation invariance concerns the specified
reference, so no theorem that arbitrary literal policies ignore their own
private catalogue is being asserted.

A uniform fine regret bound epsilon_n consequently bounds every actual private
counted one-step gain by epsilon_n. Together with the full-support result at
every n, this is the native contract required by the finite transfer argument
in [the transfer mathematics](se-publication-transfer-mathematics.md).
The construction covers arbitrary action-dependent packet observations through
the controlled identities; it does not coarsen an arbitrary fine SE after
taking its limit.

## Exact formalization boundary

The shape, coverage, registration, class-splitting, genuine-source and raw-audit
ingredients cited above already exist. The mathematical derivations here add
four composed interfaces: the immutable-type catalogue relation; its controlled
command/response successor laws; actual-input common class laws under the
publication invariant; and the ordered-pending/private-memory history kernel.
These interfaces must still be expressed and proved in Lean.

The quotient is restricted to initialized counted histories and counted
alternatives. A forbidden commitment can attach extra evidence, a forbidden
opening can expose a wrong-typed or retired handle, and an arbitrary raw owner
can deliberately use the hidden catalogue capability. Those behaviors are not
silently identified by the mask. The existing arbitrary-reception raw-audit
extension is applied after constructing the private counted SE.
