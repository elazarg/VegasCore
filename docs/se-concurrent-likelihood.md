# Concurrent qualified likelihood and causal payoff

This document gives the complete agent-reviewed mathematical argument for the
four primitive obligations used by `QualifiedBindingLaw`: `qualified_source_site`,
`foreign_posterior_cut_pair`, `qualified_annotation_pushforward`, and
`annotated_stopped_payoff`. Their Lean statements and the downstream aggregation
compile. The source-site, foreign posterior pair and stopped-payoff primitives
are Lean-checked (3/4). Weighted transport remains open. The
mathematical derivation is reviewed; concurrent sequential-equilibrium preservation remains
unproved in Lean. Checked declaration names identify existing tools; the finite
constructions connecting them are given below.

## Scope and exact conclusions

The runtime is the reserved implementation in mode `.concurrent`, with its
existing `Operational` hypotheses and `completePendingObservation`, finitely
many players and finite binding types. The initial law mu is the original
finite-support arbitrary JOINT law; its coordinates are never resampled
independently. `WellFormed.initialValues` makes initial commitment cells
successful. The whole-execution tape prior is independent of mu, but its
coordinates may be correlated across owners and time. Prefix and terminal
posteriors always refer to this same tape. Public samples use their actual
laws. No finite-support hypothesis on all histories or Nature outcomes is
added. Each individual trace and commitment block is finite.

Fix focal owner i, a genuine ready unsent binding information I=(past,view),
event e and payload type. `CleanUnsentBinding` consists of binding layout,
request, unsent, noSaved, noCurrent and noForeignFailure. The latter excludes
exclusions outside the actual archived/current omission footprint. Whole-history
foreign goodness excludes every generated unusable preparation, including
canceled and never-admitted ones. Current-store usability alone is insufficient.
Canceled focal BAD actions and their raw aliases remain literal.

Write r_N(h), r_S(g) for actual initialized reach weights, N for native
information mass, and P for `qualifiedPrefixMass`. Source-site and weights use
the stated strict perturbed prescriptions and full-support ordinary table D.
The pair permits arbitrary historical source/native profiles with its stated
support assumptions. Payoff permits an arbitrary fully mixed Bayes native
assessment, retaining prescribed source support. Its future policies are fixed
D-based unflagged policies; an arbitrary prefix policy does not change them.

The four exact conclusions are:

* `qualified_source_site`, when P>0, produces a `QualifiedBindingSource`: one
  full source site J, legal typed encoder, supported Good anchor, query and
  ordinary-policy identities, and `actualCut` tying EVERY actual canonical
  before-e cut at I to J. One source/graph joint supplies both store and emission
  locks, including already-issued static-later rows.
* `foreign_posterior_cut_pair` supplies `ForeignPosteriorCutPair`. For every
  actual h, target q, tape, clean site and proper v with its specified support
  and positive annotation, it gives positive all-ledger mass, positive Q(true),
  the ledger-conditioned pair identity, positive own-only mass, and the own-only
  pair identity. Both coordinates are enriched before-e/completed histories.
* `qualified_annotation_pushforward` applies to EVERY package satisfying the
  source contract. It gives positive finite common O_J,C_J,S and sum A, the
  required constancy, and for every m,v,g,G:

      O_J C_J W(m,v,g,G)
        = A_m 1[info_i(g)=J and Good(g)] r_S(g) H_v(g,G).

  W is actual `annotatedForcedBlockWeight`, A literal `mechanicalCoefficient`,
  and H_v `sourceForcedBlock` using the package encoder. This is a decision-cut
  equation, not a likelihood identity at every arbitrary native prefix.
* `annotated_stopped_payoff`, without P>0 or positive-annotation premises,
  identifies the actual unnormalized qualified law for every legal proper
  current response c encoding v and every outcome y:

      N qualifiedPayoff(c)(y)
        = sum_(m,g,G) W(m,v,g,G) H_G(y) + (N-P) delta_none(y).

  H_G is the actual unflagged source terminal-payoff kernel mapped to `some`.
  The conclusion retains arbitrary utility, the original tape, every proper
  alias, and c with zero probability under the historical policy.

The latter two contracts take the exact pair law internally. Real downstream
assemblers supply `foreign_posterior_cut_pair`; it is no capstone assumption.
The shared ordinary row calculation below is independent of the pair theorem
and source-site construction. Pair does not assume source-site. Source-site
proves its own pullback and cylinder positivity without annotation positivity.
Payoff uses pair only afterwards. Weights use neither payoff nor QBL.

## Literal initialization, tape and annotation kernels

Let C be h's literal `checkpointSelection`, c its `canonicalSource`: the selected
closed entry lifted using actual native proposal-archive labels. Origins retain
its supported initializer theta. Initial named references and native inputs
persist, so readback identifies this SAME theta, not independent marginals.
`proposalRecovery_initialized_prefix` and initialized-trace uniqueness identify
the enriched initial prefix.

For original environment recall rho(h), actual scheduler disintegration gives

    r_N(h) T_h(tau) = prior(tau) fixedTapeReach(h,tau).

T_h is `prefixTapeLaw`. Responses preserve environment recall;
`SchedulerImplementation.command_disintegrate` and
`Interaction.ReactiveApplication.SchedulerImplementation.posterior_snoc` give the
induction on environment steps. Retain initializer, player and physical-result
atoms throughout. Zero original likelihood vanishes before posterior fallback.

K_h is `proposalRecoveryClosedLaw sourceProfile i c`. Its key retains the
original base, full focal information, chronological foreign cause-read word
and Good bit. Literal COMMIT results, including canceled ones, remain fixed;
the specified hidden foreign PUB causes may vary.

`ordinaryForeignJoint(h,q)` pulls q's point through C's exact residual lift,
with false Bool fallback on failure. In COMMIT it runs `ordinaryBlockProfile`
and reads full foreign structural histories, focal coordinate empty, plus the
actual issued-ledger test. Write Q for that joint, U=Q(true), Q+ for its foreign
marginal conditioned on true. Actual annotation is

    r_N(h) T_h(tau) 1[foreignGood(h) and focalAlive(h)] K_h(q)
      * (if U=0 then 0 else Q+(z)).

W sums it over information histories with mechanical word m, q,z, multiplied
by the actual `bindingAdmissionBit(h,tau)` and
`sourceForcedBlockJoint(h,q,z,v)(g,G)`. Qualification stays inside the h sum.
The current full word includes emitted foreign rows after e, read from G.

## Selected entry and the independent ordinary row calculation

Let E be saved exclusions, B the maximal COMMIT prefix of C's residual, n its
length, low its phase start, k=e-low. The actual request and maximality give
0<=k<n. Embeddings and action/view maps are C's literal maps transported through
block reconstruction, with row j at low+j.

`saved_excluded_eq_public_failures` and clean.noForeignFailure give current
exclusions=E; saved/current monotonicity gives the other inclusion.
`bindingsHoldValues_of_no_saved_failure_and_foreign_good` makes all E-active
saved cells proper, using the actual request, clean.noSaved and native foreign
goodness. Inherited exclusions need not be empty.

`phaseProposal_binding_entry_checkpoint` supplies the actual first fresh entry
a retained to h, same attempt, idle actor and fresh recalls. Preserve C.
`checkpointSelection_eq_of_attempt` equates its saved source history with the
entry selection. Transfer C backwards with saved-state/generation/phase equalities.
In the entry witness replace the checkpoint by that transfer. Project the full
history equality for aligned; apply congrArg recoveryAddressWord for chronology;
transport origins with the same equality. Consumed/runtime fields have the same
actual state. Lift with the SAME archive labels for ArchivedProposals. This is
the checked `RecoverySourceWitness.prefix_at_same_attempt` record construction,
not equality of arbitrary whole witnesses. `transfer_history` and
`transfer_binding_readback` preserve C's decoder, refs, embedding and views.

`ordinary_installed_binding_cursor` gives the exact actual source/graph entries
and maximal block. `phase_commitment_prefix_sourceArchive` preserves the archive
inside COMMIT. Initial origins plus fieldwise `CompiledSuffix` traversal retain
every initial reference `.inl(inputId cell)`; C.refs.Agrees and native input
retention give literal originalInputs and initializer support.

The independent local induction uses `ordinary_block_head_law` and the installed
source block coupling. Maintain the exact lifted point, E,generation,saved phase,
active successful cells, complete active information with accumulated own
actions, unchanged archive and the literal address word. Its head read premise
is C.views.observe; control is (E,generation,low); archive is the actual submitted
archive. Appending a proper row creates no missing flag; automatic rows repeat
owners already in E, preserving the address premise.

At an active row the source kernel is exactly D at that updated owner view.
The guard is recorded for REVEAL, not tested at COMMIT. The new successful cell
and own action persist and other active views stay unchanged. At an excluded
row the structural prefix law inserts failure; the source takes NONE and
`Vegas.SourceProgram.automaticCommit`. If f is structural and f* actual, they have identical typed
cells and relevant active views, not equal histories or guard obligations.
`Config.automaticCommit_view_eq_failure` preserves other-owner views.

No row enlarges E, so final close is clean. The exact block-length suffix and
ordinary labels are retained by `proposalRecovery_ordinary_commit_block_support`.
Products of head atoms identify the whole law, retaining both depth-k prefix
and completion. `sourceCommitFuel` there is n-k; k=0 is the original prefix.
This calculation uses neither pairLaw nor positive annotation.

## All-K coverage and one joint source cut

For source-site extract actual h,tau from P>0. Its summand is foreign-good,
alive and has true admission. Make a partial assignment I_p(j) from EVERY
current-attempt recalled emission. `Vegas.EventGraphRuntime.PhaseCount.recalled_submission_emitted`, recorded
emission uniqueness and freshness give consistent immutable preparations.
Namespace filtering removes canceled attempts. Inherited-excluded owners
cannot have a current active SEND and constrain no row.

`phaseProposal_recalled_binding_preparation_value` gives proper foreign values.
For focal values, `phase_recorded_binding_rank_lt_of_unsent_request` puts every
current recalled SEND before e, and `phase_ready_earlier_binding_read` gives its
accepted field. Authentic emission uniqueness identifies that field's immutable
preparation. The original genuine view still contains this unresolved COMMIT
cell: there is no intervening REVEAL inside B. A failure would therefore witness
FailedBinding, contradicting clean.noCurrent through
`phaseProposalCurrentBindingFailure_genuine`. This proves focal properness
directly. Enumerate B: use each constrained proper
value, otherwise any supported D atom at its current query; additionally choose
v at row k for payoff. FullValues makes each fixed proper atom positive after
all earlier choices. Excluded rows are deterministic. Their finite product is
positive, without assuming equality of unrelated intermediate queries.

For EVERY q in K_h support, first obtain positive canonical source reach from
strict prescription. ClosedLaw_support supplies equal ClosedKey; the Good bit
and `canonicalSource_foreignGood` supply both Good hypotheses. Refinement's
`erasedHistory`, `publicRecall`, `surviving_info_eq` give the same erased entry
and full active information. If q.state=some s, apply withHistory using s's
history to the erased-point equality. The equations withHistory_history,
withHistory_withHistory, C.origin.withHistory_lift and withHistory_entry give

    s.point = C.lift(entry C.tail {C.source with history := history(s.point)}).

`residualEntry?_eq_some_iff` identifies this exact pullback WITHOUT Q(true).
The independent ordinary row calculation applies with the transferred controls,
addresses and archive. Repeat the partial assignments at q to prove Q_hq(true)>0
and positive focal-plus-v mass for every supported q. This precedes any use
of annotatedPrefixWeight_support and is not circular.

At the actual fresh cursor condition ONE
`phaseProposalBindingPotentialProfile_source_block_coupling` on all constraints
I, without selecting v for source-site. The positive construction gives support.
Choose (G,key) from that conditioned joint. SourceSupported, graphSupported and
blockResult come together. Conditioning and emission-frontier invariance give
lockedEmissions. For lockedStore split any present field: inherited before low;
current active accepted and fixed by authentic emission; inherited excluded and
deterministically failure. Current exclusions=E precludes a missing-active case.
Later-phase fields are absent; initial fields are inherited. This proves all
locks, not merely the focal one.

Condition the COMPLETE word first, including already-issued foreign rows after
e. Take g as this same G's depth-k prefix. Its Attempt gives past/future/clock,
rank=e, actor=i, atCommit and focal survival. Entry/cursor/initializer data give
all remaining canonical-cut fields. Ordinary rows preserve Good; strict source
prescription gives positive reach. Set J=info_i(g).
`PhaseProposalCanonicalBindingCut.info_eq_of_information`
identifies EVERY actual cut at I with J. Native readback/source view/archive
identify its query. At the genuine binding site the successful enriched move
is unique: `ProposalRecoveryMove.Valid` permits proposed=true only at withheld
REVEAL. This gives encoder and mapped unflagged D law, proving the whole package.

## The two exact posterior pair identities

For the pair theorem expand its positive annotation to obtain native foreign
goodness and Q(true)>0. `annotatedPrefixWeight_support`, using its supplied
canonicalSupported, gives equal ClosedKey and q support. Q's false fallback
then gives the selected residual pullback directly. Refinement and clean facts
supply the independent row calculation's entry data. No historical prescription
is required for these structural inferences.

Let L be that structural ordinary law, Phi its enriched prefix/completion pair,
Z its FULL foreign histories with focal coordinate empty, C(Z) the issued
foreign ledger and A the focal past plus v. `phase_ready_earlier_binding_read`
puts every earlier focal row in the accepted table; unsent ordering excludes
later focal emissions. clean.noCurrent rules out failure at those unresolved
cells. The finite proper-choice construction gives alpha=Pr[A]>0.
`issuedLedger_iff_prefix_at_request`, with the exact selected ranks/action
decoder and request, identifies precisely A; no globally-clear recall lemma
is used.

At fixed entry `prefixLaw_views_product` factors owner words. Each row reads
only its owner's initial view and earlier rows; COMMIT exposes no foreign
value and changes no archive. Repeated owner rows remain one DEPENDENT marginal.
Thus A is independent of Z. Initial correlations remain in the fixed entry,
not an independently resampled prior. Write b_z=Pr[Z=z], u=Pr[C(Z)]=Q(true)>0:

    Pr[Phi=t,A,C] = alpha * sum_z b_z 1[C(z)] Pr[Phi=t | Z=z,A],
    Pr[Phi=t,A]   = alpha * sum_z b_z Pr[Phi=t | Z=z,A],
    Pr[A,C] = alpha*u,                    Pr[A] = alpha.

For positive b_z identify the conditional kernel with the actual
`sourceForcedBlockJoint(h,q,z,v)`. Its before index is k. Pulled-entry history
and `ordinaryBlockWord_drop` remove EXACTLY the entry prefix from full z.
Excluded synthetic failures are irrelevant to the real source menu by
`source_word_cut_mask_excluded`. Active foreign lists force their exact fresh
named rows. Focal phaseCommitRecallWord plus the chosen value fixes exactly A;
fresh names, `word_action_unique`, `source_word_choices_unique` and
`source_word_focal_past` prevent constraints on later focal rows.

Division by alpha leaves the later focal causal D product. The runner inserts
v first, then evaluates each future focal query at UPDATED full information.
Foreign forcing has probability one. Ordinary COMMIT validity fixes enriched
labels. This identifies BOTH history coordinates. Ledger wordAction reads
cells, equal between f and f*, not their different excluded private histories.
Divide the two joint equations by alpha*u and alpha, respectively. These
positive finite factors cancel, giving exactly

    law(Phi | A and C) = Q+.bind sourceForcedBlockJoint,
    law(Phi | A)       = (Q.map fst).bind sourceForcedBlockJoint.

alpha*u and alpha give the remaining support assertions; zero b_z summands
vanish. Tape/admission hypotheses restrict applicability but introduce no coin
in this source-only identity. This proves the arbitrary-profile pair contract.

## Historical alignment through complete visit windows

Fix an index with qualified actual anchor h*. Construct its actual cut g*,
entry q* and completion G*. The package's actualCut gives info_i(g*)=J.
Expand each normalization into its finite settle recursion for bookkeeping,
retaining the raw pre-restore image. This adds no probability factor. A dirty
exhausted visit has ONE attempted source word; close rebuilds automatically
inside its last row.

`checkpointSelection_prefix` and `checkpointSelection_eq_of_attempt` place
selected endpoints in ONE chronology. `ArchivedSourceOrigins.append` retains
the actual dirty drained image for retry AND exhaustion; `advance` retains
nonarchiving entry images and public paths; initial retains the original input.
Proposal labels are actual archive labels.

For any Good g at J, `source_information_before`/`source_information_row` peel
the equal full signal and own-action lists. They give the unique same-depth
prefix map from g* to g. `source_information_metadata` identifies code/saved
positions, deferred registry/revelations, E,entryE,generation at EVERY row.
Public samples and addressed proposal deltas agree. Define q as g's prefix
at q*.depth. Map each historical interval [a,b] by these literal depths with
ALL intermediate masks, not by searching endpoint namespaces. The current
interval is read from supported G.

At an accepted row, pre/post activity and missing=false transfer. Good(g)
makes a foreign result proper; the focal action is literal, including canceled
BAD. A missing active reference row adds its owner to E; the target must also
be missing, and recoveryAvailable forces failure. An inherited-excluded row
has the unique absent action and automatic failure without new owned history.

Assign handles by signed immutable origin (attempt,event,owner). Historical
accepted origins read g even if canceled; current emitted origins read G even
if pending after e; initial handles read theta. Only historical never-admitted
proper draws receive auxiliary D values. Origin/freshness uniqueness prevents
overwrite. `source_emitted_binding_address` and
`sourceBindingAt_same_information` provide the actual addressed rows.

Induct through the WHOLE visit before close. A selected compiler name receives
its assigned accepted value; focal BAD, missing and inherited-excluded rows
receive failure. Old cells persist. Thus the raw source result is the decoded
mapped native drained image with its attempted history. Attempt row count,
`chosen_commit_trace`, `chosen_commit_addresses` and `chosen_commit_public_scan`
fix every interior address and the endpoint at a+block.length. No unproved
extra interval is inserted after the last row. Full masks select the close:

* No new exclusion: source saves the raw result, native clean advance retains
  the drained image, including an all-inherited-excluded block.
* New exclusions with surviving block owners: restore the saved image, retain
  the attempted history, archive native raw and increment generation for retry.
* New exclusions without survivors: archive native raw, restore and automatically
  fill failures, retaining ONE attempted word with no generation increment.
  `after_commit_exhausted` supplies exactly this endpoint. Later automatic
  visits have their own windows.

The tests use entry/final E and static owners, never same-generation=clean.
`sourceSnapshotAssignment_normalize` gives native commutation across all
current/saved/retired snapshots; the raw-image induction separately supplies
source-image identification. Thus the induction crosses each actual exit.

## Publications and every pre-SEND query

A live accepted prepared handle at PUB came through a CLEAN origin exit.
Dirty restore removes its new field. Its original packet cannot reinstall it:
retry changes generation, advance changes phase, authenticity fixes that packet
and fresh-handle uniqueness forbids rebinding. Archive storage does not reinstall
accepted maps. Later restores preserve older saved fields. Initial handles
instead use the retained initial-reference readback.

`submitted_proposal_binding_meaning` and `onePacket_opening_shape` identify an
actual opening's raw x. Its archived proposal remains present despite loss,
rejection or guard failure. Equal full J transfers that addressed delta.
Unfold recoveryProposal: payload x requires prestate binding success x;
proposed is Bool, has no payload, and the read precedes guard evaluation.
Thus target field AND accepted handle have the same x even at withheld+proposed
or failedDisclosure. Accepted-map functionality supplies all RevealFixed handles.
Stale/wrong-phase packets reject before needing this premise.

At an active foreign reveal without a proposal, prefix goodness makes its
stored binding proper, so no delta forces discloses=false. Excluded owners
have NONE. The allowed hidden variation is truthful-delivery versus
failed-disclosure with the same failed public result and proposal, both
excluding the author: the exact ForeignDisclosureLabels refinement. Public
sample outcomes and their sourcePublicEnv-dependent atoms remain literal.

At every FOREIGN pre-SEND BIND query, readiness makes earlier own rows accepted;
other owners' unfinished private rows are masked. Historical closing supplies
saved fields and ALL old address windows. Current differences can involve only
other-owner exclusions not yet processed natively. NoMiss removes precisely
these current-interval differences, preserving entry E,generation,low and old
windows. `surviving_binding_source` and `virtual_binding_source` supply actual
partial/virtual readback. Initial refs read retained inputs, saved refs their
last clean origins, and current refs their assigned own rows. This active foreign
owner's cells are proper, so virtualBindings changes none of them. Focal BAD
is allowed: focal factors instead use the unchanged full raw input and recall.

Unfold the first query coordinate using commitRecovery_erasedInformation_read.
`commitRecoveryNoMissInformation_erased` and erasure idempotence equate the
native Eras(NoMiss(ErasedRead)) with the source Eras(NoMiss(info)) expression.
Its NoMiss normalization has common attempt depth
`d = signalPast.length - (position - low)` by commitRecoveryAttemptStart.
commitRecoverySavedExclusions reads the signal at d, yielding E. The COMMIT,
active-owner and owner-not-in-E guards hold. commitRecoveryWithAttemptExclusions
replaces only each signal's exclusion component at times >=d by E; generation,
saved rank and typed views remain unchanged. Before d the signals already agree;
at/after d their only differences are exactly those replaced exclusions.
Thus first coordinates agree entrywise without hiding historical retries.

For the archive coordinate, `observedSourceArchive_eq_submitted` with
Operational.completePending, the actual initialized trace and current foreign
actor gives precisely PhaseProposal.sourceArchive of the input list. Addressed
proposal correspondence supplies that same archive at the target row; at the
selected checkpoint this is also ArchivedProposals.binding. COMMIT adds no
proposal. Together these calculations give the exact source query.
`ProtocolViewSuffix` transports ACTUAL views, not arbitrary injected views.
Apply this before the sender's possible later exclusion; final survival is
not substituted for an earlier query argument.

## Mechanical coefficient and admission read sets

Mechanical constancy concerns TWO ACTUAL positive prescribed foreign-good
histories with the same mechanicalWord. Its projection retains remaining,
actor, application public state, full network public state (pending,ledger,
inputs,nextSerial), receipts, all-owner serial freshness, environment recall
and full focal input. `history_inputRecall` fixes sent status.
`phaseProposalReferenceResponses_project_of_counted` and
`phaseProposalReferenceClasses_eq_of_counted` expose each actual class law and
input-dependent alias kernel. Supported aliases project to that class and
conditional alias mass is one; equal menu cardinalities are unnecessary.

No request/already-sent branches are pure silence, using
`onePacketActions_eq_singleton_of_sent`. For unsent BIND,
`phaseBindingSlots_eq_fresh_of_history` gives the common eligible set S;
capacity and `phaseBindingSlots_nonempty_of_history` make it nonempty.
reactiveFreshSlot chooses the same Nat.find s0. The result-independent packet
p_s has the same attempt,event,serial,public mask/token and empty evidence.
`phaseBindingPolicy_of_history` gives exactly

    w delta_none + (1-w)[s uniform(S).map p + (1-s) delta_(p_s0)].

SEND includes (1-nativeBad), WAIT does not. Keep the exact uniform/canonical
overlap. For PUB, accepted none gives silence. Accepted some and Ready give a
typed result; `BindingInvariant.binding_value` and
`accepted_snapshot_value_of_no_generated_unusable` make outputs successful;
WellFormed.initialValues handles inputs. `phaseOpeningPolicy_of_history` gives
waiting w versus truthful SEND 1-w WITHOUT a guard-success premise. Equal public
input increments determine the actual packet/silence, so evaluated atoms agree
even if an UNCHOSEN alternative truthful packet would differ. PUB has no BIND
bad multiplier.

`ReservedEpoch.family` commands read only tape, environment depth, pending-head
id and public phase kind/low. Their actual atoms agree. Initializer and Nature
probabilities are not mechanical factors. Multiply chronological row atoms and
use `mechanicalWord_ownPlay` to obtain representative independence of literal
prior*ownPlay*mechanicalPathAtom, exactly `mechanicalCoefficient`.

Admission also agrees. The offered proper-response predicate reads the same
full focal input. After a representative response, application public state,
appended packet and environment cursor agree. Acceptance words read public
exclusions/accepted map/requests/activation, tape, pending and sender-filtered
outputs. `ownedAcceptanceWord_available_bindings_eq` and
`ownedAcceptanceWord_respond_foreign` remove proper-alias dependence. This
preserves the actual bit, rather than inventing a replacement schedule test.

## Actual reconstruction and both augmented inverses

Given Good g at J and supported H_v(g,G), replay the anchor's command/packet
skeleton from g's theta and the handle assignment. Each foreign response uses
an alias in its ACTUAL input's class fiber. Historical accepted values come
from g, current ones from G, historical lost values from D at the matched
pre-SEND query. BIND request/freshness/capacity/outputValues and PUB success
plus `phaseOpeningResponse_of_history` give legal canonical representatives.
Strict alias noise/fullValues give support at each genuine partial trace.
Construct support BEFORE applying mechanical constancy.

Use target G consistently in sourceSnapshotAssignment; the auxiliary lost map
is used only for historical never-admitted handles. `sourceSnapshot_binding_available`
takes the actual anchor member, reconstructed CountRecall, equal network and
snapshot relation, plus outputValues, to give a legal SAME-serial canonical
BIND. `properBinding_calls_eq` makes every supported proper alias of that class
register the same value; count correctness makes evidence empty and class
equality fixes the packet. PUB aliases register nothing and their opening class
fixes the certificate/packet. WAIT is literal none. Raw recalled alias syntax
is retained, without assuming equal alias menus.

Focal raw responses remain unchanged. Full J fixes their private initializer,
source actions/values and the skeleton fixes public input. A historical focal
lost SEND would exclude it permanently, contrary to its current live request.
Earlier current focal rows are accepted; canceled BAD aliases remain literal.
`Vegas.EventGraphRuntime.WitnessedSubmission.emit_swap_of_own_handles` and
`respond_phaseExecution_of_onePacket` prevent
inert evidence from reading changed foreign candidate values. Those same
focal aliases remain legal. For INCLUDE, `sourceSnapshotAssignment_handle_binding`
uses the original proper value registered at this prefix and retained in the
reference's immutable final catalogue, with target sourceHandleMeaning. Its
failure branch keeps failure and pair=none; rejection uses
`sourceSnapshotAssignment_rejected_binding`. PUB uses
`sourceSnapshotAssignment_handle_opening` with RevealFixed, including rejection.
Expiry/environment use `sourceSnapshotAssignment_environment`; normalization
uses `sourceSnapshotAssignment_normalize` and the raw closing-image induction.
This yields an
actual supported h at I with the same word,tape and admission bit.

Its canonical c(h) and q have the same base, full focal information, literal
commitments, public outcomes and foreign proposal classes. The actual
proposalRecoveryForeignCauseJoint/Read therefore give equal ClosedKeys. Goodness
and support put q in K_h; hidden q PUB causes remain posterior-distributed.
z is uniquely recovered from q,G: full active history prefixes plus block
actions, deterministic excluded synthetic failure suffixes, focal empty.
Those excluded suffixes are not free inverse variables. Issued-ledger and
local row equations give positive Q(z,true) and forced-pair mass.

From a positive W atom (h,q,z,g,G), extract actual aliases and historical lost
proper values. Replay returns h by raw-depth induction, including raw/saved/
retired closing images. Entry-depth prefix recovers q; structural readout
recovers z. Conversely replay from g,G plus a supported sequential auxiliary
record, then extract: origin uniqueness recovers every choice, and deterministic
transitions with selected public chance outcomes recover the record. Hidden q
causes are recovered from g, not via a claimed bijection of unaugmented native
and source traces. Full focal raw recall and the original tape persist.

Forward coverage uses ClosedKey refinement/current focal ledger/local pair
readback to identify the cut with an actual cut at h, hence J by actualCut.
It is Good and has the proper forced completion. Reverse coverage gives every
positive target atom. Neither implication assumes the weighted identity.

## Exact weights, arbitrary packages and zero cases

Let Lambda_h be the chronological product of actual foreign alias atoms and
historical never-admitted D atoms. Each conditional alias kernel and each lost
law sums to one at its own actual input; repeated PMF.bind normalization gives
sum Lambda=1 even if later menus depend on earlier choices. A lost value cannot
change other-owner fields; its owner has no further unsent request that visit
and is excluded at its missed row. Remaining menu dependence is integrated
conditionally. Accepted canceled and current pending draws are NOT integrated
here; g,G fix them.

At q let T0 contain original mu(theta) and public Nature atoms, and O0,C0,D0,R0
the source focal,class,proper-value and conditional-cause products.
`proposalRecoveryClosedMass_foreign_products` gives on the matching fiber

    M0=T0 O0 C0 D0,                  M0 K_h(q)=M0 R0.

For a sourceProfile prescribed only at nonterminal histories, first apply
`runBehavioralFrom_congr` at each finite depth to identify run laws with the
normalized trembled profile. This transports reach, ClosedMass, ClosedLaw and
rowwise products; terminal policy differences never execute. Positive finite
M0 permits K=R0. Zero cases retain the multiplied identity. Hidden PUB labels
carry the source posterior factor, not an alias count or native cause law.

Every actual foreign SEND has exactly one location: historical accepted D0,
current issued U_hq, or historical never-admitted Lambda. INCLUDE, copying and
restore add no draw. U includes issued static-later rows, and is their owner-
prefix product by the owner-word factorization. Each query is the actual one
proved above. Focal raw factors remain in A_m. Original scheduler disintegration
and actual mechanical constancy give

    r_N(h) T_h(tau)=A_m T0 D0 U_hq Lambda_h.

Let B_q be the ordinary current block pair law, A the complete focal past plus
v, C the issued foreign cylinder, Z full foreign words, a=B_q[A], b_z=B_q[Z=z].
The per-word calculation gives on every positive compatible augmented atom

    Q(z,true)=b_z 1[C(z)],
    F(g,G)=B_q[A,Z=z,(g,G)]/(a*b_z).

Substitute in the DEFINITION of W, canceling U and b_z. For fixed g,G the
inverses give unique q,z; summing Lambda leaves A_m T0 D0 R0 beta/a, where
beta=B_q[(g,G)]. Split the dependent ordinary factors into focal past/current/
later and foreign past/later relative to row k:

    a=D_i,past D_i(v),
    beta/a=D_i,later D_f,past D_f,later.

Let O1,C1 be source own/class products q-to-g. Then

    O_J=O0 O1,                 C_J=C0 C1,
    r_S(g)=T0 O0 C0 D0 R0 O1 C1 D_f,past,
    H_v(g,G)=D_i,later D_f,later.

Multiplication by O_J C_J gives the EXACT cut rectangle. The current D_i(v)
cancels inside a, not as an external factor. All later factors read updated
queries. Excluded deterministic rows contribute one. For an arbitrary package,
actualCut fixes J via an actual cut, the legal encoded COMMIT is unique from
its binding data, and full-information own/class constancy fixes its factors.

Without an index anchor A_m=0 and `annotatedForcedBlockWeight_anchor` makes W
zero. Wrong J, non-Good cuts and unsupported completions have zero W by forward
coverage; positive RHS has reverse coverage. Legal source histories already
retain supported initialization/transitions; unsupported initializer tuples do
not introduce positive history atoms. No division by zero is asserted.

O_J is positive finite from its supported anchor's finite focal product.
`proposalRecovery_foreign_class_eq_of_information`,
`proposalRecovery_foreign_class_pos_of_good` and
`proposalRecoveryForeignProducts_finite` give the C_J assertions. S is positive
via the Good anchor and bounded by source information mass at the checked
decision-information antichain. To sum completions a proper v exists: P>0 gives
a true admission bit; its offered witness includes a proper response. Equality
with the specified binding layout transports its payload type. No inhabited-
value-type assumption is added.

Sum over g,G using H_v mass one, then over m:

    O_J C_J sum_(m,g,G) W = S sum_m A_m.

Total W is at most native information mass: original tape,K,Q+,F are normalized
on retained fibers and gates only delete mass. Since S>0 is finite, sum A is
finite. Positive qualification plus all-K positivity gives a positive W atom,
hence sum A>0. Outer sums use nonnegative ENNReal Tonelli; no finiteness of the
whole history space or Nature support is assumed.

## Actual stopped payoff and same-tape terminal attachment

For every positive actual h and original supported tau, insert any legal proper
c once. `stoppedFinish_gate_seed_joint` disintegrates the ACTUAL final posterior-
tape/gate/terminal law back to this same prefix tape, not a refreshed finish.
`ownedAcceptanceWord_available_bindings_eq`, the unflagged stopped acceptance-
word theorem and `attemptUntil_gate_iff` identify b(h,tau) on EVERY supported
stop, including false. Operational request, after-processing, capacity and
timing facts supply their actual postresponse hypotheses. CurrentStep inserts
c even if its historical policy probability was zero.

On b=true all active bindings finish with exclusions E. Apply
`phaseProposalUnflagged_stopped_binding_word_from_retained_entry` to the actual
postresponse anchor retaining fresh a.
`ReservedEpoch.active_after_processing` applies at the actual fixed-tape active prefix before c;
`respond_environmentRecall` preserves that cursor, transporting after-processing
to the actual post-c anchor even when c had zero historical policy weight.
Its full-word law is the graph continuation from the emission frontier.
`emitted_frontier_conditional` identifies it with
the original graph law conditioned on I PLUS c. Actual proper recalled
preparations and c prove its proper-frontier premise. This is post-c conditioning,
not replacement by a pre-response marginal.

For EVERY q in K support the independent row calculation gives the same FULL
semantic word law conditioned on I plus v. All-K positivity was proved before
annotation support. Choose a supported Q+ word to satisfy explicit pairLaw;
it identifies the enriched source pair measure with Q+.bind F. No weighted
reconstruction or historical native prescription is used here.

Glue physical stop law L and source pair law S_q over their common FULL word w:

    Pi(a,s)=L(a) S_q(s)/Pr[w]

on positive equal-word fibers, zero otherwise. Summing either fiber proves
both marginals. Every supported joint atom has the same complete word. The
following deterministic attachment is necessary in addition to that marginal
calculation.

The actual footprint gives before/raw/ending controls, PhaseClosingEffect,
Finished and excluded=E. Carry the SAME entry witness through the unfinished
attempt with `prefix_at_same_attempt` and `transfer_binding_readback`. Archive
stability makes its lifted entry c, whose full erased history equals q's.
`ordinary_closing_binding_checkpoint` identifies the actual drained
phaseProposalBindingWord at the SAME block/embedding/E with commitInstructionWord.

For the full witness use `raw_closing_checkpoint`, obtaining rawW, its actual
checkpoint-transfer equation and rawHistory. Apply
`rawW.completed_binding_history` with installed phase, Finished and no new
excluded phase owner. It returns completedWitness, retained path, instruction
word, ProposalDelta and settled equation. Transfer_binding_readback and rawHistory
identify its suffix with that SAME decoder word. This is the full checked
construction used in `PhaseProposalCleanBindingGain`, not an identification of
an existential checkpoint with an unrelated full witness.

The source coupling retains its Attempt joints and ordinary enriched labels.
The actual archive selector is false at binding events and Valid forbids a
REVEAL proposal on COMMIT. Equal semantic words therefore lift to equal enriched
suffixes, both retaining their entries and having length n within the maximal
commit window. `binding_close_erased_history` gives FULL erased completed-history
equality. Old hidden PUB labels are handled by entry refinement, not by asserting
equality of the enriched entries themselves.

Proper survivor cells transfer from supported ordinary completion.
`completed_normalized_archived_source` consumes actual rawW/checkpoint,
completedWitness and ProposalDelta, preserving the actual archive through all
subsequent normalization. The true-gate phase has no dirty restore; later
automatic exhaustion is handled by normalization, not ruled out by generation.
False-gate closes need no successful attachment.

The actual normalized end is idle/fresh with saved=current exclusions.
`phaseProposal_fresh_finish_payoff_law` applies with SAME tau and the constructed
proper archived witness. `proposalRecovery_terminal_erased_eq` transfers its
unflagged continuation to G using the FULL erased-history equality and actual
query dependence. Mapping arbitrary utility gives H_G. Future focal choices
read the state AFTER v, not a frozen pre-v tail.

Average over K then Q+,F. Bad h or false b contributes pure none; request
supplies focal alive. Multiply by the SAME r_N(h)T_h(tau) on both sides BEFORE
summing. An arbitrary historical native policy changes only that common prefix
weight. `qualifiedPayoff_mul_informationMass` gives the left numerator; its
positive part regrouped is precisely the defining W sum. Retained mass is P;
termwise gate<=1 gives P<=N with N finite. The complement is EXACTLY N-P.
Zero h/tau/q/word weights vanish before division; P itself may be zero. This
proves the entire aggregate endpoint, including all aliases, proper choices,
original final-posterior tape and false-gate cases.

## Bayes aggregation and the preservation boundary

`qualified_reconstruction` chooses the source package and supplies the concrete
pair law to the weighted primitive. `qualified_binding_law` combines its exact
rectangle with the aggregate endpoint. `sourceCausalPayoff` already filters and
normalizes Good in the source information belief: its denominator is S.
The rectangle summed over m therefore identifies the normalized good-source
terminal law. Common native retained mass is t=P/N, not t divided by another
source-Good mass. The gate bound gives 0<t<=1 when P>0. At P=0 the actual law
is all-none and no positive source normalization is used. Proper-choice
independence follows from the same sum A and source mass, not a new observation
or no-knowledge hypothesis.

The existing signed-gain consumers use the ACTUAL source strategy at J. For
proper-choice probability p and typed lottery L, the affine override has
coefficient a*p, without assuming finite-index source gain nonnegative.
Current ordinary-versus-prescribed error and future same-override error remain
in the stated bounds, along with native-bad and source-Good conditioning errors.
The existing shared limiting sequence controls those errors.

This completes the reviewed mathematical derivations and their composition.
The weighted transport primitive remains to be proved in Lean. Compilation of
its admitted interface and the actual aggregators does not remove their sorryAx
dependence, and this document does not mark concurrent preservation checked.
