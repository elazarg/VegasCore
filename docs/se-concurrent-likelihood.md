# Concurrent qualified likelihood and causal payoff

This document records the mathematical argument for the four primitive
obligations used by `QualifiedBindingLaw`: `qualified_source_site`,
`foreign_posterior_cut_pair`, `qualified_annotation_pushforward`, and
`annotated_stopped_payoff`. The argument retains their original hypotheses.
The source-site, foreign posterior pair and stopped-payoff primitives are
Lean-checked. Weighted transport remains admitted: its global source-image,
supported replay, augmented inverse and atom-ledger proofs are not yet
Lean-verified. The mathematical derivation below does not close that obligation
or establish unconditional concurrent preservation in Lean. The actual pre-SEND
query bridge remains mathematically open: its owner-visible partial-prefix,
chronological window and proposal-archive joins need a complete reviewed
derivation. Mechanization is paused at this boundary.

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

## Domain and the two directions

Fix a mechanical word m and original tape tau having a qualified positive
anchor h*, with final control c*. Fix the original proper choice v. Write w for
ONE summand of `annotatedForcedBlockWeight`, indexed by (h,q,z,g,G), not its sum.
Here q is the closed-entry annotation and z the whole structural foreign word.
Write B_q for the ordinary source pair, split at k = event-low in the current
block. H_v is the ORIGINAL `sourceForcedBlock` at g.

The source domain is Good(g), info_i(g)=source.site, reach(g)>0, H_v(g,G)>0.
The auxiliary coordinates are one raw alias at each actual foreign callback,
and one proper value at each HISTORICAL never-admitted foreign first authored
registration. All other slots are deterministically empty. Initial, focal,
historically accepted-but-canceled, and current-issued handles have no free
proper-value coordinate. Lists have the fixed raw length and the actual
reverse chronological convention of `RawReplayChoice`; arbitrary padded lists
are not in this domain. The law is sequential, at reconstructed actual inputs.

First derive consequences of an arbitrary positive original w summand. This
direction can use h's ACTUAL execution; it must not assume reconstruction.
Then construct the execution for every supported source pair and auxiliary
record using h*'s skeleton. These two arguments establish the augmented inverse.

## Positive original summand: entry, pair, cut, word

1. Unfold `annotatedPrefixWeight` and `annotatedForcedBlockWeight`. Nonzero w
implies the exact native reach and tape atoms are nonzero, native foreign
goodness, focal survival, word(h)=m, admission=true, K_h(q)>0, and positive
posterior word and forced-joint atoms. Canonical source support follows from
`prescribed_source_history_positive`; it is not inferred from reconstruction.
`annotatedPrefixWeight_support` gives ClosedKey(q)=ClosedKey(canonicalSource h)
and (z,true) in the actual ordinary foreign joint support.

2. ClosedKey literally retains the WHOLE original joint input, full focal
information, chronological cause word and goodness. `closed_key_entry_erased_history`
gives Good(q) and equality of q's whole erased history with h's actual selected
entry cursor. `proposalRecoveryClosedKey_depth` fixes its exact depth d.
In particular q is not an arbitrary state with the same endpoint metadata.
The erased history includes all owners' erased signals and proposal deltas;
its depth-indexed prefixes therefore have the same erased signals/deltas.

3. Use the CHECKED concrete `ForeignPosteriorCutPairAtoms`, not merely the
mixture field of `ForeignPosteriorCutPair`. For the supported (z,true), its
identity is

    b * posterior(z,true) * F_z(g,G)
      = if observed(g,G) and sourceRead(G)=z then B_q(g,G) else 0,

where b=B_q[observed]>0. The left side is positive, so B_q(g,G)>0,
observed(g,G)=true and sourceRead(G)=z. Support of the actual two finite runs
gives q <= g <= G, with depths d+k and d+block.length. Hence q is the unique
depth-d prefix of g. The ordinary current COMMIT run has no new missing rows;
inherited exclusions execute their prescribed deterministic automatic rows.
Good(q) consequently extends to g. The positive pair's own observation fixes
all earlier focal issued rows and the selected proper v. Full source support
supplies reach(g)>0 under the prescribed source profile. Identification with
the package's forced choice waits for the full-information conclusion below.

4. To identify FULL info_i(g), start with equality of the full focal entry
information from ClosedKey, not merely erased information. Induct over the k
current COMMIT rows and compare with h's canonical binding cut. Each row has
the same static address, saved phase, generation and inherited exclusion mask.
COMMIT adds neither a public sample nor a proposal delta. An inherited row has
the same absent action and failure cell. An active foreign row adds a binding
hidden from i, with no new exclusion. An earlier focal row has the value and
action fixed by `issuedLedger_iff_prefix_at_request`: readiness and the clean
unsent focal request ensure those earlier own rows were accepted, and the
ledger fixes their entire owner-prefix word, not only its last value. Thus
every focal observed signal and own action is equal, row by row. The two
information histories, not just their terminal views, are equal. Apply
`QualifiedBindingSource.actualCut` to h's actual canonical cut: info_i(g)=J.
At this identified site the package's encoded move has the specified proper
binding data. Uniqueness of the legal COMMIT move with those data identifies it
with the observed v row. The actual remaining ordinary rows of G therefore
give H_v(g,G)>0 directly from `sourceForcedBlock`'s definition.
This also identifies q's depth relative to the FIXED anchor h*: equal full
source information gives equal cut trace lengths; the same mechanical public
phase and selected event give k_h=k_h*. Since the positive pair has
length(g)=length(q)+k_h, q has exactly h*'s entry depth. Thus the uniqueness
assertion used by the inverse is across representatives, not only relative to h.

5. The source readback in the concrete proof is `foreignRead (reconstruct G)`.
`ordinary_source_structural_projection` supplies the actual target Attempt a
from q's entry and gives reconstruct(G)=a.withoutMisses empty entry. Thus z is
its foreign history (focal coordinate empty). For excluded owners it contains
the deterministic synthetic failure suffix. Do NOT identify this structural
Config with G's whole actual Config: registry and history can differ. This
calculation identifies z uniquely from the actual q,G trace. Attempt witness
independence follows from literal joints (`structural_replay_eq_of_joints` /
`structural_owned_history_of_joints`). All actual terminal typed state and
private history remain those of G; structuralization is used only for z.

## Source image for reconstruction: simultaneous finite invariant

Now fix an arbitrary supported source pair (g,G) in the domain. Use the same
G and final reference catalogue c* throughout. Map every source prefix of h*'s
canonical cut to g by `source_prefix_correspondence`. This maps ALL literal
depths, so it fixes the intervals of every historical visit, including retries;
it does not search by generation alone. Current unfinished rows use G's actual
current-block extension. The mapped q is the depth-d prefix of g.

For a prepared handle k, retain its immutable signed origin
(owner, first emission, attempt, event). Its target value is read at that exact
source row in G if historically admitted or currently issued; only a historical
never-admitted proper handle reads the auxiliary map. Input fields read G's
whole original joint input. Failed focal registrations remain failed.

Induct simultaneously over source visits, their rows, and intervening public
instructions. At each boundary retain: (a) target-entry and target-saved typed
reference agreement; (b) registry/revelation and exclusion/generation metadata;
(c) the actual TARGET attempted histories and their depth-indexed observations
and proposals; (d) the signed origin of every accepted field in current, saved
and archived reference snapshots; (e) assigned raw drained images for completed
visits. The typed and history components are separate. The induction never
equates target private histories with reference private histories.

Initialization: `State.swap_config` and `sourceSnapshotPair` on input refs map
each original typed input to the corresponding component of G's initial tuple.
This is the native encoding of that WHOLE tuple. Initial current and entry are
the same image and retired is empty. Source initialization uses the same tuple.
Full focal information fixes its focal/public components; correlated foreign
components need not equal the anchor's. No product of input marginals occurs.

For each completed COMMIT interval, `source_target_entries` gives matching
residual types and `source_attempt_of_literal_window` its actual target Attempt.
Entry typed agreement is the preceding induction clause, not a consequence of
those metadata APIs. At each row preserve old refs and add the new ref as follows.

* Inherited excluded: receipt order gives no accepted handle; source and assigned
  native reads are failure, and no owned action or proper draw is added.
* Active omitted: the pre/post full focal signals identify the new exclusion,
  so `source_binding_data_transport` gives target failure with missing=true.
  The assigned native accepted map is empty at this event and its read is failure.
* Active accepted proper: obtain the SAME-visit raw `BindingStamp` from
  `raw_handle_bindingStamp`, `phaseLiveBindingStamp_history`, actual issuance
  and `handle_attempt_eq`; copy it through environment/drain table preservation.
  Its lower-rank alternative is impossible at the current block row. Its other
  alternative identifies the actual emitted signed message and exact attempt.
  `sourceHandleMeaning_of_emission` therefore reads `sourceBindingAt` at THIS
  row of G. `source_binding_data_transport` makes this the actual target choice,
  missing=false. `assigned_completed_binding_read` obtains the same assigned
  store and bindingResult using the actual retained current/entry/retired witness.
  A transient drained image is not silently treated as a selected snapshot.
* Active accepted BAD: native foreign goodness makes the author focal. Its
  literal target action is the same BAD by full focal recall. The retained
  failure read and `sourceHandleMeaning_of_focal_failure`, with no focal lost
  entry, give assigned store/result failure and missing=false.

These four exhaustive cases are precisely the three table-read clauses.
Field extension gives the decoded raw target typed state. Advancing receipt
order uses `after_missing` or `raise_low`. All rows use the same raw drain,
same G,c* and same restricted lost map. Literal interval length makes Finished
true exactly at its final row; no additional trace interval is inserted.

Closing has three exhaustive cases, determined by entry/final exclusion sets
and static block owners. Clean saves the decoded RAW target state/history.
Retry restores the IH saved typed state, registry, revelations and accepted
origins, replaces its history by the RAW TARGET attempted history, records the
raw image in retired, and increments generation. Exhaustion performs that same
restore/history replacement, adds the deterministic failed block cells, archives
raw and advances without a second attempted word or a generation increment.
The next automatic visit is a separate interval. These are the definitions
exposed by `sourceClose_of_*_bindingPhase`; `sourceSnapshotAssignment_normalize`
supplies the matching native equations for current, entry and every retired
snapshot. FailureExtension is preserved by inclusion and failed added cells;
the failure/public status of existing fields is unchanged by assignment.

At SAMPLE, full focal public signals fix the actual outcome. Extend refs by
that same public value; the sample law reads the same public environment.
At PUB, a live accepted output has a clean origin: dirty restore removes new
accepted fields, old signed packets have the wrong generation/phase afterwards,
and fixed-handle uniqueness prevents reallocation. Old saved fields persist.
The addressed proposal delta, transferred by full focal history, forces the
target binding to equal the disclosed x BEFORE guard evaluation. Combined with
the retained origin, this is RevealFixed. Initial fields instead use input
readback. Thus the guard reads equal operands, including failed public results;
target hidden disclosure labels may differ, but the public result, refs and
registry/revelation extension agree. Retain the target history, not its reference
label. This closes every simultaneous boundary clause for public instructions.

## Unfinished current image and every callback query

The following is the intended route, not a completed proof of the query clause.
Exact current native/source exclusion equality is too strong for historical
dirty attempts. The existing window API accommodates current-mask differences;
the literal target prefix, visible-cell readback, past/window signal relation
and archive transfer remain to be established over the exact actual-trace domain.

There is no claimed completed-visit equality for the unfinished final block.
Retain its old saved refs and the assigned value of each actually accepted
current field, plus immutable meanings of issued pending candidates. Target
meanings for ALL issued current rows, including static rows after the focal
cut, are read from G. A later row of G does not assert native delivery.

At an actual pre-SEND owner request, readiness makes its earlier own rows
accepted. Its own initial, saved and earlier-current fields therefore have
exactly the target values just established; other-owner private rows are masked.
Historical windows and proposals are carried by the invariant. Only current
interval exclusion differences remain. `source_query_of_live_window` removes
exactly these with NoMiss: common attempt start is signal length minus row
offset, pre-start signals are already equal, and within the interval generation,
saved rank and typed views agree. The owner is active at this row; no assertion
of final survival is used. Actual initialized trace plus current actor gives
`observedSourceArchive_eq_submitted`; target proposals give the same archive.
Thus this is equality of the entire actual query, including historical retries
and proposals, at every callback. For a lost draw the kernel is evaluated before
registration; freshness locality makes it independent of that new coordinate.

Focal lost historical SEND cannot occur in THIS runtime. `settle` checks
`phase.Finished drained` (all phase events complete) BEFORE dirty restore,
retry or exhaustion. An earlier foreign miss does not immediately roll back
an outstanding focal row. `drain` only completes already-excluded owners and
preserves exclusions and accepted tables. Thus at retirement a focal event
has completed; absent its accepted receipt, `publicView_missedBinding` and
`SuffixExclusionRecord.excluded` permanently exclude the focal owner, contrary
to the final live request. A distinct accepted packet cannot substitute for
the focal emitted packet: counted one-packet-per-event and authenticated
emission uniqueness exclude that duplicate. Foreign failure CAN cause a later
rollback of an ALREADY ACCEPTED focal value; this is a canceled accepted value,
retained literally in focal recall, not a free lost draw. All other focal
values/actions are fixed by full focal information, including canceled BAD.
Consequently its full raw input/recall and literal legal raw action are retained.
No claim of equality under arbitrary fabricated foreign recall is needed; query
transport is used only on the actual initialized partial trace.

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

## Actual replay, extraction and both readbacks

Replay h*'s raw skeleton from G's original initializer. At each foreign callback
choose the proper value determined above, or sample the one new lost value,
then sample `splitKernel` at the ACTUAL reconstructed input and chosen class.
Canonical BIND legality follows from `sourceSnapshot_binding_available` with
same fresh serial, equal network, actual CountRecall and outputValues. PUB
legality uses its live successful binding/RevealFixed. WAIT/already-sent cases
use their actual silence classes. `properBinding_calls_eq` and count correctness
give the same packet/effect for every supported alias in the chosen class.
FullValues and strict class/alias mixing give positive behavioral atoms.

Keep literal focal actions and the same environment command/outcome. Binding
and opening handle commutation, rejection, environment and normalize assignment
equations give the next assigned state. Network, receipts, freshness, actor,
remaining and environment recall are equal; keep the actual sampled foreign
recalls. This proves actual trace support inductively, BEFORE mechanical
constancy. Fresh lost-map extension is invisible at every earlier current/saved/
retired snapshot. Before first authored registration the handle is fresh;
fixed-candidate monotonicity makes it fresh in every earlier current snapshot,
and saved/retired candidate preservation gives the same fact there. Accepted
fields consult only nonfresh handles. Although `sourceHandlePairs` reads the
final catalogue c*, `swapCandidate_fresh` makes its changed permutation invisible
at an earlier fresh candidate. Initial fields read G directly. Thus both the
fields and catalogues of all earlier assigned snapshots are unchanged. A
never-admitted but already submitted handle is not fresh and cannot be treated
as a new coordinate. No later choice changes
an already used kernel. The actual word and focal site persist. Original tape
commands read the same public cursor; `ownedAcceptanceWord` congruences preserve
the actual true admission bit. No new tape is sampled.

The canonical entry of this replay has ClosedKey equal q: same whole base,
focal information, literal commitment causes, public outcomes and proposal
classes; only permitted hidden PUB labels may differ. Prescribed positive source
reach makes K(q)>0. The assigned issued rows make observed(g,G) true. Ordinary
pair support and its concrete per-word identity then give positive annotation
at the uniquely defined structural z. This establishes coverage from EVERY
supported source pair and EVERY supported auxiliary record.

Conversely start with the arbitrary positive summand of the first section.
Equal mechanical words identify raw depths and, at EACH depth, the complete
public network inputs/pending/ledger, current and retired public accepted maps,
attempt namespace, and prepared-slot freshness. Saved accepted maps are recovered
from the earlier save boundary in this same complete chronology; restore copies
them. They are not an extra field of the endpoint public view. Thus actual
signed emitted packets, first fresh registrations and their later acceptance
status agree between h and h*. Internal automatic settle steps are determined
by the same phase syntax, masks and accepted maps; unrolling them preserves
the same classification even when they are not separate raw callbacks. Hence
the historical/current boundary and H/C/L handle slots below are the SAME
slots relative to h and h*, not two independently chosen partitions.
Its historical erased source rows fix every historically admitted proper value,
including canceled values, through the immutable signed origin. Its observed
current ledger fixes every currently issued proper value in G, including pending
ones. Initial values equal G's tuple by ClosedKey. Extract the remaining
historical never-admitted values and every actual foreign raw alias. The same
four-case/readback argument applied to h shows those are exactly the values
required by the replay classes. Prove support of the extracted script AND
equality of the replayed raw prefix to h SIMULTANEOUSLY. Initially the whole
initializer is identical. At the next foreign callback, prefix equality gives
the SAME actual input; disintegrating h's positive response atom gives positive
mass to its extracted alias in precisely that input's splitKernel. A lost
proper value has positive D at this same actual query. Its signed fresh
registration and literal action give the same next execution. At focal steps
the mechanical word fixes the literal action; at environment steps the same
word/tape fixes command/outcome. Deterministic empty slots have mass one.
This extends both prefix equality and supported-script membership, without
using an alias-support claim at an as-yet unidentified reconstructed input.
At the final depth replay(extract(h,q,z,g,G))=(h,q,z). Actual
current/entry/retired states and recalls, not just projections, agree. The
unique depth-d prefix gives q and structural read gives z. Conversely extracting
a replay gives the identical script: actual recall retains the literal alias,
and a fresh signed first registration retains its unique lost value. Deterministic
empty slots are fixed; accepted canceled and current pending values were never
auxiliary slots. These statements are inverses on supported records, not on
all arbitrary lists, and not a bijection of unaugmented source/native histories.

## Exact chronological product, with no missing or doubled draws

Expand native behavioral reach along its finite actual trace, and use ORIGINAL
scheduler/tape disintegration once. At each foreign callback the actual response
atom factors as its actual class atom times its splitKernel alias atom. At a
proper BIND the class atom further contains exactly one D(actualQuery)(value).
`foreign_binding_response_atom` gives this literal factorization as
foreignMechanicalAtom times the queried mapped-value atom times splitKernel;
its proper-preparation flag is already inside foreignMechanicalAtom. It is
not multiplied a second time. `sourceReplayAliases_atom` identifies the raw
script coordinate atom with this typed splitKernel atom.
No callback outside proper foreign BIND introduces D. Mechanical class factors,
focal raw policy factors and the original tape factor give A_m by the checked
mechanicalCoefficient constancy, now applicable to two actual supported histories.
The original correlated initializer atom mu(theta) and public Nature atoms are
T0; neither is an owner factor or an additional auxiliary draw.

Partition proper foreign BIND callbacks by their unique first-emitted signed
handle: (H) historical accepted before the selected entry, including later
canceled; (C) issued in the current block, whether accepted or pending, including
static later rows; (L) historical never admitted. This is exhaustive because
the reference chronology places each callback before or within the current
visit, and a historical handle either was accepted in its signed visit or was
not. It is disjoint because signed origins and first registration are unique.
Retry cannot reuse a nonfresh handle, copying/INCLUDE/restore are not draws, and
each historical accepted source row has exactly its authentic accepted packet.
There are no proper draws for inherited excluded rows or initially allocated
cells. Thus H contributes D0 once per actual historical proper source row;
C contributes the issued owner-prefix cylinder U once per issued row; L
contributes its sampled D to Lambda. Every foreign callback contributes its
alias atom to Lambda, including silent callbacks. No focal D is included here:
focal raw probabilities remain in A_m. Query equality above identifies each D
with the corresponding ACTUAL source query, not a frozen initial query.

Consequently the literal atom identity is

    r_N(h) T_h(tau) = A_m T0 D0 U Lambda(u).

This is a partition of the chronological finite product, not an independence
assertion. Later alias inputs may depend on earlier lost values. Iterated
normalization of the actual sequential kernels proves sum_u Lambda(u)=1.
Map to flat records loses no multiplicity: the typed-response-to-raw-action map
is injective within its actual response subtype, lost slots have fixed unique
handles, and the two readbacks above identify the entire supported record.

## Exact weights, arbitrary packages and zero cases

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

This conditional composition does not complete the weighted mathematical
argument. The global source invariant, exhaustive annotated coverage and exact
atom accounting remain open. The weighted transport primitive is admitted in
Lean; compilation of its interface and aggregators does not remove their
sorryAx dependence. Concurrent preservation remains unproved.
