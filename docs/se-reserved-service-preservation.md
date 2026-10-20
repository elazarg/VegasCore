# Sequential preservation with reserved shared service

This is a proposed argument for preservation under protected shared service,
retaining concurrent commitments, permanent expulsion and commitment-phase
restart. The end-to-end Lean preservation theorem remains unproved. The
initialized native likelihood argument has independent agent reviews and a
root-agent model audit in the linked analysis. This is neither human review
nor a Lean proof. The network tape may be correlated and its epoch times unknown.
The [exact target](../Vegas/Game/ConcurrentRawSequentialPreservation.lean)
and [likelihood analysis](se-concurrent-likelihood.md) specify the active proof
obligation. No new backend assumptions are adopted by this proposal.

The service is an ideal reserved ledger. Reservation against arbitrary modeled
raw traffic, complete pending observation, a global exclusion floor and the
specified metadata discipline are substantive conditions. Ordinary bounded
latency or independent packet delays alone do not imply them.

The [mechanization plan](se-concurrent-mechanization.md) specifies the checked
deliverable, parallel proof tracks and later common-runtime consolidation.

## The theorem's exact class

Fix a well-formed source setup with its original arbitrary finite-support
joint initial law, finite binding types and a selected intended source
sequential equilibrium sigma. Unbounded binding bid/value choices are outside
this finite binding-type contract. Preserve the original joint input law throughout:
later public histories can correlate types, and retries do not redraw them. Source guards are general
guards of the existing language, not restricted to TRUE.

Use the current public-barrier compilation and actual runtime semantics.
Bindings of one owner follow its source order; inside a private binding block
there are no cross-owner private predecessor edges. Publication readiness also
retains the owner's earlier-event dependencies: only different owners' reveals
can overlap. A phase drains before
closure. A commitment retry restores its checkpoint after permanent exclusion;
publication failure never restores the consumed commitment block. Exclusion
is irreversible.

Impose the following proposed service/observation conditions.

* Nature samples one exogenous mechanical tape from one unconditional prior
  for the entire execution, independently of the original source draw. Its
  coordinates may be correlated across owners and time. Neither block entry
  nor a new public prefix refreshes that prior. The scheduler may update its
  posterior from observed environment recall; that is Bayesian conditioning
  of the same sampled tape. Public-prefix-adaptive block priors are outside
  this contract and this derivation. Hidden meanings, private catalogs and
  arbitrary packet tags do not change the tape or foreign opportunities.
* Shared processing epochs and owner activation opportunities have known finite
  gap bounds. Every eligible coordinate has an authenticated reservation immune
  to all bounded modeled raw traffic. Process its packet before expiry/drain
  when timely; stale/malformed traffic cannot consume another coordinate's
  reservation. The first prompt valid response to each newly ready event is
  admitted before its deadline. The guarantee applies afresh on retries and
  after an owned predecessor completes.
* For a fixed live coordinate and the SAME tape, sending earlier catches the
  same epoch or an earlier one. A focal delay cannot change a foreign owner's
  within-block readiness opportunities or reserved processing. Actual drain
  does not cancel an unfinished foreign chain on the first other owner's miss.
* Usable hidden BINDING values share feasible opaque public commitment and
  metadata footprints. Source-neutral aliases have common aggregate support
  conditional on the semantic emitted packet. Truthful opening plaintext is
  retained as source/enriched disclosure. Conditional on an effective emitted
  packet, normalize positive mass over its ACTUAL local submission preimages;
  literal private evidence-request menus need not match. Premature source
  disclosure is not an unaccounted harmless alias.
* Use completePendingObservation. Every active decision sees every previously
  submitted foreign packet in leaked pending traffic or the ledger; own output
  is recalled. Packets and negative receipts remain retained. No new source
  VALUE choice occurs during an unfinished publication interval.

The finite deadline margins and physical horizon cover these opportunities,
retries, dispatch and expiry work. Candidate capacity is at least the physical
horizon. A submission registers only its named owned slot, and future counted
bindings require a fresh slot. The existing all-raw fresh-slot argument then
provides the required supply even after retries.

Utilities are the existing STATE-BASED source-readout/exclusion payoffs with
the terminal count audit. No extra clock-, message-count-, catalog- or
gas-dependent transfer is included. Surviving native base utility lies in a
finite interval [L_i,U_i], including failed readouts/default zero. Set permanent
exclusion utility a_i <= L_i. Net intended fees are zero. An authentic audit
charges no counted history and collects the first forbidden authored packet
with conditional probability at least eta_i>0 against arbitrary subsequent
strategies. Its funded finite deposit covers the full finite base-payoff range
divided by eta_i. Legal WAIT and bad private preparation are not audited faults.

THEOREM. There is a sequential equilibrium of this raw runtime with exactly
sigma's initialized joint input/outcome/payoff law. No owner is expelled and
no audit charge is collected on its equilibrium paths.

## An enriched auxiliary source game

The usual source publication stores failure when a guard rejects or an opening
is withheld. A native packet can nevertheless reveal its proposed plaintext.
It is therefore incorrect to reuse the old source posterior after such a
disclosure, even for TRUE guards if delivery fails.

Use an AUXILIARY analysis game that retains this information. At publication
record the actual proposed typed value as well as the semantic result. In
addition to truthful publication and withholding, allow failedDisclose(v) for
the actor's actual stored typed value v: the proposal is recorded, the semantic
publication fails and its author is permanently excluded. This represents a
delivery-failed opening at logical resolution. It does not assert that a
physically uncertain sender was already excluded when it sent.

Let Z be the canonical proposal archive, keyed by full source attempt/address
and reveal rank, not timestamps or packet serials. A successful proposal is
already determined by its successful source publication; recording that
duplicate adds no intended-path information. Missing proposals are NONE.
Include guard-failed and delivery-failed proposals. The original logical
transitions, original input law and utilities are unchanged.

This enriched finite game has ONE normalized recovery assessment extending
sigma, as follows. Retain intended values, truthful openings and no omissions.
Every first unilateral extra action either directly fixes its author's floor
or creates a private unopenable/guard-invalid binding. Before commitment close
that substitution is opaque to all foreigners. Guards read public data and
their AUTHOR'S own commitments, so it cannot silently invalidate another clean
owner's private guard. Foreign retained policies continue in their retained
information region. If the deviator itself forces a retry by another omission,
it is permanently excluded. Otherwise the block closes with its debt saved in
the checkpoint before any public divergence. Publication does not restore it.
Thus when a new disclosure first lacks an intended counterpart, the unilateral
deviator's payoff is already its fixed floor against every later continuation.

Replace a complete deviation at its first extra action by any legal intended
continuation. The replacement pays at least the floor pointwise. Until that
action it is an admissible source deviation. Source sequential optimality
therefore bounds the enriched deviation too. This is unilateral clean closure,
not a claim that bad bindings are doomed against simultaneous foreign faults:
foreign omissions really can cancel them before checkpointing.

Choose one fully mixed source consistency sequence. Pin its intended components,
add positive domain floors, and choose all remaining components jointly in a
finite perturbed agent game. Outsider rates are chosen below the fixed intended
passage masses. At retained sites outsider histories have vanishing conditional
mass; the preceding whole-policy comparison gives vanishing regret. At free
sites use the actual jointly optimized conditional inequalities. Take one common
subsequence of all strategies and Bayes beliefs. This determines downstream
priors and continuations together, not independent equilibria at reset words.

For reset transport this completion must be NORMALIZED. Use pools

    K_i = (Erased(NoMiss(source information of i)), Z).

Keep the complete per-rank failure footprint and retired source-address word in
the old normalized component. At fixed actual failure controls the ancillary
inverse-history exchange changes canceled own private draws, preserves Nature,
live checkpoint data and every foreign full input, and preserves Z: a canceled
opaque attempt never entered publication. Consumed disclosures are never erased.
Own-reach factors cancel in Bayes' rule. Corresponding erased refinements have
equal conditional action vectors.

Across NoMiss/reset refinements the vectors need only be affine:

    G_r(x) = c_r + d_r V_K(x),   d_r >= 0.

A foreign miss cancels current private choices and uses the same full refined
failure/address/Z continuation; its contribution is independent of x. A clean
branch supplies V_K. Hence positive reach-weighted pooled optimality implies
optimality at every full refinement with d_r>0; d_r=0 is indifference. The
public logical position remains in each key, so a play cannot visit a pool
twice. The finite pooled agent game consequently has affine component payoffs
and an ordinary perturbed Nash selection. Omission/disclosure flags are compared
separately to the floor, not incorrectly treated as ordinary domain choices.

This extends the existing normalized recovery completion mathematically by
carrying Z through its transition and history-exchange induction. It produces
one global witness, source beliefs and conditional gains at genuine enriched
queries, including source debt and excluded-owner defaults. It does not assume
reduced states are pristine well-formed intended states.

## The actual archive and publication incentives

Work in the counted native game first. Counted uniqueness gives at most one
opening per physical coordinate. Its certificate identifies the actual accepted
typed value. An unusable stored meaning has no counted nonsilent opening.
At a binding callback following publication resolution, complete observation
and own recall recover every old proposal, whether pending, included, rejected
or stale. A later counted response cannot reuse an old event/attempt. Thus the
old canonical Z is finalized and locally reconstructible. The native enriched
query is the existing genuine normalized source query together with this Z.

Inside publication, do NOT erase earlier private observations of pending
plaintext. Compare policies pointwise instead. All source bindings are locked;
no new source value choice is available. Against foreign earliest truthful
responses, couple the same tape and foreign own-coordinate coins. Current
foreign readiness/processing is unaffected by focal timing; newly ready owned
successors receive fresh protection. Guards may use unresolved OWN publication
results: on a surviving prefix they equal fixed binding values; a prior own
failure already fixes the floor. Completed guard verdicts are fixed when ready.

If both focal timing plans survive the interval, both disclose the same fixed
values and reach the same semantic boundary, exclusions and canonical Z.
They therefore face the same enriched source continuation Phi, regardless of
different early observations. Same-tape qualification gives
Q_late <= Q_earliest. Where only the earlier policy survives, its continuation
payoff is at least a_i while the late policy gets a_i; where neither survives,
both get a_i. Unavoidable semantic debt also gives a_i. Earliest truthful
submission is therefore weakly optimal pointwise, including at unsafe late
inputs where its admission probability is less than one. No source posterior
identity at intermediate publication nodes is required.

This permits the auxiliary failedDisclose transition to represent a physical
failed attempt at block resolution. Every observation is retained in the
boundary archive before a new source value decision, and the intervening
publication decisions have the pointwise comparison just proved.

## Binding beliefs, aliases and the NONE case

Use the one enriched source ordinary-domain sequence at actual local queries.
Choose source-neutral timing coins by owner/coordinate/own ready-callback
ordinal, ignoring foreign within-block receipts. Use common effective packet
weights and positive conditional weights within actual private preimages.
Every counted binding is a fresh owned handle with a typed preparation or
failure; every counted nonsilent opening is its truthful accepted typed value
and valid certificate. Other menus are silent as required. This covers the
FULL counted action support, including private aliases and failed preparation.

For a compatible enriched source history and physical skeleton, multiply actual
transition probabilities chronologically. Source choices contribute their
ordinary laws; Nature keeps its ORIGINAL joint law. The remaining weights use
the retained public prefix and source-neutral mechanics under the same
whole-execution tape prior. Integrate virtual
unsubmitted foreign values, sum their private packet preimages and cancel the
focal own-reach factor. Failure/address controls and Z are retained. This is
causal factorization at the ACTUAL full input, not a desired posterior premise
or independence of the final network transcript and source outcome.

For Z(e)=v, the enriched public fiber also determines completed guard checks:
SourceGuardRead uses public data/publications and resolved publication results
for commitment reads. Sum guard-failed truth and failedDisclose histories when
they are observationally indistinguishable. Their physical and auxiliary rate
factors can differ but are common across hidden source worlds on this fiber.
Unchecked future obligations are not retrospectively evaluated.

For Z(e)=NONE, a failed publication can instead mix a forced WAIT from an
unusable binding with optional WAIT from a usable binding. Their factors are
1 and products of timing rates. Exact finite-n cancellation is false here.
Use the following perturbation hierarchy and shadow.

Fix positive ordinary-domain, timing, disclosure and alias floors BEFORE
optimizing free pool weights. They give a lower bound ell_n>0 for each COMPLETE
response needed in the following repair. Choose failed-preparation rate b_n
LAST, with b_n/ell_n^H -> 0 in both source and physical experiments.

Repair ALL foreign failed preparations in a prefix to a typed value at the
SAME handle, keeping occupied slots and emitted binding envelope fixed. Type
inhabitation supplies a value. Use a canonical NONE evidence request for a
binding; for unchanged other openings use their actual accepted-handle
certificate preimages. At every originally forced-silent publication callback
choose permitted WAIT until the SAME expiry. Native public completion, TRUE
binding receipt, eventual publication failure, exclusion, count controls and
Z=NONE remain identical. Other owners' guard inputs use public results, not
the changed hidden binding. Public Nature omits private commitments. Thus the
focal FULL input is preserved. Canceled slot meanings are repaired too.
Immutable inputs and all unmodified live meanings are preserved; only the
designated foreign hidden bad-preparation meanings are replaced, including
their persisted semantic cells. Their PUBLIC publication failures remain the
same. This probability repair is distinct from the later resource allocation
transport, which preserves accepted live meanings exactly.

The histories need not have equal terminal utility. Instead keep their common
chance/mechanical/focal-own-reach coefficient C(h). An original bad history has
weight at most b_n C(h); its repair has weight at least ell_n^H C(h). The map
has a fixed finite preimage bound M, so uniformly at every positive focal fiber

    P_n(foreign preparation failure | I) <= M b_n/ell_n^H -> 0.

The domain floor bound is independent of free optimization, so this choice is
not circular and divides by no unknown limiting reach. Apply the bound in BOTH
the auxiliary and physical experiments. Automatic failed cells of already
excluded owners are matching logical controls, not rare preparation flags.
On the remaining typed/openable worlds availability is source-independent and
the preceding cancellation applies. Bounded payoffs control the two discarded
posterior masses. The resulting transport is APPROXIMATE, with vanishing
error, rather than blanket exact finite-n Bayes equality.

Known own failure is handled separately. Checkpointed debt gives the floor.
Current-attempt debt is canceled only on a foreign reset; without that reset it
gives the floor, while timely completion weakly maximizes survival to the same
reset continuation. Retired own preparation memory is ancillary and cancels
as own reach. None of these cases is called rare at the actor's known input.

## Adaptive timing, retries and one common native limit

Couple focal timing plans using the same tape and foreign own-coordinate coins.
Source barriers, independent private readiness cones, reservations and actual
drain give the SAME foreign per-rank failure/address record J*. If the focal
chain survives, its paired post-reset query agrees in ALL controls and Z:
current canceled commitments never reached publication. The same global
enriched source witness supplies the continuation W_J*. Fresh prompt service
realizes its no-new-fault logical runner for every residual tape.

Catalogs persist. Preserve accepted/input meanings, shadow only dead private
preparations and allocate from actual fresh slots. Different residual fresh
sets need not be bijective; each contains the common residual allocation budget.
Local query and local allocation define one policy at every native fiber.
The state-based source payoff is independent of unused catalog contents.

On a clean surviving branch, an adaptive late value plan is a randomized source
deviation. Its mechanical observations and qualification are jointly neutral
relative to the unexposed source information after the proved transport.
Extend its source policy on failure branches too; replacing those payoffs by
the floor cannot improve it. On a reset branch current values are canceled and
the same J*/Z continuation is used. Since W_J*>=a_i, same-tape qualification
p'_J<=p_J gives

    E[u_late|I] <= sum_J P(J|I)[p'_J X_J+(1-p'_J)a_i]
                <= sum_J P(J|I)[p_J X_J+(1-p_J)a_i].

Source optimality supplies the clean branch; the floor supplies the second
inequality. This is a whole-policy comparison, not a marginal packet lemma.

At finite n compare to the source no-NEW-fault runner with the chosen ordinary
domain laws, not to an allegedly identical full trembling runner. Stop at the
first FUTURE nonprompt/failure coin. Conditional rate r_n and finite horizon H
give probability at most H r_n from every full history. Bounded utilities give
a uniform vanishing continuation error, without dividing by tiny past reach.
Past failures use the query, archive and bad-posterior hierarchy instead.

Let e_n be the maximum positive WHOLE-continuation source policy regret at the
finitely many genuine enriched queries. Along the selected source sequence
e_n->0. The native conditional regrets are at most e_n plus the vanishing
posterior-shadow and future-fault errors. NoMiss refinements may give affine
source vectors c+dV with d>=0 rather than equal vectors; the same pooling
comparison applies. In the physical branch comparison d is a qualification
probability, at most one. Publication inputs use pointwise dominance instead.

All chosen physical profiles are fully mixed on the counted menu. Finite
compactness selects ONE subsequence of all policies and actual Bayes beliefs.
Vanishing conditional regrets and perfect recall give sequential rationality
at every counted input. This constructs a single consistent counted equilibrium,
not a family of unrelated reset assessments.

Finally apply the existing authentic count-audit action-restriction extension
from counted to raw play. It chooses consistent optimal free continuations and
bounds a FIRST forbidden packet against arbitrary later strategies. It assumes
no compliance after a sunk charge and prices no legal WAIT/bad preparation.
It preserves the counted initialized law with zero audit charges.

In the limit the selected intended values and prompt timing occur surely.
Protected service and well-formed intended guards cause no failures. Source
commutation/read stability identifies the original joint input/outcome law;
zero net intended fees and sound audit preserve its payoff law in the mathematical
argument. The initialized transport and this final composition still require Lean
proofs.

## Scope

This is not a theorem about arbitrary asynchronous services, independent-delay
channels, or ordinary capacity-competing chains. Complete pending observation
is an explicit choice. Reservations are against modeled RAW traffic, and
full-block service freezing is stronger than hidden-value blindness alone.
The source guards themselves remain general. The new enriched auxiliary
assessment and approximate native adapter are mathematical constructions, not
existing checked declarations under new names. No current target, source
semantics or runtime rule has been modified or claimed mechanized.

Existing components underlying this argument include the
[global source recovery construction](../Vegas/Game/CommitRecoveryEquilibriumConstruction.lean),
[source ancillary Bayes exchange](../Vegas/Game/CommitRecoveryAncillaryBayes.lean),
[original genuine phase query](../Vegas/Game/PhaseObservableSourceQuery.lean),
[complete packet observation](../Interaction/ReactiveCompleteObservation.lean),
and [terminal audit extension](../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean).
The proposal-archive enrichment and conditional transport arguments motivate the
construction. The initialized reserved-service transport is derived in the
likelihood analysis; those existing declarations alone do not certify the
proposed preservation theorem in Lean.
