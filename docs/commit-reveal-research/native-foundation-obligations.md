# Proof obligations for the actual asynchronous runtime

Analysis by Codex. This note maps the current concrete research questions to
existing mathematical APIs. It does not define another backend, change the
runtime, or assert a full raw-menu preservation theorem. The owning declaration
surfaces were inspected with `rg` and `lean-defs.py`; paper arguments and checked
statements are distinguished below.

The [native research agenda](native-research-agenda.md) has been independently
reviewed for scope, quantifiers and allocation. Research effort is focused on
concrete work: accepted late actions, independent review and
integration of the reviewed protected construction. The protected paper proof
needs no additional general foundation. Further foundational work is justified
only by another concrete reported gap; no missing equilibrium-existence theorem
currently warrants a separate research track.

## The concrete question and source scope

The primary source is the finite intended game. A commitment chooses a value
predicted to satisfy its guard; every required opening publishes its immutable
value. The initialized private inputs can be correlated. The actual target
permits private candidate preparation, signed submissions, silence, remembered
packet samples, public builder commands and its implemented terminal audit.
Candidate registration occurs atomically inside a transmitted submission; there
is no separate silent preparation action in the native response alphabet.

The desired full result preserves the joint initialized-parameter, public-result
and realized-net-payoff law, with no charge on initialized equilibrium paths.
Forfeit, deposit and declared public service bounds precede the selected builder
and source equilibrium. Existence of a service-dependent target policy differs
from one common policy using only those public bounds. A specified independent
prior over services is a further, explicitly Bayesian question.

The primary intended source avoids one genuine representation problem, but only
after an induction. In
[IntendedGame](../../Vegas/Source/IntendedGame.lean), `intendedValues` permits all
values if the predicted accepting set is empty. `Setup.WellFormed` supplies
`GuardsSatisfiableFrom`, which quantifies over every supported source chance
outcome and every predicted accepting commitment value. Propagating this property
along every legal intended prefix shows that the fallback is never used there.
This must cover the full-support consistency profiles, not just the selected
equilibrium's initialized paths.

General source games that permit TRUE and FALSE are a separate scope. A rejected
TRUE and FALSE can both become native silence while the original owner recalls
different intentions. An exact original-menu bijection is then false. Existing
[DisclosureAssessment](../../Vegas/Game/DisclosureAssessment.lean) and
[DisclosureBeliefs](../../Vegas/Game/DisclosureBeliefs.lean) reconstruct those
intentions conditionally and compare mixtures of original source deviations.
That machinery is available; its assembly into adaptive native execution is
not supplied by the primary mandatory-effective argument.

Serial execution is the first concrete case. The eventual compiled concurrent
case needs its own observation and decision-recall argument; completion
commutation alone does not establish it.

## What existing APIs already provide

| Existing boundary | What it supplies | What it does not supply |
| --- | --- | --- |
| [First-turn protection](../../Vegas/Game/SourceServiceFirstTurnOpportunity.lean), `firstTurn_inclusionFits` | A first ready owner response fits the deadline under the actual opportunity and timing contract. | Acceptance of an arbitrary packet: the packet must also be canonical, valid and sole. |
| [Canonical decisions](../../Vegas/Pending/ReactiveCanonicalDecision.lean) and [resolution](../../Vegas/Pending/ReactiveCanonicalResolution.lean) | Actual preparation, registration, normalized signed response and authentic opening construction. | Freshness from an arbitrary privately prepared catalogue. Clean-prefix freshness must be proved. |
| [Prefix factorization](../../Vegas/Game/SourceServicePrefixFactorization.lean) and [prefix posterior](../../Vegas/Game/SourceServicePrefixPosterior.lean) | Joint source/full-traffic laws and the complete owner-input posterior, including retained private state and guarded disclosure. | The declarations use specified rosters, timing laws and roster schedulers. They are not an arbitrary adaptive public-scheduler theorem. |
| [Proportional belief transport](../../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean), `bayesBelief_projection_of_proportional_reach` | Exact projection of actual Bayesian beliefs once summed native prefix weights are a common multiple of source weights. | The native proportional-weight identity itself. |
| [Local simulation limit](../../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean), `exists_sequentialEquilibrium_limit_of_local_simulations` | One globally consistent target SE from actual fully mixed Bayes assessments, local terminal-law simulations and initialized law equality. | Packet realization, the observation channel or the continuation simulations. No source-to-native history-length embedding is required. |
| [Component completion](../../GameTheoryExtensions/Analysis/Protocol/ComponentCompletion.lean) and [copied-site limit](../../GameTheoryExtensions/Analysis/Protocol/CopiedSiteLimit.lean) | Coupled full-support component profiles, common Bayesian subsequences and completion at additional decision sites. | Rationality of arbitrary retained late components. Pool optimality must be converted to each member's comparisons. |
| [Terminal audit extension](../../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean), `sequential_equilibrium_extends_of_terminal_audit` | Forward SE extension from a sound restricted game, with arbitrary later policies after an excluded move. | Soundness and positive collection on every retained hidden history; it cannot exclude an audit-clean accepted late action by naming it forbidden. |
| [Native composition](../../Vegas/Game/AsyncIntendedComposition.lean), `intended_raw_sequentialEquilibrium_of_certificate` | Composition from an intended-source sequence certificate through retained/effective/native raw layers, with the specified audit settlement. | A native `PooledLimitCertificate`: this is a substantive hypothesis, not a completed arbitrary-builder result. |

The generic
[ActionRestriction](../../GameTheory/GameTheory/Protocol/ActionRestriction.lean)
preserves trace length, activity, information and one-step kernels. It is useful
between two menus on the same physical execution skeleton. It cannot directly
identify a logical source transition with a variable number of native activation
and response steps. First prove preservation into the restricted physical game;
then use an actual physical menu restriction for the extension problem.

The checked
[public scheduling theorem](../../GameTheoryExtensions/Analysis/Protocol/PublicScheduling.lean)
uses a fixed number of scheduler draws per source transition, and includes the
draw transcript and pending count in player information. It does not directly
realize arbitrary native first-ready stopping. Padding native execution into
that theorem would need an additional proof that padding adds no information or
choices. Direct stopped-prefix laws avoid this unnecessary obligation.

## The missing adaptive prefix bridge

This bridge concerns the proposed strict first-ready restriction of actual
native menus: each owner submits its once-selected canonical intended action at
its first ready response; all other responses have singleton silence menus.
It uses actual runtime views, without publishing a draw count or adding a
dispatch action. The surrounding finite horizon and opportunity/inclusion
contract are the implemented symbolic runtime's assumptions.

Fix a legal intended source history h just before an owned decision. Replay the
native operations, forcing only the earlier logical source actions, initialized
parameters and realized logical chance outcomes in h. Sample the actual public
scheduler and private packet-observation kernels. Stop immediately after the
first ready activation has sampled this owner's input, before its response.
Let Q_h be the law of these complete physical prefixes; it can include different
physical lengths. Let J_i be the owner's actual full information, not an enlarged
transcript invented for the proof.

The concrete coupling obligation is

\[
 Q_h(J_i=J)=Q_{h'}(J_i=J)
 \quad\text{whenever }I_i(h)=I_i(h').                 \tag{1}
\]

The equality need only concern the focal player's full remembered view. It
should not require equality of the complete global private state: foreign
candidate catalogues legitimately differ with foreign secrets. The coupling
does retain the entire scheduler input and its command recall so that adaptive
public scheduling uses equal kernels. It also couples all joint private samples
actually visible to the focal player.

For the primary serial source, earlier successful opening contents are already
source-public at the next genuine decision. Canonical commitments expose only
structural fresh handles. The current owner's catalogue contains its initialized
and previously chosen values and the fixed-slot bookkeeping. These are the
concrete cases that can establish (1); recovering source information alone is
not its proof.

Normalization of Q_h is an obligation, not conditioning on successful future
delivery. Force only positive-support logical chance edges, so the replay's
physical paths remain legal native traces. Then prove along every such path:

- all earlier canonical actions have their original source transition;
- the owner has a first ready response within the timing budget;
- every emitted canonical packet is valid and sole, and its protected receipt
  is an acceptance before expiry;
- the bounded native execution cannot terminate before reaching this decision.

The contract's inclusion field promises a receipt with some acceptance boolean.
Canonical validity and handling facts turn it into acceptance. Completion of
the graph by itself does not say that every event succeeded: the protected
canonical induction is needed to exclude expiry on these replay paths.
Once all replay paths hit the bounded stop, Q_h is a normalized law by ordinary
finite-tree probability accounting.

**Paper adapter.** Suppose this normalization and (1) are established, source
information is recoverable from J, and canonical menus realize every intended
action. Also suppose that from every compatible clean physical prefix, taking
one canonical source action and subsequently copying the source policy gives
the original source continuation's terminal readout law. Finally require that
the actual initialized native law maps to the source initialized law and that
initialized copied terminal readout laws agree for each source profile in the
consistency sequence. Then every source SE lifts to an SE of this strict native
restriction, with its source readout law. The initial premise covers source
chance instructions before the first owned decision and games with no owned
decision; source-site conditions alone could be vacuous.

Here is the direct argument. Take one fully mixed source consistency sequence
sigma_n and copy it at first-ready source choices. For every source prefix h,
actual physical prefix probabilities factor as

\[
 w_n(h)Q_h(x),                                      \tag{2}
\]

because source choices ignore auxiliary physical observations, and logical
chance has its original kernel conditional on the full physical past. This is
a prefix identity; it does not condition on later success. For a native
information value J decoding to source I, sum (2) over all compatible physical
prefixes of every length. Equation (1) gives the same factor for each h in I,
which cancels in Bayes' rule. Actual target beliefs therefore project to the
source Bayesian beliefs at every first-ready source decision.

The assumed pointwise continuation equality now makes both sides of each
native one-shot comparison equal to the corresponding source comparison,
averaged over these projected beliefs. A silence-only site's comparisons are
identically zero. The copied profiles are fully mixed on the retained native
menus. Take their actual Bayesian assessments and one common compact
subsequence, including forced waiting sites. This gives global consistency
even where limiting reach is zero. The existing local-simulation limit theorem
supplies sequential rationality and the initialized law; no new completion
principle or visible stop counter is needed.

In the concrete intended-source application, initialized law equality follows
separately from `serviceInitialLaw` using the actual setup's initialized inputs,
unchanged logical chance, and the acceptance/checkpoint induction. It is not
deduced solely from observation equality at strategic sites.

This adapter also shows why a stronger global independence assumption is
unnecessary. The continuation law must be correct from each compatible physical
prefix, but the conditional distribution of foreign private catalogues need
not be the same. Actual zero audit and zero intrinsic forfeit on these retained
paths require their own accepted-packet and no-miss induction. The existing
roster soundness theorem is not evidence for arbitrary adaptive soundness.

## Concrete obligation map and priority

The reviewed [protected execution construction](native-protected-execution.md)
discharges the protected menu, adaptive coupling and prefix-relative continuation
obligations at paper level. The table distinguishes existing checked ingredients
and the corresponding formal adapters from unresolved mathematical questions
about the larger retained and raw menus.

| Obligation | Present assessment | Leverage and next concrete evidence |
| --- | --- | --- |
| Intended guard satisfaction on all legal prefixes | Checked recursive source predicate and prediction APIs exist; propagation and native alignment remain assembly work. | High: prevents hidden loss of an intended value or opening in full-support profiles. |
| Canonical menu coverage and fixed fresh slots | Actual constructors, value coverage and retained-slot invariants exist. Uniform clean-prefix use under adaptive scheduling is not yet a checked constructor. | High: prove the counted prepared slot stays fresh and within capacity, without falling back to a secret-dependent slot search. |
| Adaptive bounded first-ready channel | The native paper construction supplies normalization and the complete source-fiber coupling; checked roster laws and atomic observation facts supply ingredients. | High formalization value: implement (1) and (2) on actual variable-length histories. No further general paper bridge is missing. |
| Original continuation and zero settlement from every clean prefix | The native paper checkpoint/acceptance construction supplies the conditional law and conformance induction; semantic, first-turn and settlement declarations supply checked ingredients. | High formalization value: implement adaptive prefix-relative readout and audit soundness, including every legal intended source alternative. |
| One globally consistent restricted assessment | Existing Bayesian compactness and local-simulation theorem suffice once the preceding evidence is supplied. | Low need for new theory; instantiate rather than invent another equilibrium completion theorem. |
| Extension through accepted late moves | An accepted late packet can be uncharged. The [native two-late paper negative](native-late-action-analysis.md) rules out a general full-menu extension under the declared contract and its fixed deposit thresholds. | Highest concrete priority: identify further public service or settlement properties supporting a positive, and distinguish SE from weaker PBE. |
| Excluded raw moves and one-time charges | Existing signed exclusion, collection and raw alias APIs cover important classes. Uniform collection must be checked for each excluded class. | High: keep arbitrary later play in the quantifier, and distinguish an uncharged first departure from an already collected penalty. |
| Concurrent genuine choices | Typed completion commutation exists, but current serial channel proof does not settle information or timing opportunities. | Separate later extension; do not count serial success as general concurrency preservation. |

The first-ready positive is a result about a strict physical menu restriction,
not the runtime's larger retained risk menu or its complete raw menu. Components
that are accepted and charged differently on failure can require direct gain
bounds; abstract state or observation erasure alone supplies none.

## Review requirements for a concrete negative

A native impossibility argument must quantify over every target SE that could
preserve the specified joint law. A profitable deviation against one copied
assessment, or a negative reduced subgame, is insufficient. In particular:

- verify source menu, guard satisfiability, candidate bounds, readiness and
  actual publicly observed scheduling for the selected compiled fixture;
- verify the builder contract for every legal play, not only prescribed paths;
- prove why candidate-registration submissions, encodings, early packets,
  withholding, duplicate identifiers and later continuations cannot restore a
  preserving equilibrium;
- allow every type-dependent fully mixed sequence at protected decisions,
  rather than fixing a convenient off-path prior;
- distinguish initialized audit cleanliness, which the preserved joint payoff
  law may force, from unconstrained off-path play after a one-time charge;
- choose the adverse service only after the fixed public collateral constants,
  while retaining all the declared service properties.

The actual audit can charge a player once. A charge already collected is not a
fresh marginal penalty for later packets. Existing completion machinery handles
such continuations by solving their game; it does not make all later messages
unprofitable. This distinction must survive both positive and negative proofs.

Ideal cryptography, finite bounded physical play and funded participants remain
the setting. Fees, capital timing, external trades, coalitions, strategic
producers, computation and deployed capacity/finality guarantees are not supplied
by these adapters. Native signed-message modeling is evidence about the stated
symbolic game, not a certification of a deployed blockchain.

**Status.** The root mathematical review accepted the declaration-based
obligation map and direct paper stopped-prefix adapter, including the explicit
initialized-law premise. The concrete
[protected execution note](native-protected-execution.md) received independent
mathematical acceptance of its complete restricted-game paper construction.
Its adaptive formal adapter remains unformalized. The
[native negative](native-late-action-analysis.md) has a reviewed full-menu paper
construction, with remaining obligations explicitly identified as Lean
formalization. The declared contract alone therefore supplies no general
SE extension. No Lean code, build, adopted checklist or runtime
semantics is changed by this note.
