# Non-concurrent sequential-equilibrium preservation: scope and next questions

The retained target is compilation of an intended commit–reveal game to the
actual bounded message runtime. The checked non-concurrent results already
allow partial pending observation. Their main open questions concern the prior,
service and evidence assumptions, and operational realizations of those
assumptions. No counterexample below refutes the checked statements.

The [two-player instance](sequential-se-instances.md) exercises positive latency
and imperfect audit coverage on the same forced-exit runtime as monetary preservation.
The [client scenarios](sequential-client-scenarios.md) check concrete failure
responses and useful information in rejected traffic, separating simple
fallback rules from an explicit client with full sequential rationality.
The [uniform semantic compiler](semantic-client-compiler.md) supplies bounded
raw-menu clients through completion and decoding, with ledger realization
under no pending delivery. Its catalogue premises require finite binding, publication and
initial-input value types. The [diagnostic client analysis](ledger-client-correctness.md)
isolates the belief obligation for a manually prescribed policy; it is not an
additional premise of the semantic compiler.
With at most two players and a single submission opportunity per event, the capstone
accepts arbitrary private priors. The [correlated-prior analysis](sequential-correlated-prior-analysis.md)
discusses the remaining problem with repeated opportunities.

## Checked starting points

The permanent-exclusion capstone is
`Vegas.intended_raw_sequentialEquilibrium_preserved` in
[SequentialCompilation](../Vegas/Game/SequentialCompilation.lean).
It compiles the sequential graph, uses the supplied runtime's relative deadline
durations, and quantifies over a supplied scheduler and pending-observation rule.
It constructs an actual raw-runtime assessment with whole-continuation
sequential rationality. Its supported paths exclude nobody, incur no count-audit
charge, and preserve the exact joint law of typed source readout and realized
settled payoff vector. The complete typed terminal store retains the original
initial cells. Applying the fixed source initial-state and public-outcome
readers therefore retains their joint law too; the utility's parameter reader
does not restrict this typed-store conclusion.

The returned artifact also retains the supplied intended assessment through
[`ClientAssessmentRefinement`](../Vegas/Game/ClientSpecification.lean).
At genuine first source decisions its strategy is the canonical intended law;
its actual replay posterior is the intended posterior, including off-path
sites. Every intended information site has a native realization and raw
counterpart; at each corresponding native site, every legal source history
has an exact replay preimage. Matching legal starts preserve complete normalized
terminal histories jointly with actual settled payoffs and zero charges.
Clean source boundaries retain ordinary source utility, no defaults and no
failed reveals, also for decoded physical clients. These certificates and the
retained one-packet SE concern the same selected assessment as the raw
equilibrium and initialized settled-payoff law.

The monetary specialization
`Vegas.intended_raw_programPayments_preserved` in
[PaymentPreservation](../Vegas/Game/PaymentPreservation.lean)
additionally retains executable cash with the initial reader and full typed
store for every supplied `ClientCompilation`. It uses that artifact's assessment
and the exact physical clients decoded from it, including the output of
`ClientSpec.compile`. It separates valuation, declared exit valuation and exit
transfer, and needs no additional source-equilibrium premise after the artifact
has been supplied.

The substantive premises remain:

* Well-formed source syntax, finite intended histories, finitely many players,
  and finite physical nature for the actual bounded execution.
* Either each player's private initial inputs and commitments are independent of the
  remainder given a signal determined by public initial inputs, or there are at most two
  players and the owner of a ready event cannot pass and get a second chance to submit
  for that event on any legal one-packet history.
* The actual raw-history service supplies opportunity, protected inclusion and
  completion. The opportunity and inclusion bounds sum to strictly less than
  each owned event's supplied relative deadline.
* The finite wire menu covers every value of each binding, publication and
  initial-input type; these types must be finite. The candidate reserve exceeds the owner's binding-event count as stated in these
  capstones.
* Utilities have supplied bounds, and each excluded owner's fixed payoff is no
  greater than its utility at every intended terminal readout.
* Authentic count evidence has uniform observation coverage and delivery
  coverage conditional on the entire observed list; their product times the
  deposit covers the stated utility spread, including the exclusion override
  and zero fallback.

There is no complete-pending-observation premise in the native sequential-preservation theorems and no
independent-per-message-delay premise. Those facts distinguish their scope
from the deferred concurrent construction. The evidence-coverage premise requires a capture and delivery law for the chosen backend.

## First priority: an explicit audit backend

This is a deployment/refinement obligation, rather than a defect in the
conditional theorem. Inspect the exact definitions
`Vegas.EventGraphRuntime.CountEvidenceCoverage` in
[ReactiveCountAudit](../Vegas/Pending/ReactiveCountAudit.lean).
Count evidence includes a signed envelope and the signed traffic list against
which its serial is judged. That traffic is the model's actual emission record;
it is not automatically a publicly available ledger.

For any actual list with a violation by a player, coverage lower-bounds the
probability of observing at least one violation by that player. On each
supported observed list containing one, it lower-bounds the probability of
delivering a witness for the player by the deadline. Per-item bounds also
suffice. Delivery may depend on the entire observation.

The [one-report service](../Vegas/Pending/CountReportSelection.lean) submits
the first forbidden item per sender from the observed list. Its coverage
proof accepts arbitrary partial observations with the capture bound and
conditional timely delivery of each selected witness. With whole-batch
capture and delivery coins, the joint charge-vector law agrees with reporting
the full list. The bounded auction uses that service. The capture law still
takes authenticated count evidence as input.

The [sender archive checker](../Vegas/Pending/CountReportObservation.lean)
constructs count reports from bare observed envelopes. It retains a forbidden
packet of serial `k` when the archive contains each serial below `k` from that
sender. Authentication and unique IDs identify every predecessor the verdict
uses. On every legal prefix, a complete archive for one sender supplies a
report exactly when that sender has a violation. Packets from other senders
are unnecessary. The same binding at serial one has opposite verdicts when
the unseen serial zero is a malformed packet or an earlier copy of the
binding. For a permitted opening of an event-bound field, the verdict on
an authentic subarchive agrees exactly when the archive contains an earlier
matching commitment. Treating an incomplete archive as complete can therefore
both miss violations and accuse a lawful sender. A forbidden submission can
also leave the passive view of blocks and leaked traffic empty.

Early player moves and early audit reports can use the same bounded-inclusion
service. The [player contract](../Vegas/Pending/ReactiveAsyncContract.lean)
protects the owner's sole identifier for its ready event. Its scope stops at
game traffic. If the ledger also protects the watcher's selected reports, the
watcher can submit by a cutoff that leaves one inclusion bound before
settlement. Each selected witness then arrives with conditional probability
one on every supported observation. The capture bound carries through to
collection. [Protected report delivery](../Vegas/Pending/CountReportSelection.lean)

The [zero lower bound](../Interaction/DelayedEvidence.lean) applies when
report delay is unrestricted. In its witness every report is submitted
immediately and included one tick after settlement. Extending bounded
inclusion to reports rules out that service.

In the EVM prototype, the watcher samples blocks and configured pools, and the
contract accepts reports only before its audit window closes. The checked audit judges signed submissions, including unconfirmed
traffic, and distinguishes a second fresh submission from the same packet being
observed again. It checks an opening against the sender's earlier signed
commitment. A contract that checks only accepted commitments needs a separate
correspondence argument for signed but unaccepted commitments. A deployment
also needs to relate its transaction identities and fee replacements to the
fresh serial that the model assigns to each emitted envelope.
Its collection rate depends on its network and inclusion law.
[Watcher](https://github.com/elazarg/vegas/blob/8d306fb21dd0aca30670b6589ca4d1f6e8894c2a/src/main/kotlin/vegas/watcher/Watcher.kt#L54-L109)
· [Contract report](https://github.com/elazarg/vegas/blob/8d306fb21dd0aca30670b6589ca4d1f6e8894c2a/src/main/kotlin/vegas/backend/evm/Solidity.kt#L320-L341)
· [Prototype assumptions](https://github.com/elazarg/vegas/blob/8d306fb21dd0aca30670b6589ca4d1f6e8894c2a/docs/AUDITED-RUNTIME.md#L58-L100)

A positive deployment result would need an authenticated source of witnesses
covering every admissible route, including unconfirmed and rejected traffic,
a contract that verifies the same rule, and a lower bound on report inclusion
conditional on each supported observation containing a witness. The existing
enforcement theorem then uses the product of those bounds. Establishing them
for a specified deployment is a separate obligation from the preservation proof.

## Second priority: weaken the private-prior condition

The checked [prior condition](../Vegas/Game/SequentialPrior.lean) admits every joint
prior, including priors with impossible type pairs, for at most two players with a
single submission opportunity per event. An owner may wait, but cannot then receive
another opportunity to submit for that same pending event. The condition ranges over
off-path decisions too. Raw deviations still use the full bounded message menu.

The repair keeps the responder's hidden cells. Every other initial cell is visible
to the other player, whose observation agrees across the two histories. The repaired
draw therefore equals the original supported draw. A single opportunity also rules
out the late decisions at which the proof has to compare posterior weights.
The [bounded auction](../Vegas/Examples/BoundedAuctionService.lean) consequently
preserves the truthful joint outcome and surplus law under any valuation prior on
such a service. An [explicit event-tagged roster](../Vegas/Examples/BoundedAuctionRoster.lean)
satisfies those conditions for every joint valuation prior. The separately instantiated
periodic service uses uniform private values.

For a builder offering retries, the checked theorem still uses conditional
independence given public initial data. Two players suffice for the support repair
even there. What remains is the comparison of off-path incentives at late decisions
with the same timing information. With more players, the support repair can also
require a new joint draw. Neither limitation establishes failure of preservation.

## Third priority: a physical clock and service realization

Relative deadlines are already configurable; the source-rank calendar is only
an instance. The checked timing condition is
`reaction(event) + inclusion(event) < duration(event)`. The duration starts when
the event becomes ready, not when the game starts or when a player first sees
the event.

The abstract service admits several commands between clock advances. Its
opportunity, protected-inclusion and completion obligations quantify over every
legal raw history, including silence, malformed responses and horizon-terminal
histories. An externally advancing block clock needs a concrete scheduler
realization satisfying those same obligations. An honest-path timing estimate
or a numerical positive margin does not supply that realization.

The checked [two-player instance](sequential-se-instances.md) has event duration
six, reaction and inclusion bounds three and two, and proves the actual service
contract under arbitrary raw play. It combines multiple source decisions with
imperfect evidence capture. Its periodic full-batch scheduler and empty pending
reception are concrete choices to strengthen independently.

Protected inclusion only protects the owner's sole identifier for an event.
It is not a guarantee to flush the pool or include every malformed duplicate.
Any concrete capacity or fee policy must preserve the actual protected service
under all raw deviations. Keep this obligation distinct from the bounded
candidate alphabet required by the game model.

## Further strengthening, after the operational examples

* Quantitative service failures: exact SE preservation uses all-history service
  guarantees. A probabilistic outage model needs a new explicit conclusion,
  such as an approximate incentive/law bound. Conditioning at rare information
  sets must be controlled; an unconditional outage probability is insufficient.
* Exit utility and quit handlers: the checked result gives the failing owner a
  fixed payoff below every intended terminal utility. Replacing it by a
  history-dependent handler needs a sequential incentive bound at actual
  failure sites and rational continuation play, including consistent beliefs.
  The ability to express a handler does not establish that bound.
* Fees and transfers: the monetary theorem preserves its declared cash model.
  Endogenous fees, opportunity costs, external assets and nonlinear utility
  require an explicit extension of payoffs and funding, followed by a new
  preservation or approximation statement.
* Full source games allowing intended silence: the capstones start from the
  intended game in which publications succeed. A policy-law correspondence
  for a larger source game with rational omissions and retry histories is a
  distinct theorem. Pointwise terminal-state correspondence does not transport
  policies, probabilities or unilateral deviations.

For each strengthening, retain the existing theorem as a regression consumer.
Prefer deriving a missing adapter for the actual execution, observation and
settlement machinery. Add a new abstraction only when both the old theorem and
the new example use it. The concurrent research checkpoint remains the place
to recover other designs; resolving these non-concurrent questions does not
require reopening it.

The [archived correlated-prior analysis](https://github.com/elazarg/VegasCore/blob/cb6b8df2d011c678c0c2bc03981feb8b04243048/docs/se-correlated-prior-research.md)
contains the detailed splicing, likelihood-ratio and common-best proposals.
The [archived deadline analysis](https://github.com/elazarg/VegasCore/blob/cb6b8df2d011c678c0c2bc03981feb8b04243048/docs/se-deadline-scope.md)
gives the timing-instance calculation. They are research background with their
own scopes; neither is a checked weakening of the retained capstones.

## Manuscript verification

The strict build checks the retained formal statements and their axiom pins.
A complete manuscript-to-Lean walkthrough of the late-leak statements and
supporting results remains an independent review task: compare each prose
claim, its hypotheses and quantifier order to its exact pin. Passing the source
policy alone does not verify that correspondence. This task does not require
reintroducing concurrent preservation into the active development.
