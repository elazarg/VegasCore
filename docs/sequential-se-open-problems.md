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
The [correlated-prior analysis](sequential-correlated-prior-analysis.md) gives a
conditioning/gluing route for an existing signal known to every player, with
its outstanding formal adapters. It does not settle generic correlated priors.

## Checked starting points

The permanent-exclusion capstone is
`Vegas.recovery_intended_raw_sequentialEquilibrium_preserved` in
[RecoverySequentialCompilation](../Vegas/Game/RecoverySequentialCompilation.lean).
It compiles the sequential graph, uses the supplied runtime's relative deadline
durations, and quantifies over a supplied scheduler and pending-observation rule.
It constructs an actual raw-runtime assessment with whole-continuation
sequential rationality. Its supported paths exclude nobody, incur no count-audit
charge, and preserve the exact joint law of typed source readout and realized
settled payoff vector. The complete typed terminal store retains the original
initial cells. Applying the fixed source initial-state and public-outcome
readers therefore retains their joint law too; the utility's parameter reader
does not restrict this typed-store conclusion.

The monetary specialization
`Vegas.Recovery.intended_raw_programPayments_preserved` in
[RecoveryPaymentPreservation](../Vegas/Game/RecoveryPaymentPreservation.lean)
additionally retains executable cash with the initial reader and full typed
store. It separates valuation, declared exit valuation and exit transfer.

The substantive premises remain:

* Well-formed source syntax, finite intended histories, finitely many players,
  and finite physical nature for the actual bounded execution.
* Private initial inputs and commitments are independent of the remainder
  conditional on a signal determined by existing public initial inputs.
* The actual raw-history service supplies opportunity, protected inclusion and
  completion. The opportunity and inclusion bounds sum to strictly less than
  each owned event's supplied relative deadline.
* The finite wire menu covers relevant initial and output values, and the
  candidate reserve exceeds the owner's binding-event count as stated in these
  capstones.
* Utilities have supplied bounds, and each excluded owner's fixed payoff is no
  greater than its utility at every intended terminal readout.
* Authentic count evidence has uniform observation coverage and delivery
  coverage conditional on the entire observed list; their product times the
  deposit covers the stated utility spread, including the exclusion override
  and zero fallback.

There is no complete-pending-observation premise in the recovery theorems and no
independent-per-message-delay premise. Those facts distinguish their scope
from the deferred concurrent construction. The evidence-coverage premise still
needs an operational producer; arbitrary pending observation does not produce
it automatically.

## First priority: an explicit audit backend

This is a deployment/refinement obligation, rather than a defect in the
conditional theorem. Inspect the exact definitions
`Vegas.EventGraphRuntime.CountEvidenceCoverage` in
[ReactiveCountAudit](../Vegas/Pending/ReactiveCountAudit.lean).
Count evidence includes a signed envelope and the signed traffic list against
which its serial is judged. That traffic is the model's actual emission record;
it is not automatically a publicly available ledger.

Coverage is stronger than authenticity. For every forbidden actual evidence
item it lower-bounds observation, and then lower-bounds delivery at every
supported observed list containing that item. Dependence between censorship
and observation is allowed, but the conditional lower bound must still hold.
This rules out just multiplying unrelated unconditional averages.

The next concrete task is to specify who obtains the needed signed evidence,
how missing earlier messages affect verification, who publishes the evidence,
and why publication receives the claimed coverage before settlement. Derive
the existing coverage definition from those operations. Include packets
sent after exclusion and packets rejected by the game. A verifier alone, an
honest-relayer assertion, or a complete-evidence example does not discharge
availability for a realistic partially observed network.

Traffic rejected before ledger inclusion needs a separate capture route.
Recording rejected contract calls alone does not establish evidence coverage
for packets that cannot enter the ledger at all.

Start with a small complete operational example and state its availability
assumption openly. Then weaken capture or delivery while preserving a positive
conditional lower bound. The existing deposit inequality localizes the cost of
such a weakening. If the lower bound becomes zero where disclosure is
profitable, increased finite deposits alone cannot recover this deterrence
argument. That observation identifies a proof limitation; a game-level
impossibility claim additionally needs a complete equilibrium counterexample.

## Second priority: weaken the private-prior condition

The current hypothesis is precisely conditional independence, not merely
pairwise independence. It excludes correlated hands and signals not explained
by the existing public initial inputs. Introducing a new public latent signal
changes the game and therefore is not a general solution.

Two proof uses should be separated. Hidden-cell splicing needs supported
repaired initial states. Prior transport also uses a constant multiplicative
change of weight across repaired histories. Rectangular support can address
the first without addressing the second; card-dealing priors can fail even
the first. Full support alone does not prove the required common continuation
optimizer.

A manageable first result retains rectangular support but allows a correlated
prior. Show directly that the actual timing components have a common best
choice at every pooled information site, or transport their relevant gain
observables through the nonconstant likelihood ratio. Keep the actual legal
deviation family, continuation payoffs and the one common fully mixed
consistency sequence. Assuming a common-best property at the final preservation
interface exposes an adapter; deriving it from the runtime is the research
result.

Next try a small nonrectangular prior, such as two correlated private bits with
one impossible joint state. Either construct source-faithful supported repairs
without splicing arbitrary cells, or give an exact failure of preservation.
A failure of the existing splicing or pooling lemma only refutes that proof
route. A preservation counterexample must fix one valid intended SE and show
that every target SE changes the required joint law under the retained service
and audit assumptions.

This problem is independent of the concurrent proposal's independence of
message service. Do not import that network premise into the non-concurrent
runtime definitions.

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
