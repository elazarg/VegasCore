# A finite preservation theorem for partially observed broadcast

For the primary fresh-service construction with direct public-ledger audit,
start with the [end-to-end derivation](se-broadcast-preservation-derivation.md).
It needs neither strategic reporters nor an honest audit monitor. This document
describes the alternative delayed-support timing construction, its reporting
model and the monitored backend, with their separate hypotheses.

This theorem gives a complete mathematical construction for a specified finite
commit–reveal implementation. Its network has ordinary broadcasts with partial
observation, concurrent sending, and partial ledger batches. There is no
confidential channel: a sender does not choose a secret recipient, and a player
does not learn another player's sending history merely because time passes.

The scope matters. The theorem uses the explicit bounded-load, content-blind
network below, ideal authenticated commitments, and funded reporting. It is not
a theorem for every builder satisfying an inclusion deadline, nor a verified
implementation of the current Lean concurrent theorem. The construction makes
the additional assumptions and compiler choices concrete enough to test them
separately.

The detailed derivations are the [service and timing construction](se-asynchronous-fixed-window-construction.md),
the [conditional pre-exit proof](se-asynchronous-pre-exit-construction.md), and
the [authenticated raw-message extension](se-asynchronous-authenticated-construction.md).

There are two useful alternatives to the base construction below. A
[fresh-service construction](se-asynchronous-support-weakening.md) removes
delayed-delivery support and includes deterministic prompt inclusion and
complete observation. A [monitored-lane backend](se-asynchronous-lanes-and-audit-service.md)
replaces publication of all raw variants and strategic report-all with bounded
application work and one audit witness per offending author. Their additional
conditions and composition are stated below. The
[mechanization inventory](se-asynchronous-mechanization-inventory.md) identifies
the existing Lean results and the new implementation adapters.

Both service routes require the stated independence between distinct bodies'
service. Complete observation here does not include the correlated reserved
tape of the current concurrent Lean theorem. Common random outages or congestion
shocks are not covered merely because they respect a delay bound. The compact
audit alternative also assumes reliable evidence capture and forwarding;
its objective verifier removes trust in an accusation, not this availability
assumption.

## Statement and quantifiers

Let G be a finite perfect-recall intended commit–reveal game with a fixed finite
phase layout. In a private-choice block, each player's information is its
phase-entry source information and its own preceding choices. Its legal menus
depend only on those data and are nonempty. Public samples and new public
observations separate blocks. All accepted commitments have designated later
resolve obligations. Initialization may correlate the players' private data
arbitrarily.

Concretely, initialization has finite support and the binding/payload domains
offered to strategic players are finite. Unbounded bids are outside this
statement. The linear source adapter covers every program of the existing
syntax satisfying these finiteness and well-formedness conditions.

Fix the compiler, finite traffic bounds, service, observation kernels and audit
described below. Let F_i be a fixed exclusion payoff, no greater than any base
terminal payoff of player i while it remains active, including failure-handler
and default outcomes. Exclusion permanently sets its base payoff to F_i. Let
U_i bound every base payoff and choose refundable audit collateral

    D_i >= U_i - F_i.

These choices precede the choice of source equilibrium. They do not depend on
the probability that a particular late packet is included. Gas and report costs
are separately funded; they do not change these net game payoffs.

**Theorem.** For every fixed finite service and observation kernel satisfying
the structural and support conditions below, every selected sequential
equilibrium of G has a sequential
equilibrium of this finite raw-message implementation preserving the joint law
of initial source data, typed terminal results, source public results and
realized net game payoffs. There is no exclusion, forfeiture or audit charge on
that limiting law. Players remain able to wait, send late, rebroadcast, choose
malformed messages, and communicate after exclusion. Those actions are not
removed from the target game.

The theorem asserts existence of an implementing equilibrium. It does not say
that every target equilibrium implements the selected source equilibrium.
The likelihood constants may depend on the chosen kernels' positive chance
probabilities. They need not be uniform across the class of services, and the
collateral inequality does not depend on those constants. The kernels are fixed
throughout the perturbation sequence and are not chosen after observing a
deviation. Independent inclusion coins of probability 1/2 give one instance,
not the only service quantified over.

## The compiler

Bundle each owner's choices in a private-choice block into one legal vector.
The probability of that vector is the product of the owner's original
behavioral probabilities. No choice is moved before information the owner was
originally entitled to receive. The [batching proof](se-private-mempool-compilation.md#a-language-level-batched-source-semantics)
transports the source consistency witness and its continuation comparisons,
not just its initialized outcome law.

Batch the transmission, not the disclosure scope. The binding packet contains
one opaque handle per source component, with accepted records naming the
physical block, owner and component index. An opening packet contains only
components belonging to the current original reveal block. Later components
remain hidden across intervening samples or commitments. Distinct components
are distinct binding slots; genuine component openings are not handle reuse.

For the existing linear source syntax, the
[source adapter](se-asynchronous-pre-exit-construction.md#8-the-source-adapter-for-finite-linear-vegas-programs)
derives this block structure from the observation and successor definitions.
Collect reveal vectors without reordering source commitments or samples; apply
their semantic transitions in the original source order. A guard whose inputs
are not all public remains a pending obligation, exactly as in the source.

Use fixed public execution windows. A window becomes ready at r; every player
may broadcast at each subsequent modeled block. Let A be its last protected
broadcast time, and let D=A+Delta be its settlement boundary. A message sent
after A remains possible and may still arrive before D. The contract does not
classify it as a failure merely because its sender waited past A.

The public ledger through D determines success and exclusion before any next
strategic decision. This can be a ledger-computable expiry predicate; it must
not depend on an optional timeout transaction leaving a known miss unannounced.
An extra Delta-long recording interval after closure makes every qualifying
opening broadcast by D public before the next binding choice. Thus an opening
broadcast at a<=D records by a+Delta<=D+Delta, even if its inner game call is stale.

On commitment-window failure, roll back the entire current commitment block
and exclude its missing owners. This does not erase anyone's memories. A saved
binding outside that block retains its resolve obligation. Every such obligation must eventually
be opened, genuinely erased by rollback, or owned by an excluded player. A
deadline discharges each unfinished obligation by exclusion. A retry consumes
at least one previously active owner; successful advance consumes a source
block. These two finite measures bound the controller's execution.

After the first public exclusion, keep the full raw continuation game, including
the chosen rollback and survivor handlers. No all-player abort is required.
The construction will solve that actual continuation game rather than copy a
source strategy into information sets created by failure.

## The network and evidence service

The following defines a class of finite networks, each fixed independently of
the selected source equilibrium. This section uses the delayed-support route;
the fresh-service route below replaces that support condition.

Its initialization installs the original private values without extra public
disclosure. Initial handle names and other auxiliary public metadata are fixed
by public syntax or sampled independently of the whole source realization.
Service and delivery randomness is also independent of that realization; public
source samples retain their original conditional kernels and separate coins.

| Component | Concrete rule |
| --- | --- |
| Broadcast | A player broadcasts a bounded multiset of authenticated bodies through the one network. Each known body has a fixed finite multiplicity bound; there is no smaller aggregate cap that prevents adding the current first entry. |
| Partial observation | Independent body/occurrence receipt coins select who receives each complete envelope. Every permitted pattern, including no new receipt, has positive probability. Selection does not inspect hidden payload values; removing an unseen extra body changes no other receipt law. |
| Qualifying publication | Each distinct qualifying body broadcast at a has its own immutable publication job. Independent body-local coins give every permitted subset of pending nonurgent jobs positive probability; include due jobs compulsorily at a+Delta. A nonurgent inclusion probability must be strictly between zero and one for this route. |
| Capacity | The qualifying application traffic has a fixed finite bound, and capacity/funding covers that whole bound even after deviations. This is not a promise to clear unrelated mempool traffic. |
| Repetition | Repeating a body creates observable broadcast occurrences but no second publication job and cannot reset or cancel the first deadline. |
| Authorization | Canonical authenticated phase and accepted-binding certificates identify the actual installed physical attempt. Historical validity and guard inputs remain verifiable from immutable records. |
| Reporting | After game play, freeze reporters' knowledge. Sponsor every reporter's full bundle of known foreign-authored evidence, and guarantee its inclusion by the audit cutoff. |

The body's identity does not certify a hidden global sending rank. Distinct
conflicting bodies may overtake each other; their publication jobs remain
independent. There is no registry that tells players who sent first.

The independent job construction is stronger than a bare delay bound. It gives
two facts needed by the proof: a protected entry can remain unobserved until
the last protected block, and an unobserved extra body cannot change another
body's delivery or service before an evidence-retaining recipient receives it.
An arbitrary congested or payload-responsive builder need not satisfy either.

Use the ideal commitment and finite authenticated message algebra specified in
the audit construction. In particular, an opaque fresh handle cannot itself
provide a publicly verifiable disclosure of its value; opening authorizations
cannot be forged or predicted before installation. Application bodies do not
contain unaccounted nested signed messages. These are cryptographic and message
domain idealizations, not consequences of contract padding. Ordinary
sender-selected hash commitments and arbitrary side channels require a
separate realization argument.

## Construct the equilibrium before public failure

Fix a fully mixed source witness beta_n for the selected source SE. Its largest
relevant source continuation gain R_n tends to zero.

Before A, use fixed positive, source-independent probabilities for broadcasting
the first entry at each available time. At A, if still unsent, broadcast with
probability 1-epsilon_n. Select the semantic vector using beta_n. After a
protected send, use a fixed full-support distribution over the available
rebroadcast multisets. These choices are independent of the hidden values.

Solve all remaining late operational information agents jointly in one finite
auxiliary game. Each agent is paid the indicator of its owner's completion in
that agent's window. Positive action floors of total mass eta_n give a
constrained Nash equilibrium. Dividing its agent optimality inequality by the
positive reach probability gives conditional completion regret at most eta_n;
there is no inverse-reach error. Protected choices already complete with
probability at least 1-epsilon_n. This constructs one joint timing profile,
including its off-path timing choices.

The essential posterior bound is

    Pr(foreign protected-cutoff miss | any actual pre-exit information set)
        <= C epsilon_n / (1-epsilon_n)^m.

Here C and m depend on the fixed finite implementation, not on n or the mass
of the information set. To prove it, take a history containing a foreign late
broadcast and add that owner's ordinary first broadcast at A. Keep it unseen
through the observed prefix. Its former first broadcast becomes a rebroadcast;
retain every other observed occurrence. The repaired history is still in the
observer's actual information set. Its probability replaces a cutoff-miss
factor epsilon_n by a send factor, with only fixed positive chance/replay
factors lost. The observer's own rare earlier waits cancel exactly. The batch
menu ensures that adding this first entry does not remove a visible replay.
For an entry not yet sent in the original history, perform the comparison on
the equivalent probability space with presampled source vectors, then sum out
those unobserved vectors. This preserves the source factors without dividing
by the limiting probability of an unsent value or an off-path information set.

This is a probability comparison between possible histories of the same
partially observed broadcast game. It neither grants a confidential delivery
mechanism nor changes what any player observes.

## Complete failure play under the same beliefs

Stop copying the source at the first public exclusion. Complete every remaining
raw information agent jointly by a tremble-constrained equilibrium using the
actual entry law induced above. The permanent public exclusion marker separates
these sites from the pre-exit sites. Players retain their entire received and
sent histories, including abandoned attempts.

If xi_n is the handler's total local floor mass and B bounds net utility
differences, each handler local regret is at most B xi_n. At a clean first-exit
entry, the excluded player can remain quiet and obtain exactly F_i; every
continuation pays at most F_i. Perfect recall and finite one-deviation
telescoping therefore give

    F_i - H B xi_n <= handlerValue_i <= F_i.

This is a conditional entry-value bound under the common Bayesian law. It does
not assert equal payoffs at every hidden node or assume rational silence after
an already incurred audit offense.

Before public failure, the posterior repair makes foreign failure uniformly
rare. Subsequent cutoff misses have a finite union bound. Away from those
events, actual value has the form

    F_i + q * (sourceContinuationValue_i - F_i).

At a binding site, old openings are public and current commitments are opaque,
so the source posterior is exactly the required source posterior. At an opening
site, received values can refine the source payoff belief, but content-blind
transport separates that belief from the operational completion probability q.
The source surplus is nonnegative in both cases.

Consequently every pre-exit pure one-step gain is at most

    R_n + B max(epsilon_n, eta_n)
        + 2 B [C epsilon_n/(1-epsilon_n)^m + H' epsilon_n]
        + 2 H B xi_n.

All terms tend to zero. One common subsequence of the fully mixed profiles and
their Bayes beliefs yields an SE of the game with proper pre-exit entries and
the full audited raw handler. Its initialized failure probability tends to
zero, so its limiting joint source law is the selected one.

## Restore every raw pre-exit action

A raw opaque binding can hide an unusable or guard-invalid value. Replace it
in the comparator by an admitted value behind the same opaque handle, retaining
the raw value in a private simulation. No one else's observations change during
the commitment block. If that block rolls back, all these differences disappear
before a genuine opening is authorized. If it is irreversibly saved, stop the
comparison there: its earliest invalid binding dooms its owner to exclusion.
Truthfully completing every own publication eventually checks the false guard;
omitting an indispensable publication also excludes the owner. Earlier own
inputs of that earliest defect agree, and later rollback cannot erase a saved
obligation. An unusable binding similarly cannot satisfy its resolve obligation.
The raw terminal payoff is therefore at most F_i; the clean comparator can
remain quiet and obtain at least F_i.

This argument does not assume that a guard can be checked at its subject's
opening. Its last input can be published later, even after another source
commitment. Nor does it claim that the first changed opening is itself invalid:
a later repaired value could have been valid relative to an earlier bad one.
The argument uses the earliest defect at its irreversible save. After a foreign
exit that rolled back the current block, the states agree and the full raw
handler permits the subsequent bindings without an intended-menu selector.

Suppress other auditable forbidden bodies in the comparator and simulate their flights
using its own independent random coins. Until the first external exposure E,
all other actors' observations and controller effects agree. At E a complete
authenticated body reaches a recipient who can report it. An earlier body
needed for a conflict witness retains its individual publication promise.
The comparator can switch to quiet using its simulated flight coins; it does
not need to observe another player's actual receipt.

Keep this clean-message rule in the handler even though its raw menu permits
misconduct. A new handler binding can be copied literally; if it saves an
unusable or guard-invalid value, the same inevitable-exclusion comparison
stops there. Thus the comparator does not spend its clean reserve on a handler
offense before the exposure comparison needs it.

The positive verifier and sponsored report-all stage collect D_i on E. The
clean comparator obtains at least F_i. If own exclusion or an irreversible bad
save comes first, raw net utility is at most F_i. If none of these events
happens, the shadow differences have been erased and terminal laws agree.
Thus, at every retained pre-exit information set, under any belief and any
extending opponents' profile,

    E[raw net utility - legal comparator utility]
        <= (U_i - F_i - D_i) Pr(E) <= 0.

The comparator is one legal causal policy shared across the information set's
hidden histories. No lower bound on Pr(E) is needed. The finite
action-restriction extension therefore supplies an SE of the reduced raw game.
The existing theorem
`GameTheory.Protocol.InformationModel.ActionRestriction.sequentialEquilibrium_extends_of_continuation_unclocked`
in [PassageRestrictionExtension](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean)
permits the retained game already to have audited raw handlers: match its actual
net payoff and supply the direct continuation comparison. It does not
require all retained off-path histories to be audit clean.
Finally, reporting all foreign evidence is sequentially optimal: with frozen
knowledge and guaranteed final delivery, one's report cannot change the final
set of evidence against oneself. A further vanishing reporting perturbation
lifts the equilibrium to strategic reporting with common consistent beliefs.
Reporting occurs afterward, so it does not change pre-report reach or beliefs.
Its bounded finite-horizon error is uniform over pre-report histories and tends
to zero, as does reporting regret at its actual information sets.
All retained-path charges vanish, preserving the claimed realized net law.

## An alternative without delayed-delivery support

The [fresh-service proof](se-asynchronous-support-weakening.md) replaces the
normal-explanation bound with a direct comparison of foreign-failure branches.
Its exact conditions are stronger than independence of source and network
randomness alone:

* For a not-yet-broadcast body of class e, first broadcast at a has success
  probability p_e(a) by the window deadline. Its service coins are fresh
  conditional on all previous observations and independent of foreign jobs.
  After broadcast, retries and other traffic do not change this job's service.
* Future job and new-message observation kernels restart from the public entry
  state and fresh randomness. Old queue state, allocation counters, receipts
  and proof-byte/order metadata do not affect them.
* After a commitment failure, the entire current block rolls back. The public
  recording barrier precedes the next attempt. Keep live saved bindings and
  their obligations, actual public archives, exclusions and private source data.
  Use fresh physical namespaces for new actions.
* In the intermediate handler, remove positive-audit offenses and first old
  disclosures of already excluded owners. Keep public old-body replays legal,
  with fixed positive source-independent replay probabilities. The prescribed
  handler policies ignore all old-namespace occurrences, including new copies.
  New messages and all current source information remain available. The raw
  extension restores the removed actions by audit or the excluded-owner floor.

For an unsent body, one clock-based policy attains

    q*_e(t) = max_{a >= t} p_e(a)

conditional on every payoff-relevant foreign completion scenario. An adaptive
policy using later receipts cannot do better: its fresh success probability is
an average of p_e(a)'s, each at most this maximum. This does not require p_e to
be monotone in a or require any delayed-delivery pattern to have positive mass.

The reset proof supplies the actual information and action correspondence for
the handler. It is not an instruction that players forget what they observed.
On foreign commitment failure, the current semantic vector is erased from the
effective continuation; on all-player success it has its ordinary source
effect. At a binding site its value consequently has the form

    q*_e(t) * Pr(foreign completion | actual information) * sourceValue(a)
        + a term independent of a.

Every surviving handler payoff is at least the global floor. The same timing
optimizer is therefore optimal on failure branches too. With future timing
trembles epsilon_n and coarse-handler local regret delta_n, the uniform local
bound is max(R_n + 2 B H epsilon_n, delta_n), without a rare-foreign-failure
term. The common Bayesian limit and raw extension give the same joint-law
conclusion as the base theorem.

This alternative quantifies over every fixed finite kernel satisfying these
freshness, reset and observation conditions. It includes deterministic prompt
service, complete observation and partial observation. It does not cover an
arbitrary value-blind kernel whose old signals predict a future body or whose
old traffic changes new receipt probabilities. The two service classes are
alternative sufficient conditions, not an assertion that one contains every
instance of the other.

## An audit service with capacity proportional to authorized work

The [monitored-lane construction](se-asynchronous-lanes-and-audit-service.md)
can replace strategic report-all. An audit service durably captures relevant
complete bodies by a bound, keeps one representative per authorized physical
slot, and detects an intrinsic violation or a conflicting pair. It then
publishes one protected witness for that author and can quarantine further
application work. Capture can occur after another player's receipt; there is
no registration-before-observation or global sending-order assumption.

The contract checks complete positive evidence itself; it does not accept an
auditor's verdict. The backend nevertheless assumes that relevant bodies are
retained and forwarded, that witnesses are assembled, and that the required
reports arrive. One honest service or a proved honest-route coverage condition
can supply this guarantee. Timely inclusion alone starts too late to establish
capture. Neither permissionless reporting nor an auditor bond proves it without
additional dissemination or incentive arguments. The monitored backend is
conditional on that extra availability guarantee.

Before a witness, every first qualifying representative receives an archive
publication job, including stale calls. Inner execution is conditional
separately. After a witness, further publication is unnecessary for deterrence
because the covering charge is already unavoidable. Thus the required
invariant is publication of a retained-prefix body by its bound **or** an
unavoidable charge against its owner by settlement.

Let H_i bound author i's authorized slots, including retries; let a_i bound
one body publication's work, including its component vector; and let e_i bound
one full positive witness and verification. Total ledger work is at most

    sum_i (H_i * a_i + e_i).

It depends on program size, retries and encoding sizes, not on the number of
different values or handles a deviator could try. Per-author application lanes
isolate other players from that flood. A separate protected audit allowance
delivers the one witness before collateral release. There is no strategic
reporting game in this backend. With certain collection the deposit condition
remains D_i >= U_i-F_i; conditional collection q_i requires q_i D_i >= U_i-F_i.

This reduces ledger capacity, not the need for reliable evidence intake.
Bounded capture, authentication/DoS isolation and audit delivery are still
service assumptions. Paying a monitor or reserving a lane does not by itself
prove them.

The two alternatives can be composed concretely. In a clean fixed-window run
there is at most one outstanding first body per author. Give that body's
capture/publication job fresh packet-local randomness and a protected
per-author service bound; start the next window after old first jobs have
recorded. This supplies the fresh timing model. The compact monitor does not
change any clean run. Additional raw jobs can change the run only at a causal
effect with eventual evidence capture, at which point the charge comparison
applies. The audit-clean intermediate handler and the saved-debt/direct-floor
comparisons supply the raw extension at post-failure sites as well.
Here the clean body's completion probability includes capture delay. Per-author
intake must preserve the assumed freshness and cross-author isolation; sharing
a monitor does not itself supply these properties.

## What this settles and what it does not

The construction supplies source comparison, joint late timing, actual-memory
failure continuation, raw deviation control, reporting incentives and the
initialized joint-law conclusion for the specified finite implementations. The
companion proofs give the intermediate probability and coupling details.
No pending message is declared common knowledge before ledger publication.

The principal backend obligations are the selected service class's information
and noninterference properties, bounded funded application work, and actual
evidence capture/delivery. Delayed support and full raw-body publication are
requirements of the base construction, not of every alternative above.
With ideal authenticated commitments given, the remaining audit task is the
message/capture interface and positive verifier. A generic transaction deadline,
a larger deposit, or contract padding alone does not establish them. These
obligations must be checked before applying this theorem to a blockchain model
or claiming that it replaces the current concurrent theorem's observation
hypothesis. No Lean result or frozen checklist item is closed by this hand proof.

The standard existence and consistency ingredients are finite-game equilibrium
existence, perfect-recall behavioral realization, and sequential equilibrium
as a limit of fully mixed Bayesian assessments. The existing bibliography keys
are `Nash1951`, `Kuhn1953` and `KrepsWilson1982`; see
[Nash's original article](https://cs.uwaterloo.ca/~klarson/teaching/F04-886/papers/nash51.pdf)
and [Kreps and Wilson](https://doi.org/10.2307/1912767).
They do not supply the service repair, saved-debt coupling or evidence adapter;
those are the constructions proved here.
