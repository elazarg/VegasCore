# Ledger requirements for rational commit–reveal games

This research project asks which properties of a blockchain-like service let
an abstract commit–reveal program retain its game-theoretic analysis. It studies
a family of candidate interfaces. **None of these candidates is adopted as
the VegasCore runtime model by appearing here.**

The work is mathematical for now. Written proofs and counterexamples are
separate from machine-checked theorems. Existing code, compiler semantics and
owner-controlled proof checklists are outside this project's editing scope.

In these notes, the **source** is the abstract program's game. The **target**
is the implementation's game, including its actual message, timing and cost
choices. An action described as **raw** means a submission the platform allows,
even if the compiled client would never make it. Each result states which
such actions its mathematical interface includes.

## The question we aim to answer

Fix a class of finite games in which players can choose private values,
commit to them, make decisions using partial information, and open or withhold
their commitments as the program permits. Players remember their observations
and choices. Private values may remain hidden across several phases and may
be correlated between players. Utilities are bounded over the declared game
and deviation space.

Assume ideal authenticated, hiding and binding commitments, and explicitly
state any additional cryptographic service. Ideal cryptography removes attacks
on the primitive; it does not remove network delay, censorship, metadata,
voluntary disclosure, transaction costs or the need for communication.

The main question is:

> Which operational ledger interfaces admit a compiler that implements every
> sequential-equilibrium outcome of every game in this class?

The compiler, deadlines, fee policy and deposits must be chosen before selecting
the source equilibrium. A mathematical result must state whether it applies
to every service obeying the interface or just one constructed service.

The primary target chooses collateral before selecting the builder, using
only the program and public service properties. The
checked settle-late comparison defeats every fixed forfeit above the reward
scale and every fixed audit charge above half that scale by choosing sufficiently
reliable late inclusion. This settles a uniform-order negative for that
abstract family. Embedding it into the full compiled runtime remains open;
collateral chosen for a fully known service is a pedagogic contrast.
[Collateral and service quantifiers](quantifier-orders.md) gives the exact
statement, model reminder and obligations for the two orders.
[Miner behavior and player knowledge](miner-assumptions.md) distinguishes
pointwise preservation, a common policy and Bayesian uncertainty about the
service, and reviews what standard consensus assumptions actually supply.
[Runtime choices and scope](model-decisions.md) recommends a small research
interface and separates details proved irrelevant, effects quantitatively
bounded, and aspects deliberately excluded. It makes no change to the adopted
model.

A finite deposit is not automatically an affordable deposit. Each result
must state the available capital and whether play begins after funding, or
whether participation and refusal to fund are additional choices. Locked
capital and borrowing costs cannot be removed by naming the funds “escrow”.

Here a sequential equilibrium requires two things. At every decision, including
decisions off the equilibrium path, the player's entire remaining strategy is
optimal given its beliefs. Those beliefs must arise together as a limit of
Bayesian beliefs under strategies giving every legal player action positive
probability. Convenient but incompatible off-path beliefs are insufficient.

## The most useful current proof route

The research separates two proof obligations that can be combined for the
same finite implementation game. First, show that source decisions retain their
menus, conditional logical transitions and utilities, and that the entire
remembered runtime record adds no information within a source information set.
This may include genuine uncharged choices among equivalent implementations,
provided one fixed, fully supported selection rule yields the required
observation channels. Second, handle every remaining physical action through
an actual incentive and consistent-completion argument. The
[compositional criterion](universal-preservation-criterion.md) gives a paper
constructor for the first obligation and states the checked audit-extension
theorem used for the second. Its assembly has not been instantiated for the
full native runtime.

For protected serial commit–reveal play, there is a concrete information
argument: opaque commitments have identical public envelopes across hidden
values, and earlier effective openings are already source-public before the
next logical decision. Coupling the actual packets and environment inputs then
couples timing, receipts and remembered private samples. This permits readable
pending plaintext; it does not require a payload-blind scheduler. The
[native serial analysis](native-observation-criterion.md) proves the restricted
paper result and identifies the missing adapters for extra actions.

[Native protected execution](native-protected-execution.md) gives a reviewed
paper proof on an explicit first-ready restriction of the actual serial
runtime for the intended mandatory-action source. Its adaptive bounded
stopped-prefix coupling retains the real private catalogues and full recall;
it adds no visible scheduler counter. The copied policy works for every
declared timely contract scheduler. Its adaptive adapters remain unformalized,
and deferral, retries and other raw actions are still outside this theorem.
The [foundation map](native-foundation-obligations.md) identifies the checked
APIs and remaining concrete extension obligations.

Accepted late actions require separate analysis. With one late opportunity to
open an immutable value, a complete paper positive permits inclusion chances
approaching one, including certainty; it needs no uniform lower bound on
failure. Its successful posteriors are derived from one common tremble sequence.
The [admission-risk analysis](admission-information-boundary.md) also explains
why multiple timing choices or fresh value choices need different arguments.
Its value-choice counterexample uses a private attempted-value failure payoff
that has not been embedded in the native typed readout.

The [serial late-opening theorem](serial-late-release.md) composes the positive
across an entire finite program with retained secrets. It keeps binding choices
protected, permits one late Send/Never callback per mandatory opening, and
allows an arbitrary rational continuation after a publicly marked failure.
Public success and total-loss bounds give uniform finite forfeits. A separate
theorem removes the success bound when the callback's exact success odds are
known and its classification is recoverable by every later strategic player.
That extra public information is not established by native readiness tokens.
Both are reviewed paper results for explicitly restricted interfaces.

The [many-decision delivery theorem](delivery-control-preservation.md) removes
the one-callback restriction for immutable openings. The owner may send, wait,
retry and privately learn about service conditions. If publication failure
ends play with the same nonpositive owner utility after every route, all
retained private types can share a delivery-maximizing policy. One global
consistency construction supplies its off-path beliefs. Protected initialized
play then implements the exact source law without any late-success floor.
Successful retry charges and mode-dependent failed-packet penalties are outside
this result; the actual settled audit distinguishes accepted packet identifiers.
A separate cost corollary permits bounded operational deductions when one
policy is optimal at both extremes of the source continuation-payoff range,
at every legal delivery site. It requires actual settled, irrevocable bills
and free initialized protected transport, not an average fee estimate.

[Late binding with failure erasure](late-binding-erasure.md) extends the
success-bound result to a late callback that chooses a fresh value. It requires
a common continuation projection preserving every future menu, observation,
transition and utility after an unaccepted attempt; the owner's actual memory
remains intact. Ending payoff-relevant play at the first publication failure
is a simple sufficient protocol variation. General raw native continuations
retain opening evidence for unaccepted candidates, so terminal readout alone
does not establish the required erasure.

Physical outages call for a different output claim. The
[exogenous-abort theorem](exogenous-abort-preservation.md) preserves exact SE
when the service process is source-independent and abort utility is unaffected
by source choices. The complete source law is then exact conditional on
delivery; the unconditional readout includes its actual abort mass. Conditional
checkpoint guarantees bound whole-game failure by a product or a union bound,
without independent checkpoints. These stronger exogeneity and payoff
conditions are separate from merely having a high completion probability.

[Controlled whole-game delivery](whole-game-delivery-preservation.md) adds
finite Send/Wait/Retry choices and removes guaranteed protected inclusion.
Its stronger interface makes the entire mechanical service independent of
logical data and transports every source action through the same process.
Every physical abort gives each player the same utility no greater than any
source outcome. A globally completion-maximizing transport policy then
supports exact SE, the exact delivered source law, and at least any declared
fallback's whole-game completion guarantee. This permits realistic kinds of
delivery risk without claiming that ordinary blockchain service or the
current audit satisfies these conditions. Lawful source withholding remains
distinct from a physical abort.

For persistent serial jobs with exogenous opportunities and monotone
eligibility, always submitting at the first eligible callback works across
the whole stated service class without knowing its inclusion law. The same
note proves that corollary and gives a two-stage counterexample to charging
only the player whose stage fails. A player may deliberately shift failure
to another stage; making every abort payoff low does not by itself align its
delivery choices.

Two source classes must remain separate:

- **Withholding is a lawful choice.** Failure and its payoffs belong to the
  source game. A compiler cannot silently add a fine that changes this choice.
- **Opening is required by the intended game.** An implementation may introduce
  withholding with a specified intrinsic forfeit. This changes the expanded
  game and needs its own preservation argument.

## What preservation means

The principal exact target is forward implementation: for every selected
source equilibrium, there exists a target equilibrium with the same joint law
of initial private parameters and declared logical results. Matching net
payoffs and avoiding extra charges are additional obligations, stated explicitly.
This allows the target to have other equilibria. It does not require copying
every off-path belief of the selected source assessment.

This distinction changes which analyses a programmer may trust. Forward
implementation supports a selected source equilibrium. A property proved
about **all** source equilibria needs an appropriate reflection theorem or
a separate proof of that property in the target; forward implementation alone
does not exclude additional runtime equilibria.

These stronger or weaker questions have different conclusions:

| Target | Required conclusion |
| --- | --- |
| Copy a selected assessment | Its strategies and beliefs are recovered at corresponding decisions, including off-path ones. |
| Reflect all target equilibria | Every target equilibrium produces an outcome permitted by a source equilibrium. |
| Exact rationality with physical abort | The target assessment is an exact SE; the source law matches conditional on completion, and the unconditional law includes explicitly bounded abort mass. |
| Approximate sequential preservation | There is a target assessment with exactly consistent beliefs, uniformly small gains from changing an entire continuation, and a nearby logical outcome law. |

Logical-law error is measured in total variation: the largest probability
difference for an observable event. Payoff error is measured separately,
for example by expected absolute difference under an explicit coupling.
A tiny deterministic fee can move every realized payoff and make payoff-law
total variation equal to one. Small monetary errors are not automatically
small errors in that metric.

## Reading route and parallel tracks

| Track | Question | Document |
| --- | --- | --- |
| Information and release | What may be learned before a dependent decision? How do plaintext, encrypted admission and owner-held secrets differ? | [Information and release](information-and-release.md) |
| Service and enforcement | Which delivery, finality, attribution, collateral and cost guarantees suffice? What survives after a charge is sunk? | [Service and enforcement](service-and-enforcement.md) |
| Preservation and robustness | Which quantifiers and error measures are useful? What does noise preserve, and which exact claims fail? | [Preservation and robustness](preservation-and-robustness.md) |
| Integration | Which candidates have proofs, which are contrasts, and what assumptions distinguish them? | [Interface and result catalog](catalog.md) |
| Collateral and service | What fails when collateral is fixed before the builder, and what can hold when it is chosen for a known service? | [Quantifier orders](quantifier-orders.md) |
| Miner behavior and knowledge | Which service properties are public, what can independent miners choose, and do players know the scheduler law? | [Miner assumptions](miner-assumptions.md) |
| Model choices | Which details can be omitted without losing the intended conclusion, and which omissions limit its scope? | [Runtime choices and scope](model-decisions.md) |
| Observation abstraction | When can the full remembered private or public runtime view be retained physically but ignored by a preserving policy? | [Observation abstraction](observation-abstraction.md) |
| Honest producer candidates | What follows from sufficient capacity or simple fee maximization, without modeling a miner economy? | [Two producer models](honest-producer-models.md) |
| Costs and scope | Which utility changes cancel, which yield approximate rationality, and what do participation and capital assumptions exclude? | [Costs and omissions](costs-and-scope.md) |
| Auditable fee policy | Can we enforce a public bidding rule without fixing the numerical payment, and which priority and signaling effects remain? | [Fee policies](fee-policy.md) |
| Compositional preservation | Which full observation, logical-execution and extra-action obligations combine into an SE theorem? | [Compositional criterion](universal-preservation-criterion.md) |
| Native protected play | How do actual opaque envelopes and source-public openings couple serial runtime observations? | [Native serial analysis](native-observation-criterion.md) |
| Actual first-ready execution | Does the intended mandatory-action source preserve SE with adaptive native waits and full private recall? | [Reviewed protected proof](native-protected-execution.md) |
| Concrete proof obligations | Which checked APIs apply, which adaptive adapters remain unformalized, and what prevents a full raw-menu conclusion? | [Foundation map](native-foundation-obligations.md) |
| Accepted late actions | When does a late opening's gain scale with failure risk, and when can rare failures change successful posteriors? | [Admission risk and information](admission-information-boundary.md) |
| Multi-phase late openings | Can accepted late fixed-value openings compose across a whole program while old secrets persist? | [Serial late-opening theorems](serial-late-release.md) |
| Several delivery decisions | Can waits, retransmissions and private service learning share a type-independent rational completion? | [Immutable openings with delivery control](delivery-control-preservation.md) |
| Late value choices | When can an unaccepted private binding value be ignored without changing later strategic possibilities? | [Failure erasure and absorbing settlement](late-binding-erasure.md) |
| Physical outages | Can rationality remain exact while the outcome claim explicitly allows noncompletion? | [Exogenous abort and delivery-conditioned preservation](exogenous-abort-preservation.md) |
| Controlled whole-game delivery | Can send, wait and retry remain rational without surely successful admission, with a whole-game reliability guarantee? | [Value-blind service and completion](whole-game-delivery-preservation.md) |

[The research workflow](workflow.md) specifies independent tasks, handoffs,
review obligations and the next mathematical questions.
[The native research agenda](native-research-agenda.md) directs the remaining
mathematical effort to actual late actions, independent concrete review and
protected-proof integration. Existing foundations suffice for the reviewed
protected restriction; new foundations require a concrete missing bridge.
The agenda fixes the intended-source scope and keeps alternative runtime
proposals separate.
[The annotated literature](literature.md) records relevant primary sources
without treating them as proofs about this project's ledger.

## What “minimal” can reasonably mean

An interface specifies permissible physical behavior, observations, actions,
faults and costs. One interface is weaker than another when it allows every
behavior of the stronger one and possibly more, under a common comparison
model. A preservation theorem for the weaker interface is correspondingly
stronger. Interfaces with different trust, communication or resource mechanisms
may instead be incomparable.

We therefore seek useful sufficient interfaces and their boundaries. For a
declared family of assumptions, an irredundant sufficient set is one for which
each removed assumption admits a specified counterexample. This does not show
that every possible weakening fails, that the same assumption is necessary for
every individual game, or that one implementation mechanism is uniquely minimal.

A rejected packet is a particularly important example. Contract rejection can
prevent a state update. It cannot undo knowledge obtained from the packet.
An information-preservation claim must cover that knowledge or justify why the
additional transmission cannot profitably change the relevant equilibrium.

## Relationship to existing project results

The existing calendar compiler theorem is a checked exact reference case.
It combines a particular scheduling interface, source-information analysis and
audit enforcement. It is not an assertion that a fixed calendar is necessary.

The ordinary asynchronous service model gives owner opportunities, protected
sole-packet receipts and eventual event completion within its configured
execution. It also permits uncertain late admission and additional submissions.
Those execution properties alone are not a general SE-preservation theorem.

The existing [public stochastic scheduling paper](../public-scheduling-se-preservation.md)
is a broader exact mathematical reference: nonstrategic public waiting can
depend on the source-public past, while players keep their original menus and
payoffs. Its primitive construction supplies the information and continuation
arguments. Actual packet submission, private aliases and fee bidding need
separate treatment.

The [single disclosure-phase proof](../full-public-disclosure-phase-preservation.md)
and [public-reset composition](../public-reset-phase-se-preservation.md) are
restricted positive paper results. Neither assumes that hidden values simply
become public when their owner withholds them.

The checked [finite-horizon service obstruction](../probabilistic-runtime-preservation.md)
shows that positive unavoidable noncompletion probability prevents exact
terminal-law matching. It weakens sure service; it is not an impossibility
under the unchanged asynchronous contract.

The [vanishing-noise paper](../noisy-runtime-approximate-se-preservation.md)
supplies a consistent approximate-SE target under a fixed finite information
structure and uniformly small primitive chance errors. Its concrete ledger
adapter remains a separate obligation.

These are reference results with their own interfaces, rather than assumptions
silently inherited by every new candidate.
