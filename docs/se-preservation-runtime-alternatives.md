# SE preservation with an abstract source language

Analysis by Codex. This document evaluates possible runtime contracts. It does
not adopt a new target, change the baseline semantics, or close an obligation in
the [preservation checklist](se-async-checklist.md). Proposed positive results
below still require proofs.

An abstract game language remains a reasonable objective. The late-leak
counterexample forces a choice about control of disclosure and the information
created by execution. My preferred direction is a backend that accepts
recoverable commitments and takes responsibility for their subsequent release.
The checked calendar service is the closest existing reference implementation
at the mathematical level.

Boneh and Naor's timed commitments are one possible ingredient. The useful
property is **recovery without further cooperation by the owner**. They are
neither necessary for that property nor sufficient to make disclosure an atomic
public event. A theorem assuming owner-independent disclosure can be a useful
ideal-service theorem, but removing a reveal message from a model does not by
itself establish SE preservation or a faithful implementation.

**The impossibility concerns a specific strategic combination.** The
[mechanized result](../Vegas/Examples/LateLeak/Preservation.lean), pinned in
[Paper](../Paper.lean), exhibits an intended game with sequential equilibria
whose intended outcome law no sequential equilibrium of the late-turn game
reproduces. The concrete example uses payoff range 2, forfeit 6, drop charge 3,
and late-inclusion probability 99/100. Its consistency argument allows arbitrary
type-dependent and turn-dependent trembles. This rules out all preserving
assessments for that game, not merely one attempted proof construction. See the
[mathematical account](open-problem-late-turn-equilibria.md) for the argument
and its extension across penalty margins. The separate
[checked native obstruction](commit-reveal-research/native-se-obstruction.md)
controls an actual compiled three-instruction program and its full bounded raw
menu. For fixed $R>0$, $D>R$, $K_A>R$, $K_B>1$, full authentic audit and fair
partial pending samples, one finite admissible builder has arbitrarily small
positive canonical omission but no SE with the source's joint terminal-store
and realized-payoff law. Native SE exist. This does not establish an
impossibility for the public-result marginal alone, every blockchain or a
different compiler. Sharper collateral and broader audit/sampling variants
remain paper results.

Pending openings can disclose their contents even when never included. That
changes the continuation following failure and induces different private types
to prefer different sending times. Consistency then makes some late-success
observation informative, forcing a listener response that rewards delay. With
late acceptance sufficiently likely, that reward outweighs the expected
failure-related penalty. A content-blind builder does not remove this effect.

This explains the limitation of increasing collateral: if a cost is incurred
only when a late opening fails, its expected contribution vanishes as the
success probability approaches one. It does not establish that every fixed
builder defeats every possible enforcement rule or deposit calibrated to that
builder.

**The alternatives change different parts of the contract.** None requires
putting packets, retries or block construction into every game program.

| Approach | What the source can retain | What the backend must provide | Proof status here |
| --- | --- | --- | --- |
| Ordered service with logical rounds | Private choices, bindings, reveals and dependencies | A specified admission and inclusion schedule, with actual observations and enforcement | SE preservation is checked for the fixed calendar; physical realization is separate |
| Recoverable commitments with service-driven release | An intended reveal that always opens | Validated recovery material, confidentiality, release and delivery guarantees | Proposed general direction |
| Penalties that survive successful late delivery | Intended timing can remain implicit | Attributable departures and an additional collectible cost sufficient to dominate their gain | Generic enforcement machinery exists; a suitable runtime instance is needed |
| Certified source fragment | Abstract games meeting a robustness condition | A runtime proof for that condition | Candidate restrictions need proofs |
| Asynchronous publication primitive | High-level disclosure and effect events | An implementation of the stated information and delivery semantics | Changes the source game whose SE is preserved |

For an ordered backend, a server or replicated application service could
implement the interaction protocol while a blockchain handles settlement. The
[calendar theorem](../Vegas/Game/SourceServiceCompilation.lean) already permits
partial pending observations; its strong restriction is the service schedule.
Calling a deployment round-based does not establish its hypotheses, and
concurrent execution needs an additional proof.

A bare acceptance deadline is insufficient. Between the last guaranteed
submission opportunity and the deadline, a player may still submit with a high
probability of success. Rejecting transactions after the deadline leaves that
interval intact. Nor does a sender-supplied timestamp establish when a message
was actually transmitted.

For economic enforcement, the relevant condition is that the minimum
additional expected collectible penalty for the first strategic departure
exceeds its maximum possible continuation gain. This comparison must hold
conditionally at the relevant information sets, under arbitrary subsequent
play. A cost already sunk cannot deter a later decision. Publicly certified
obligations or an accountable receipt service might supply evidence; block
inclusion time alone does not distinguish withholding from delivery delay. The
[terminal-audit machinery](../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean)
and [restriction extension](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean)
are reusable consumers of such evidence, not implementations of collection.

A narrower source fragment could require that all payoff-relevant choices be
irrevocably fixed before disclosure, or that specified continuation choices
remain optimal under the additional signals. Those are candidate proof routes.
Alternatively, a publication primitive could distinguish information becoming
observable from an action becoming effective. That is still a semantic
abstraction, but its equilibria belong to a different game from one with
instantaneous public disclosure.

**Timed commitments address the owner's ability to withhold.** Boneh and
Naor's construction adds a forced-opening procedure: a receiver can recover a
committed value through computation without the sender's participation. The
original definition includes assurance of recovery after a successful commit,
an opening proof verifiable by others, and resistance to accelerating recovery
through parallelism. It also retains ordinary cooperative opening. The paper's
applications explicitly use timing assumptions. Thus it supplies a way to
recover a secret, rather than a claim that all observers learn it at one
physical instant. [Boneh and Naor, *Timed Commitments*, CRYPTO 2000](https://www.iacr.org/archive/crypto2000/18800237/18800237.pdf)

For VegasCore, three properties should be distinguished:

| Property | Meaning | Consequence |
| --- | --- | --- |
| Owner-independent recovery | Accepted recovery material suffices without another owner action | Withholding an opening need not prevent eventual recovery |
| Guaranteed publication | Some specified mechanism completes recovery and delivers an accepted result | Recovery is a service guarantee, not merely a possible computation |
| Adequate information discipline | The actual release process supports the source information structure at strategic decisions | Additional signaling and early knowledge are accounted for in the SE proof |

My assessment is that a useful reveal abstraction needs all three, with the
last property derived from operational rules. Eventual recoverability alone
does not supply the latter two.

Several obligations remain even with a secure timed commitment:

1. **The owner already knows the value.** It may reveal early, tell a selected
   recipient, or publish recovery assistance. Disabling the contract's reveal
   entrypoint does not remove those capabilities. If they are possible in the
   modeled runtime, they must be represented, deterred or proved harmless.
   An optimistic owner-opening path also retains a timing choice; adding a
   slow fallback does not erase that choice.
2. **Recovery must actually happen.** A solver needs resources and a reason to
   run. If the solver can profit from withholding its result, it introduces a
   strategic action. A trusted service assumption or an incentive proof must
   account for this. Permission to recover is not a liveness guarantee.
3. **Recovery time and source readiness differ.** A puzzle available at
   commitment can be attacked from then onward. If the game's disclosure event
   depends on an unpredictably delayed branch, a fixed computational delay may
   expire too early or impose a long extra wait. Starting a new puzzle at
   readiness requires explaining who supplies the necessary material without
   restoring the owner's veto.
4. **Knowledge and ledger state can diverge.** One observer may recover or
   receive a value before another. A solver's submission can be pending before
   a contract records it. Preventing dependent ledger actions during this gap
   can help, but does not delete observations or later conditioning on them.
5. **An accepted commitment must recover the right object.** The backend needs
   evidence connecting the recovery material to the binding, payload type and
   relevant validity requirements. Recovery of arbitrary bytes is insufficient
   for the intended game's valid-value guarantee.
6. **Costs belong somewhere.** Recovery work, fees, delay and service failures
   can affect incentives. Exact preservation of realized net payoffs requires
   accounting for them or explicitly choosing an ideal cost model.

These are analysis of the compiler interface, not claims that the cited
cryptographic primitive promises to solve them. They also identify why a
generic VDF is insufficient: a verifiable delayed computation still needs a
construction connecting its result to the chosen secret and a release service
around that construction.

**Practicality should be assessed by the required service.** Timed commitments
are not confined to the original construction. Ambrona, Beunardeau and Toledo
give newer constructions aimed at practical use, but their revised definition
allows forced opening to return an invalid marker instead of guaranteeing in
advance that it recovers a message. They also distinguish sequential work from
wall-clock time: faster hardware can accelerate the former. These details
matter for selecting a backend primitive. Their construction is not by itself
an implementation of an intended typed reveal. [*Timed Commitments Revisited*](https://eprint.iacr.org/2023/977.pdf)

There is implementation evidence: Octez documents a timelock library, commands
for creating and opening encrypted chests, and an instruction for checking a
supplied opening. This demonstrates concrete tooling, while also illustrating
that verification consumes an opening supplied to the runtime. It does not
establish suitable cost or timing bounds for VegasCore on the EVM. [Octez
timelock documentation](https://octez.tezos.com/docs/alpha/timelock.html)

A different engineering option is threshold release. Drand's tlock encrypts
for a future beacon round and permits decryption using that round's published
signature. Its documented assumptions include a bound on malicious threshold
participants and continued network operation. This avoids making each
recipient perform a long puzzle computation, but relies on a committee and
delivery of its output. Tlock is an encryption building block; commitment
validity, conditional game events and ledger integration remain our work.
[Drand timelock documentation](https://docs.drand.love/docs/timelock-encryption/)

I would therefore avoid either a blanket practicality claim or a blanket
dismissal. A small number of long-lived releases is a different workload from
a game with many short, dependent rounds. The latter needs measured generation,
validation, recovery and on-chain verification costs, a timing budget, and a
failure model. A committee can offer a more direct release service if its trust
assumptions are acceptable. A trusted server offers another implementation of
the same abstract interface.

**The theorem should describe an autonomous reveal event precisely.** In the
ideal service, acceptance of a binding stores a recoverable value. Once the
declared source dependencies complete, a service transition publishes that
value. The owner has no open/wait choice at this transition. Physical messages
may implement the transition; their authors, visibility and delivery cannot be
silently omitted from the concrete refinement.

This abstraction assigns responsibility for producing the result to the
service. It is appropriate to the
[intended game](se-two-sources.md), where reveals always open. A source game
that intentionally offers withholding needs its own treatment: removing that
option changes its strategic meaning.

A candidate preservation claim would fix the program, initial law, utilities,
release service, observation mechanism and enforcement before selecting an
intended source SE, and then construct a native SE with the required joint law.
This is a research target. Owner-independent revelation removes the exhibited
late-opening mechanism but does not prove that every other deviation is safe.

The proof should separate four tasks:

1. Specify and implement acceptance, validated recovery, release triggers,
   observations, scheduling and collection. Give service guarantees for all
   admitted raw histories, including malformed traffic and silence.
2. Prove honest execution and settlement correspondence, including source
   private information and recall.
3. Construct one consistent native assessment from actual reach weights.
   Account for metadata and observations during release; a hypothesis asserting
   the desired posterior correspondence is not an implementation contract.
4. Prove whole-continuation rationality at every native information set,
   including failed admissions, optional early disclosures and sunk penalties.

A logical public event need not mean physically simultaneous reception if a
refinement proves that reception skew creates no unaccounted strategic
advantage. That is a proof obligation about the full protocol. Likewise,
eventual delivery does not imply completion within the bounded runtime's
horizon. Partial synchrony provides bounded delays only under its specified
stabilization assumptions. [Dwork, Lynch and Stockmeyer, *Consensus in the
Presence of Partial Synchrony*](https://groups.csail.mit.edu/tds/papers/Lynch/jacm88.pdf)

**Exact ideal SE and computational implementation are different claims.**
An ideal authenticated release service can support an ordinary SE theorem.
For concrete cryptography, players' computational limits and negligible errors
require an appropriate computational formulation. Halpern, Pass and Seeman
prove an SE transfer theorem under an explicit representation relation for
computational extensive-form games. That relation includes matching history
lengths, so it is not a direct adapter for a multi-step Vegas runtime.
[*Computational Extensive-Form Games*, Theorem 4.6](https://arxiv.org/html/1506.03030)

Mediated implementation also has genuine SE results. Geffner and Halpern
establish implementation results for Bayesian communication games under
specified participant thresholds and scheduling assumptions. Their scope and
communication model differ from arbitrary interactive Vegas programs. This
supports investigating a mediator interface without treating general secure
computation as an automatic SE preservation theorem. [*Communication games,
sequential equilibrium, and mediators*](https://arxiv.org/html/2309.14618)

My recommendation is to keep the intended source language abstract, retain the
calendar result as the checked reference, and investigate a validated
recoverable-binding and autonomous-release interface. The first test should
retain observable traffic and raw deviations in a small concrete implementation
and prove that it supports the intended outcome of the late-leak game. A
general compilation theorem must then address arbitrary source programs and
equilibria. Timed commitments give this investigation a cryptographic basis;
they do not justify assuming away either communication or its strategic effects.
