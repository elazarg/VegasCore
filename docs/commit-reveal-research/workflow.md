# Mathematical research workflow

The deliverable is a collection of useful conditional results about ledger
interfaces, organized so that a reader can reconstruct each model from its
statement. It is not a replacement specification for the compiler.

## Required result card

Every proposed result must supply these fields, in ordinary language before
any technical notation:

1. **Source game.** Which commitments, private inputs, legal withholding choices,
   intermediate decisions and payoff functions are present?
2. **Physical interface.** Who submits, orders, receives, decrypts and publishes?
   What may players retry, alter, query, broadcast or bid for?
3. **Observations.** Who learns payloads, identities, lengths, fees, timing,
   omissions, receipts and finality, and before which decisions?
4. **Fault and service assumptions.** Which parties may be corrupt or unavailable?
   Are bounds deterministic, conditional probabilistic, or eventually valid?
5. **Costs and accountability.** What is attributable, who collects a penalty,
   how much additional collectible collateral remains, and which utilities count?
   Is the required capital feasible, and is funding a prior condition or a
   strategic choice?
6. **Quantifiers and output.** What is fixed before the equilibrium is selected?
   Is the claim exact, approximate, forward implementation or reflection?
7. **Proof status and boundary.** Give a proof or counterexample, its independent
   review status, the missing adapters, and the precise relationship to the
   existing runtime.
8. **Deliberate omissions.** State which aspects are proved irrelevant, bounded
   as an approximation, or excluded from the game. Identify the consequences
   for participation, fees and capital, producer incentives, coalitions,
   external channels, computation, and resource/finality assumptions as relevant.
   Put material exclusions beside the theorem statement, not solely in a
   distant model description.

The same vocabulary must accompany a result even if its interface appeared
earlier. Avoid relying on internal declaration names or unexplained labels
for the assumptions that determine the result.

## Evidence categories

| Category | Meaning |
| --- | --- |
| Existing checked theorem | A named machine-checked statement with its actual scope and assumptions. |
| Paper theorem | A complete written mathematical argument; no machine-checking claim. |
| Counterexample | A specified source and target game, a selected source equilibrium, and proof that no target equilibrium preserves the declared object. |
| Local lemma | A useful conditional comparison or probability fact that does not by itself prove equilibrium existence or preservation. |
| Candidate interface | Specified mechanics proposed for study; a preservation theorem is not yet established. |
| Conjecture or open question | An explicit statement whose proof is missing. |

Computational experiments may find candidates, but are not substitutes for
proofs of an all-equilibria claim. A bad compiled comparator is not a
counterexample to existential outcome implementation. A profitable action after
a deterred departure is not automatically a counterexample at initialized play.

## Independent work packages

The information track can analyze disclosure channels and exact scheduling
expansions without fixing an audit scheme. Its handoff specifies what faithful
execution exposes, and which extra transmissions still need enforcement.

The service track can prove bounds on timely delivery and first departures
without selecting equilibrium beliefs. Its handoff states primitive collection
probabilities, payoff bounds, source-equivalent alternatives and fault scope.
It must distinguish a retained decision with uncharged collateral from a later
decision after an unavoidable charge.

The robustness track can prove preservation limits and error bounds for a
fully specified finite game without selecting a ledger implementation.
Its handoff states the required common actions, observations, chance supports
and payoff metrics. Uniformity must include legal deviations and relevant
off-path histories, not merely honest initialized execution.

Integration combines these handoffs only when they concern the same game:
same admissible actions, observations, phase boundaries, fault model and utility
accounting. It must identify every adapter still missing. Multiplying together
informal claims from incompatible interfaces is not a preservation proof.

## Review and minimality tests

Before promoting a result to the catalog, another mathematical reviewer checks
its quantifier order, complete deviation space, conditioning at rare decisions,
and consistency of off-path beliefs. Small counterexamples should be simple
enough to verify directly from their trees and payoff tables.

For each sufficient interface, attempt the following distinct weakenings:

- admit a payload or timing signal before a source-dependent choice;
- allow permanent or finite-horizon publication failure;
- allow a player's timing choice to alter another player's admission chances;
- replace fresh attributable penalties by a capped, already charged escrow;
- introduce fees, delayed-payoff preferences or private inclusion information;
- replace public phase resets by retained correlated private state;
- allow retries, replacements and alternative encodings;
- weaken source-history-wide guarantees to guarantees only on prescribed play.

Failure of one weakened interface establishes a boundary in that comparison
family. It does not invalidate every interface sharing the weaker feature.
If a weakening survives, record the broader candidate and the new proof task.

## Next mathematical questions

1. Which physically stated encrypted-admission or plaintext-window mechanics
   realize the existing public scheduling construction, including observations?
2. Can exact source-information transfer survive source-private auxiliary
   receipts and retries without requiring their removal from the interface?
3. Which first-departure enforcement mechanisms have bounds independent of the
   selected equilibrium and of arbitrary later strategies?
4. Can independent deposit tranches or refundable per-event collateral provide
   credible enforcement with a reasonable finite capital requirement?
5. Can a general consistent approximate-SE theorem be derived from operational
   delivery and information guarantees rather than a pre-supplied common game
   tree? What happens at newly reachable decision points?
6. Which exact results survive fees under strict incentive margins, and which
   source equilibria disappear at indifferences?
7. How far can several disclosure phases be composed while retaining old secrets?
8. Which guarantee follows from a specified consensus and communication model,
   and which requires a separate inclusion, decryption or keeper assumption?
9. If higher reliability requires larger collateral, do the resulting cost and
   regret errors still vanish? The fixed-bounded-payoff noise theorem cannot
   simply be reused with deposits growing without bound.
10. Under which public collection/gain bounds does collateral chosen before
    the selected builder preserve SE? Treat exact-builder calculations as
    contrasts. In parallel, test a native embedding of the checked settle-late
    negative comparison. Added native actions can change equilibrium existence;
    an abstract embedding alone does not preserve a negative conclusion.
11. State a public miner/service class and distinguish pointwise preservation
    from a common policy and Bayesian hidden-service preservation. Test whether
    the negative comparison survives unknown inclusion rates and whether a
    standard honest-miner transaction-selection model realizes its mechanics.
    Constants depend only on public properties and precede the selected builder;
    exact-builder calculations are contrasts rather than deployment targets.
12. Derive the actual retained runtime's full remembered observation channel
    from its primitive kernels. Test the replay-channel criterion in
    [observation abstraction](observation-abstraction.md), including correlated
    private leak samples, receipts and timing while old secrets persist.
13. Test the [simple producer candidates](honest-producer-models.md) against
    native menus, sender identifiers, observable arrival times and settlement
    evidence. Keep their service lemmas separate from a full SE adapter; an
    enforced physical emission cutoff is not supplied by a logical horizon.
14. Combine the successful information/action interface with the
    [bounded-cost comparison](costs-and-scope.md). State whether the output is
    exact SE under canceling utility costs, approximate sequential rationality,
    or exact strict-margin preservation. Do not erase fee-dependent information
    or opportunities as a terminal payoff perturbation.
15. Establish which [public fee rules](fee-policy.md) can be audited and
    collected upon, including successful high-priority departures. A canonical
    bid can depend on public state while the actual payment varies. Account for
    permitted fee signaling and priority actions; do not infer a fixed-fee action
    space from fee auditability or lift the producer negative by merely adding
    a bidding menu.

16. Instantiate the [compositional constructor](universal-preservation-criterion.md)
    on a single fully specified native restriction. Classify every raw action
    as a source action, a proved harmless implementation choice, or an action
    with a separate incentive proof. Check audit soundness on every retained
    history, including failed late sends; accepted-call correctness alone does
    not supply the extension premises.
17. Extend the [protected serial observation argument](native-observation-criterion.md)
    to barrier-ordered concurrent opaque bindings. Prove own decision recall
    and information about whether another binding has happened, alongside
    completion commutation. Guard-rejected TRUE and FALSE choices require the
    private-intention normalization or an explicit private-memory adapter.
18. Test the native adapters for the [multi-phase late-opening theorems](serial-late-release.md).
    Their paper proofs derive successful prefix likelihoods and global
    consistency while old secrets persist. Determine whether multiple physical
    callbacks can be normalized to one, which actual failure observations
    separate continuation regions, and which total-loss caps hold. Exact public
    callback odds are an alternative sufficient interface, not information
    supplied by a bare readiness token. Keep protected binding choices distinct
    from late callbacks that select fresh values, and state which utility
    readout the negative examples use.

19. Test the [failed-binding continuation erasure](late-binding-erasure.md)
    against native recovery menus and transferable candidate evidence. The
    paper theorem retains actual private recall through an ancillary-record
    lift; terminal payoff independence is insufficient. Compare the absorbing
    first-failure settlement variation with sources that genuinely need
    recovery, and identify which raw actions still require deterrence before
    failure. Do not treat the missing erasure adapter as a native impossibility.

20. Test the [delivery-conditioned exact-SE theorem](exogenous-abort-preservation.md)
    against a genuine exogenous outage model and actual settlement. Its stage
    bounds aggregate without independence, but admission must not reweight
    source actions or later public source coins. Immutable initial wealth may
    affect abort utility; action-dependent paid fees and changing balances
    cannot be hidden in that extension. State the weaker outcome target and
    every additional physical action excluded from the adapter.

These tasks are mathematical and parallelizable. Formalization, deployment
claims and changes to project semantics require separate work.
