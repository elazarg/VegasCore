# Assumptions for sequential-equilibrium implementation

## Recommendation and claim boundary

The smallest defensible general route is to retain ambient communication in
the source **interpretation**, with one explicit service contract, and prove
the existing compiler preserves that game's sequential equilibria. Keep the
language's game operations unchanged. Hide packet encodings and bookkeeping
only after proving they add no observations or continuation choices.

For an ordinary source game that omits communication, use an additional,
utility-dependent extension theorem for a supported game class. Monitoring
can support that theorem when every profitable extra channel is accountable;
packet-shape checking alone does not establish this premise. This is a route
recommendation, not a completed native SE theorem.

Distinguish a fixed playerwise compiler preserving every source SE from
`for every source SE, some target SE has the same initialized result law`.
A general off-path completion can depend on the opponents' source profile and
therefore establish only the second statement. Neither statement asserts that
all target equilibria reflect to source equilibria.

## What the proposed service can honestly assume

Labels: **ledger** = implementable application checks conditional on inclusion
and the chosen finality abstraction; **model** = explicit restriction of the
modeled environment; **incentive** = utility/belief hypothesis needing proof;
**setup** = additional communication or cryptographic service.

| Candidate assumption | Classification and exact limit |
| --- | --- |
| Bounded public packets and interaction count | **Model.** A finite alphabet, finite activation budget and bounded candidate supply make finite SE analysis possible. A game deadline or gas limit does not bound all pending packets or all communication before it. Enforcing admission counters bounds accepted game moves, not messages an opponent might read. |
| Binding when submitted | **Cryptographic/ideal premise.** A posted commitment must not acquire its meaning later. Binding does not imply that its author knows an opening, cannot share it, or retains exclusive signing-key control. The current ownership-based capabilities need a possession-based cryptographic refinement. |
| Partial pending observation plus public ledger | **Model with a realistic mechanism.** Ordinary nodes may see pending traffic; included transaction data is public. Using the same observation rule does not give a watchdog another player's sample. The rule, activation opportunities and correlation with later inclusion must be specified. |
| Positive probability of a timely report | **Setup/incentive.** Requires observation, retained evidence, reporting and timely inclusion, conditional on what the deviator knows. Public gossip supplies no universal quantitative lower bound. Private submission paths exist. |
| Inclusion oblivious to identity or new messages | **Service/incentive assumption.** Ethereum permits economically consequential inclusion, exclusion and ordering. Non-collusion alone does not imply a particular selection kernel. Prefer contract-checkable event authorization for ledger effects where that suffices; it does not suppress pending observations. |
| Canonical public encodings eliminate signaling | **Unproved unless concretely enforced.** Canonical parsing removes some aliases. Legal values, cryptographic coins, identifiers, timing, silence and correlations may still signal. A traffic normalizer acting before reception is a stronger **setup** than a watchdog fining afterward. |
| Signed evidence identifies the liable player | **Ledger plus liability policy.** A signature identifies an account under its key; shared keys separate account authorship from strategic control. An opening proves a candidate/value relation, not original transmission time or latest rebroadcaster. Define sending or custody liability explicitly. |
| Escrow guarantees a sanction | **Ledger**, after a valid report is included and adjudicated. The deposit must remain locked, correctly denominated in utility, and collectible at the relevant continuation. A prior forfeiture is sunk; future deterrence needs remaining collateral. |
| Interested players will enforce | **Incentive.** Compare reporting with concealment including fees, information advantages, retaliation, self-report rebates and side contracts. Being interested in winning does not automatically make reporting optimal. |

Ethereum's documentation gives signatures, nonces, arbitrary transaction data,
gas, pending pools and block inclusion; it does not certify the proposed
monitoring service. Its MEV documentation expressly discusses strategic
ordering and private submission. These are reasons to expose the assumptions,
not claims that a specific watchdog design is infeasible.
[Transactions](https://ethereum.org/developers/docs/transactions/),
[MEV](https://ethereum.org/developers/docs/mev/).
The cryptographic capability distinction is audited in
[ideal-commitment-capabilities.md](../ideal-commitment-capabilities.md).

## Minimal monitoring obligations

The following are proof obligations for a chosen backend, not an assertion
that all blockchains satisfy them:

1. **Sound admission:** every legal source deviation retains an unpenalized
   implementation. Enforce protocol conformance, not one selected strategy.
   If lawful observable support is `A`, a zero-false-positive monitor can
   detect only observations outside `A`. Changed probabilities within `A`
   remain a blind spot even when statistically distinguishable.
2. **Accountable profitable deviations:** identify a first extra behavior and
   a source-compatible replacement. Bound its conditional game-utility gain;
   establish why retained evidence proves a breach by the charged account.
   Do not replace this argument by assuming that every rejected call leaks.
3. **Conditional collection:** at each relevant information set `I`, for each
   deviation, prove a lower bound on its *additional future expected net
   charge*. A sufficient comparison is `gain(I,deviation) <= charge(I,deviation)`.
   Factoring charge as `p(I,deviation) * D(I)` requires an actual collection law.
   Positive ex ante sampling, or positivity separately for infinitely many
   deviations, does not provide a uniform finite deposit.
4. **Credible continuation:** receivers act optimally after learning evidence;
   reporters act optimally after observing violations. Use one common
   fully mixed approximation for all beliefs. Collection probabilities must
   be justified under those beliefs, including after unexpected prior acts.
5. **Observation accounting:** reports and fines can themselves reveal secrets
   or correlate later decisions. Replacing them by an expected utility charge
   requires a continuation-law argument. A charge parameter is not an
   implementation of the monitor that would collect it.

These obligations have checked pieces: observable-support deterrence,
fixed-snapshot sampling/report bounds, and SE extension for finite
sender/receiver decision games. The latter has one disclosure opportunity,
arbitrary payoffs, and explicitly completed receiver behavior; it does not
solve repeated off-path disclosure after collateral has already been lost.
See [ObservableEnforcement](../../GameTheoryExtensions/Analysis/ObservableEnforcement.lean),
[MessageMonitoringProbability](../../Interaction/MessageMonitoringProbability.lean),
and [DisclosureEnforcementEquilibrium](../../GameTheoryExtensions/Analysis/Protocol/DisclosureEnforcementEquilibrium.lean).

The native certificate-shape checker permits ordinary matching opening
certificates and detects the checked selective-association packet. It also
permits premature matching openings. The shared-pad experiment shows why even
complete public packet observation need not expose signaling inside lawful
formats. These are concrete missing cases for a complete protocol checker;
neither relies on an assumed external private channel.
[ReactiveConformance](../../Vegas/Pending/ReactiveConformance.lean),
[MonitoredSignaling](../../GameTheoryExtensionsTests/MonitoredSignaling.lean).

## Comparing routes

| Route | What it can buy | Main cost or limitation |
| --- | --- | --- |
| Same ambient communication in source and runtime | General strategic abstraction without promising secrecy that players can voluntarily defeat; language syntax can remain game-oriented. | Prove a concrete observation/action correspondence, including timing and evidence possession. A channel contract is still part of the semantics. |
| Watchdogs plus escrow | Ordinary-source SE extensions for games whose profitable extra behavior is detectably nonconforming and whose stakes are bounded. | Conditional reporting incentives and admission completeness; fines do not erase received information or necessarily eliminate additional equilibria. |
| Mediator, reverse firewall or threshold service | Prevent selected extra channels before observation; privately compute or release data according to a specified interface. | Stronger setup, availability and corruption assumptions. No generic blockchain implementation follows. |
| Two-player zero-sum restriction | Useful value results and a possible route from a preserved Nash law to some SE outcome implementation. | Expected value is weaker than outcome-law preservation; repair need not be a fixed playerwise compiler. Current general reactive SE bridge remains open. |

Timed or threshold recovery can remove an owner's later veto over opening;
it does not stop an owner who already knows transferable opening material
from sending it early. Boneh–Naor timed commitments expressly allow normal
opening and add forced opening under sequential-work assumptions. Keeping
the witness outside the owner changes the service and possibly the game.
[Timed Commitments, Section 2](https://www.iacr.org/archive/crypto2000/18800237/18800237.pdf),
[cryptographic future work](../cryptographic-runtime-future-work.md).

## Primary results that guide the boundary

- **Computational SE preservation:** Halpern, Pass and Seeman, Theorem 4.6
  in arXiv:1506.03030v1 (9 June 2015),
  derive computational SE from a perfect-recall source SE under their
  representation conditions. Those conditions relate histories, utilities,
  implemented strategies and feasible deviations. The conclusion uses
  computational indistinguishability and negligible approximation, not exact
  classical SE over every bit-string distinction. Their commitment example
  also shows why reverse equilibrium correspondence need not hold when players
  coordinate on revealing encodings. This is a direct future-crypto target.
  [Computational Extensive-Form Games, arXiv v1](https://arxiv.org/pdf/1506.03030v1).
  The same preservation statement is Theorem 4.5 in the
  [Cornell author PDF](https://www.cs.cornell.edu/home/halpern/papers/kuhn.pdf).
- **Actual mediator elimination for SE:** Geffner–Halpern prove implementation
  of mediated `k`-resilient sequential outcomes with `n > 3k` synchronously and
  `n > 4k` asynchronously. Their authenticated communication model, secure
  computation and common consistent beliefs are substantive. The main results
  restrict outcome probabilities to rationals; asynchronous delivery is
  eventually guaranteed and need not satisfy a fixed deadline. Communication
  is present on both sides. This does not implement an arbitrary silent
  two-player source over our pending-message service.
  [Communication games, sequential equilibrium, and mediators, Sections 2–6](https://arxiv.org/html/2309.14618v3).
- **Preserve allowed communication, suppress implementation-added channels:**
  Alwen–Katz–Maurer–Zikas fix the same external resources in both worlds.
  Their collusion-preserving formulation is stronger than collusion-freeness;
  general constructions require resources providing isolation, independent
  randomness and programmability. The stated impossibilities concern their
  general functionality/resource setting, not every individual game.
  [Collusion-Preserving Computation, Sections 1–2](https://www.iacr.org/archive/crypto2012/74170124/74170124.pdf).
- **Normalization before reception:** Mironov–Stephens-Davidowitz construct
  protocol-specific reverse firewalls that modify traffic without reading
  the protected party's private state. Their security/exfiltration definitions
  show what a stronger normalizing service can promise. Mere canonical
  serialization or post hoc inspection is not such a construction; an SE
  implementation theorem remains a separate obligation.
  [Cryptographic Reverse Firewalls, Sections 1–2](https://www.iacr.org/archive/eurocrypt2015/90560152/90560152.pdf).
- **Interested enforcers require a coalition model:** Kelkar et al. study
  provable whistleblowing and colluders' enforceable retaliation contracts.
  Their impossibility and conditional positive results rule out treating a
  bounty as unconditional honesty. We have not instantiated their financial
  assumptions or proved reporter equilibrium here.
  [Breaking Omertà](https://eprint.iacr.org/2025/1582).

## Future work: reducing channel value

Batching, shuffling, fixed fees and canonical fields may reduce particular
signaling opportunities. Ledger batching does not erase earlier pending
observations; normalizing one field leaves other permitted choices, including
cryptographic randomness, unless normalization precedes reception. Noise need
not make channel capacity zero, as Shannon's noisy-channel analysis shows.
[A Mathematical Theory of Communication, Sections 12–13](https://people.math.harvard.edu/~ctm/home/text/others/shannon/entropy/entropy.pdf).
A cost-free increase from 50% to 55% correct guessing is still profitable for
a player rewarded for accuracy. A promising future route combines bounded
utility, communication/checking costs or strict incentive margins with
quantitative information bounds. Exact SE requires conditional incentive
bounds at every relevant information set, including rare ones; an average
noise or mutual-information bound alone supplies no such result. An
approximate-SE bridge from these bounds remains future work.

## Cheapest concrete next proof

Use the existing raw reactive response space. Classify its effects into game
moves, ambient communication, and operationally inert distinctions; prove
that classification preserves the actual observations and continuations.
This gives a falsifiable operational target for one semantic edge. It avoids
postulating the strategic conclusion as a service axiom.

Then discharge an ordinary-source extension criterion for a useful subclass:
the checked finite decision class, or a concretely enforced communication
policy. Stop weakening the environment when a permitted observable channel
fails that criterion; retain that channel in the interpretation instead.
Do not add language flags for every backend mechanism.

All current unilateral-SE conclusions remain distinct from CE or coalition
preservation. Shared recommendations, keys, witnesses, side payments and
jointly controlled reporters alter the deviation class. Zero-sum value
invariance or a unilateral fine calculation does not discharge those cases.
Miner/validator participation and Ethereum deployment feasibility are deferred
economic/engineering questions; this audit supplies no deployment guarantee.
