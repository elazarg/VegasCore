# Auctions: outcomes, private values, and truthfulness

This is an open design discussion, not a specification. A claim is established
only where a Lean name is given, as in
[Checked facts relied on](#checked-facts-relied-on). Everything else is a
proposal, a proof sketch, or an open question. When a question resolves, move
the decision into the document that owns it, such as the
[source semantics](source-semantics.md), the
[outcome/utility distinction](outcomes-and-utilities.md), or the
[road ahead](a-road-ahead.md), and remove it here.

## The problem

A Vegas program settles with one integer per player. An auction outcome has
more structure: who receives the good (allocation), what each player pays
(transfers), and how much each bidder values the good (private values). An
auction whose settlement is its only description falls into one of two failure
modes:

- **No value term.** Winning only costs money, so no bidder gains by winning,
  and truthful bidding has no content. If every tied top bidder is charged, one
  item is also sold several times.
- **Value paid out as money.** The buyer's surplus becomes a transfer that no
  participant deposited. With deposits of 100 each, a value of 10, and a price
  b scaled by 10, the seller receives 100 + 10b and the buyer 100 + 10(10 − b):
  300 paid from a pot of 200.

The goal is to write auctions whose game-theoretic claims, truthfulness in
particular, are stated about the source program and carried to the runtime.

## Checked facts relied on

- The source game form's outcome is the public source result
  (`Vegas.SourceProgram.gameSignature`, `Vegas.SourceProgram.PublicOutcome`):
  the publications and public samples, projected by
  `Vegas.SourceProgram.publicOutcome`. Payoffs are a separate reading of the
  same context (`Vegas.SourceProgram.evaluatePayoffs`), and the utility is
  chosen outside the game form. The complete terminal state remains the
  internal object that `Vegas.SourceProgram.Setup.run` produces.
- Nash correspondence holds at compiled profiles for every real utility of that
  result (`Vegas.Paper.source_event_graph_approximate_nash_iff`,
  `Vegas.Paper.source_event_pending_approximate_nash_iff`).
- The compiled honest profile has the source terminal-state law
  (`Vegas.Paper.source_event_pending_honest_law`). For a fixed profile, a native
  unilateral replacement, and a real-valued test of the terminal state, some
  source policy does at least as well
  (`Vegas.SourceProgram.Setup.eventPendingGame_deviation_utility_bound`). That
  witness may depend on the profile and on the test.
- The canonical graph deviation law uses an explicit backtranslation that
  depends only on the program and the replacement policy
  (`Vegas.Paper.source_event_graph_canonical_deviation_law`). The scheduled graph
  and pending-message deviation laws are existential per profile.
- A `Vegas.SourceProgram.Setup` carries a finite prior over initial states,
  including private cells. A player observes exactly their own private cells.
- Every initial private cell is a publication obligation, and `ret` requires no
  open obligation, so the program must contain a `reveal` for each one.
- `sample` binds public data only. There is no private chance.
- `ret` payoffs are integer expressions over the public context. Nothing checks
  conservation.
- Every `commit` may bind failure and every `reveal` may withhold. A policy's
  decision observes all earlier publications.
- `GameTheory` has quasilinear and Bayesian direct mechanisms
  (`GameTheory.Mechanism.QuasiLinearMechanism`,
  `GameTheory.Languages.BayesianMechanism.IsIncentiveCompatible`), dominance over
  arbitrary or restricted opponent classes (`IsDominant`, `StrictlyDominatesOn`),
  and the finite revelation principle
  (`GameTheory.BayesianGame.revelation_principle`). None of these is connected
  to source programs.

## Organizing principle: operational versus analysis data

Private values, priors over them, utility functions, and the solution concept
have no operational meaning. No contract reads a bidder's valuation. They belong
to the analysis of a program, and need not appear in the executable language at
all. Transfers, collateral, disclosure order, failure settlement, and the
allocation *when the runtime must effect it* are operational and belong in the
program.

Consequences:

- A reserve price is operational because settlement reads it. The seller's value
  for the good is not. A hidden-reserve auction commits the former; the latter
  is analysis data.
- Removing values from the language does not remove them from the theorems.
  Strategies still depend on them, and Bayesian notions still need a prior. The
  analysis layer must supply both, and the transfer results must accommodate
  them (see [Transfer to the runtime](#transfer-to-the-runtime)).
- An allocation read only by a utility is analysis data too. It becomes
  operational when something must deliver the good.

## What the outcome must provide

Position under discussion: the outcome is the final environment, or a
declaration computed from it, and a payoff is one possible interpretation of it.
The outcome needs no common-knowledge interpretation of its own. The utility
*is* the interpretation, and it is the only common-knowledge requirement,
because strategic reasoning about other players' reasoning goes through it.

Refinements:

- **Private values.** What is common knowledge is the type-indexed utility
  family and, for Bayesian notions, the prior. The realized type is private.
  Dominant-strategy notions need no knowledge of other players' utilities at all.
- **The rules.** Reasoning about others maps profiles to outcome laws, so it also
  uses the game form. For a Vegas program that is the program and its semantics,
  both public. At compiled profiles, the compilation theorems let players reason
  about the source game in place of the runtime game they actually play.
- **No observation requirement.** Equilibrium reasoning evaluates expected
  utility over outcome laws, so no player needs to observe the realized outcome.
  That is a fact about the reasoning, not a licence to prefer outcomes by what
  stayed hidden: under the decision below, a utility cannot read a committed but
  withheld bid, because such a binding is not part of an outcome at all.
- **Epistemics are not hypotheses.** The Lean results make no epistemic
  assumption. Common knowledge justifies using a solution concept; it is not a
  premise of any theorem.
- **Operational requirements are separate.** Whatever the runtime enforces must
  be computable from what the runtime holds. That is why `ret` payoffs range over
  the public context, and why a declared result (A3) or a delivery (A4, A5) would
  need public determinability. The reason is operational, not game-theoretic.
- **Payoffs are also effects.** A payoff is an interpretation for the analysis
  and an enforced transfer for the runtime. Only the interpretive role is
  optional.
- **Completeness.** Preferences must factor through the outcome. A player who
  cares about something outside it, such as timing, fees, or receipts, plays a
  richer game (see the [outcome/utility distinction](outcomes-and-utilities.md)).
- **Preservation.** The runtime result must decode to the outcome, so that
  utilities of the outcome transfer.

**Decision.** The game-form outcome is the public source result: the
publications and the public samples, exactly what `sourcePublicEnv` projects
out of the terminal state and exactly what settlement itself reads. Private
bindings leave the outcome. Common knowledge was never the reason to shrink it;
the reasons are that a preference over what a player kept secret is not a
preference over anything the protocol produced, and that every later edge then
owes a smaller decoder.

Consequences:

- Commit failure and reveal refusal induce the same outcome. A native
  unopenable binding may be backtranslated to a refusal, so the tower carries
  fewer failure modes.
- Utilities may not read what a player kept secret. Private values are analysis
  parameters (V1). V2 loses its one advantage, that a prior inside a `Setup`
  let the existing correspondence cover Bayes-Nash directly — an advantage
  already weakened by the rule that every initial private cell must be
  revealed.
- Nothing needs reproving. Each checked law is stated at the complete terminal
  state, and its public form follows by instantiating the utility at
  `utility ∘ project` or by mapping both sides of a law through the projection.
  The state-level law stays as the internal lemma.
- The executable language does not change. This is a decision about the
  analysis surface, not about what a program may do.

This is now the checked statement. `Vegas.SourceProgram.gameSignature` carries
the public result, `Vegas.SourceProgram.Setup.publicRun` is the law a profile
induces, and the capstones quantify over utilities of it. The state-level laws
stayed where they were: `Vegas.SourceProgram.Setup.run` and
`Vegas.SourceProgram.Setup.eventPendingGame_deviation_law` still speak of the
complete terminal state, and the public forms are derived from them.

## Encoding the allocation

**A1. Read the allocation from the public terminal state.** The utility computes
the winner from the published bids. Define the winner once as a public
expression, use it inside the `ret` payoffs, and evaluate the same expression in
the utility as `evaluatePayoffs` does. Allocation and payment then agree by
construction, including tie-breaks and failure branches.

- For: no language change, and the current theorems already cover it.
- Against: the runtime never sees the allocation, so delivery is an off-model
  assumption. Nothing forces the payoff code and the utility to share the
  expression.

**A2. Decode the allocation from the payoff vector.** For example, "a negative
payoff means I won." Utilities of payouts are attractive: the payout readout is
what the runtime enforces (`Vegas.Paper.source_event_graph_payout_readout`), and
a later edge preserving only payouts would still preserve them. The decoding is
valid only when the allocation is a function of the payoff vector. It fails for:

- price zero (a second price with a zero second bid, or a zero reserve), which
  decodes a winner as a loser;
- all-pay auctions and entry fees, where losers pay;
- failure penalties: a slashed bidder decodes as a winner, so with value above
  the penalty, withholding scores above losing honestly, and the analysis would
  recommend defecting;
- ties that charge several bidders.

The utility must also have the shape vᵢ·[i won] + payoffᵢ. Utility increasing in
the amount paid would reward overpaying. Open: is there a natural program class
(positive minimum price, winner-only charges, penalties distinguishable from
prices) on which A2 is exact?

**A3. Declared outcome alphabet.** `ret` additionally returns a public value of
a program-declared finite result type, such as the winner, and the runtime
publishes it. Utilities factor through the result and the payoffs.

- For: the observable target result is named, as the
  [outcome/utility distinction](outcomes-and-utilities.md) asks. An external
  deliverer can act on it. Utilities that factor through it survive edges that
  do not carry the full terminal state.
- Against: a language change, and the result is still only data unless
  something delivers.
- Open: should payoffs be computed from the declared result, so that a price rule
  is applied to an allocation rather than recomputing the winner?

**A4. Several assets.** Payoffs become one column per asset: money and the good.
The seller deposits the good, conservation holds per asset, and the runtime
transfers both.

- For: delivery is enforced rather than assumed.
- Against: an asset model is needed (fungible versus indivisible, non-money
  deposits, exactly one unit assigned), and the runtime obligation grows.

**A5. Delivery as a later strategic action.** The seller transfers the good
after settlement. The trust assumption becomes explicit and analyzable, since
non-delivery is a failure branch. It reintroduces hold-up and needs escrow, and
hence A4, to be credible.

Open: do A1 and A3 differ enough to justify A3 before A4? Should VegasCore check
payoff conservation?

## Where private values live

**V1. Analysis parameters.** Each player has a type space Θᵢ, the utility is
indexed by the type profile, and a strategy is a family σᵢ : Θᵢ → source policy.
The program is unchanged. Dominance and ex-post notions are per type and need no
prior. Bayes-Nash needs a prior over types and a wrapper game at the analysis
level; `GameTheory` already has Bayesian games. The Bayesian transfer is open
(see below).

**V2. Initial private cells in a `Setup`.** The prior draws the types, owners
observe them, and the utility reads them from the terminal state. The existing
Nash correspondence then applies directly: source Bayes-Nash holds exactly when
runtime Nash holds at compiled profiles. The cost is an operational encoding of
non-operational data:

- the runtime must realize the private setup;
- the publication obligation forces a `reveal` per type (withholding it at the
  end, with payoffs independent of it, satisfies the obligation but is still a
  runtime event);
- types share the one prior with genuine protocol secrets.

**V3. A private chance constructor.** Nature draws a value observed by one
player. It has independent uses, such as dealt cards, and needs its own
publication rule. For values it carries the same operational cost as V2.

**V4. Ghost cells.** Initial private cells are marked as analysis-only: no
publication obligation; unreadable by guards, payoffs, and public expressions;
readable by the owner's policy and by utilities; and erased by compilation. This
is V1 expressed inside the source game so that the V2 theorems can be reused.
The erasure edge is the proof obligation.

**Rejected: a value as a `commit`.** The player would choose their own type.

**Interdependent values.** Utilities may depend on other players' types, as with
common values and the winner's curse. V1 expresses this directly. Dominant
strategies generally disappear, but ex-post notions remain definable.

## Utility of money

The Vegas theorems place no restriction on the shape of utility: any real
function of the terminal state, with expected utility over chance and mixed
policies. Linearity in money is therefore not needed for any transfer result. It
enters elsewhere:

- **Values as money.** Reading a value as a willingness to pay in payoff units
  assumes quasilinearity, uᵢ = vᵢ(allocation) + payoffᵢ, with no wealth effects.
- **Risk neutrality.** Randomized tie-breaking, mixed strategies, and chance are
  evaluated by expected utility. With nonlinear money, a lottery over prices is
  not equivalent to its expected price.
- **Mechanism theory.** VCG, the Myerson characterization, revenue equivalence,
  and the `GameTheory.Mechanism.QuasiLinearMechanism` bridge assume
  quasilinearity. The single-object second-price auction is believed to remain
  strategy-proof on general preference domains when a bid is read as willingness
  to pay. Find and cite the precise result before relying on it.
- **Net versus gross payoffs.** A settlement may pay gross amounts that include
  refunded deposits rather than net transfers. A per-player constant offset
  changes no Nash or dominance comparison. A branch-dependent offset, such as a
  forfeited deposit, is a transfer and must be counted.
- **Budgets.** Collateral bounds the bid domain. A bidder whose value exceeds the
  largest payable bid cannot bid truthfully, and budget constraints break
  second-price truthfulness in general.
- **Discreteness.** Bid domains are finite. A value off the grid has no exact
  truthful bid, and ties are common, so tie-breaking matters for weak dominance.

Open: which of these are standing assumptions (for example quasilinear,
risk-neutral, and values on the bid grid) and which are theorem parameters?

## Defining truthfulness

### Prescribed plans

A source program is an indirect mechanism: bidders commit, then disclose, with
failure available at each step. "Truthful" therefore names a prescribed
type-indexed plan σ, not a single action. For a sealed-bid auction, σᵢ(θ)
commits θ, or its image in the bid domain, and always discloses. Incentive
properties are properties of σ, stated with existing `GameTheory` predicates on
`Vegas.SourceProgram.Setup.gameForm`.

Candidate notions:

1. **Ex-post Nash.** For every type profile θ, σ(θ) is Nash under the utility
   for θ.
2. **Dominant strategy.** For every player and own type, σᵢ(θᵢ) is dominant
   under that player's utility (private values).
3. **Dominance over a restricted opponent class,** in the `StrictlyDominatesOn`
   shape. Examples: opponents that always disclose, or whose disclosure ignores
   other players' publications.
4. **Iterated dominance.** First eliminate withholding where penalties make it
   dominated, then require dominance among the survivors.
5. **Bayes-Nash.** σ is Nash of the prior-averaged game.
6. **Designated reports.** One `commit` per player is marked as the report, with
   payload type Θᵢ. The truthful plan commits the true type and discloses. This
   enables a bridge to direct mechanisms.

### Withholding gives later revealers a free option

With sequential disclosure, unrestricted dominance (notion 2) fails for a
commit-reveal second-price auction.

Take bidders A, with value 5, and B. The program commits both bids, then reveals
A's bid, then B's. Settlement:

- both disclose: the higher bid wins and pays the other bid;
- B withholds: A wins at price 0 and B forfeits a deposit.

B's policy commits 4 and discloses only if A's published bid is 5. Truthful A
gets 5 − 4 = 1, while A bidding 6 gets 5 − 0 = 5, so truthful bidding is not
dominant.

In general, such a policy exists whenever some misreport's best case over the
later revealer's disclosure beats the truthful report's worst case. Other
withholding settlements, such as cancelling the sale or treating the withheld bid
as the top bid, admit the same construction. A deposit deters rational
withholding, but dominance quantifies over all opponent policies, including
costly ones.

Decisions this forces:

- Accept notion 3 or 4 as the meaning of truthfulness for commit-reveal
  programs, with the opponent class stated explicitly.
- Or add a simultaneous-disclosure construct to the source, in which no reveal
  decision observes another reveal of the same round. Its runtime counterpart
  must keep a round's openings invisible until every opener has decided. That is
  the same free-option problem at runtime: a hiding commitment does not help if
  a pending or included opening is visible before another opener decides.
- `GameTheory.Languages.BayesianMechanism.IsIncentiveCompatible` quantifies over
  fixed opponent reports. A bridge from source programs must restrict opponents
  (notion 3) or show that the program leaves opponents nothing to react to.

### Bridge to direct mechanisms

Under full disclosure, a program with designated reports (notion 6) induces a
direct mechanism whose allocation and payment are computed from reports.
Candidate statement: notion 3, with opponents that always disclose, holds
exactly when the induced `GameTheory.Mechanism.QuasiLinearMechanism` is DSIC and
the focal player's own failure or withholding is never profitable against
disclosed opponents. The monotonicity results in `GameTheory.Mechanism`
would then apply. Open: the exact statement, and how guard-rejected commitments
enter.

## Transfer to the runtime

Status with types outside the program (V1):

- **Ex-post Nash needs no new result.** It is
  `Vegas.Paper.source_event_pending_approximate_nash_iff` applied at each type
  profile θ, with the utility for θ and the profile σ(θ). A type-indexed wrapper
  would add nothing.
- **Dominance against compiled opponents is checked.**
  `Vegas.SourceProgram.Setup.eventPendingGame_isBestResponse_of_isDominant`: a
  dominant source policy compiles to a best response against every compiled
  opponent profile, against arbitrary native deviations. The per-profile
  version,
  `Vegas.SourceProgram.Setup.eventPendingGame_isBestResponse_compileProfile`,
  carries a source best response at one fixed profile, so notion 3 transfers
  profile by profile for any opponent class, with no dominance needed off it.
  Both specialize the simulation-generic
  `GameTheory.GameForm.UtilitySimulation.isBestResponse_compileProfile`, whose
  proof is the chain

  ```text
  runtime value of τ against compiled π
    ≤ source value of α against π                    (deviation bound)
    ≤ source value of σᵢ(θᵢ) against π               (source best response)
    = runtime value of compiled σᵢ(θᵢ) against compiled π   (honest law)
  ```

  The source witness α may depend on π, which is harmless because a best
  response is checked at a fixed profile.
- **Dominance against arbitrary native opponents is open.** The current
  certificates are unilateral: opponents are compiled source policies. A new
  certificate must simulate every native opponent profile against a fixed
  compiled focal plan. The free-option example shows why this is delicate:
  source dominance depends on what opponents observe before disclosing, and
  native opponents may observe more, such as pending openings or delivery order.
  This connects to the coalition extension in the [road ahead](a-road-ahead.md).
- **Coalition-proofness is reflected, never preserved.**
  `Vegas.SourceProgram.Setup.eventPendingGame_isStrongNash_of_compileProfile`
  carries strong Nash back from the compiled profile, using the honest law
  alone. The forward direction is impossible in general, not merely unproved:
  `GameTheory.GameForm.CoalitionWitness.isEmpty_coalitionSimulation` exhibits a
  target with an exact one-player certificate and no coalition certificate for
  any strategy translation, because one member can route private information to
  another. For an auction this is the difference between bidders who each
  deviate alone and bidders who collude through the runtime, which the timing,
  pre-inclusion delivery, and receipts of the message pool make available.
  `InteractionTests.CoalitionChannel` checks that the pool really is such a
  channel: with every message rejected by the application, it still carries one
  principal's private draw to another before inclusion. Colluding bidders are
  therefore outside every certificate the tower currently has.
- **Bayes-Nash under V1 is open.** Averaging the per-type deviation bound over the
  prior yields a source deviation that may depend on other players' types through
  their policies, which is not a legal type-indexed deviation. There are two
  routes:
  - a backtranslation independent of opponents' policies, as the canonical graph
    edge already has, extended to the scheduled graph and pending-message edges;
  - V2 or V4, where the prior lives inside the `Setup` and the existing Nash
    correspondence applies directly.
- **Raw private bindings are gone.** A utility can no longer read a committed
  but withheld bid: the decoder now recovers the public result only, so nothing
  a player kept to itself is available to prefer over. A2 and A3 utilities need
  less still.

## Channels, and where they belong

The coalition obstruction is checked, and it quantifies over every strategy
translation: `GameTheory.GameForm.UtilitySimulation.isEmpty_of_grandCoalitionValue`
compares one target profile against every source profile, and the grand
coalition overwrites whatever the compiler did. So this is not a statement
about our compiler, and no better one would repair it. It is a statement about
the medium: a runtime where one player acts on private information and another
observes that action before acting cannot implement a game whose analysis
assumes players cannot correlate.

Payload secrecy does not help. In `InteractionTests.CoalitionChannel` the
application rejects every message, so nothing a player sends reaches
application state, and existence, timing, ordering, delivery and receipts still
carry the secret. Capacity can be reduced — encrypted submission, fixed
cadence, padded messages, anonymity, forced participation — but it does not
reach zero while players choose whether and when to act, and an auction is made
of such choices. Collusion-free protocols are known to need physical
assumptions for this reason; find and cite the precise result before relying on
it.

Position, to be settled rather than assumed here: the mismatch belongs in the
adversary a claim quantifies over, not in the executable language.

- **Keep the language medium-general.** A correlation device is not a program
  construct. No contract offers one, and the same language should compile to
  media whose channels differ. Adding one would bake a property of one target
  into the source of all of them.
- **Widen the deviation class instead.** A coalition claim is made against
  source coalitions that may correlate and pool their private observations. A
  dominance claim is made against source opponents that observe what the medium
  exposes. This is the operational/analysis split this document already uses:
  the channel is a property of the target, its consequence is a property of the
  analysis, and neither is a feature of the program.
- **The resulting statements are weaker, and honest.** They establish guarantees
  against an adversary the medium actually permits, instead of against one the
  medium quietly refutes.

For auctions this changes the target property. Collusion-impossibility is not
available on this medium. What can be proved is collusion-resistance: that the
settlement leaves a colluding coalition nothing worth having, which is the
realistic requirement for shill bidding and bidder rings in any case. The same
move applies to truthfulness, where the free-option example already showed the
opponent class to be the delicate part.

Open work under this position: a correlated coalition deviation class on the
source side and a certificate for it at the pending-message edge; the matching
opponent class for dominance; and collusion-resistance for whichever settlement
the auction design settles on. The reflection direction and the refutation
criterion are already checked.

## Retiring commit-time failure

A source policy may bind an unopenable candidate, and it may bind a value and
then refuse to open it. Publicly these coincide: `runWith` proposes
`if disclose then state.get source else .failure`, so a cell bound to failure
publishes failure whatever its owner decides
(`Vegas.SourceProgram.runWith_reveal_of_failure_bound`). Now that an outcome is
the public result, nothing distinguishes them.

The action stays in the syntax anyway, for a reason that only appeared when the
alternative was attempted. `ContextRefs.Agrees` is an *exact* store-to-state
correspondence that holds for arbitrary stores, including those a native
deviator produces with a failed binding, precisely because the source can
represent one. Remove the action and the decoder becomes lossy, so agreement
has to be re-based on public cells throughout the compile layer — churn in
proofs that are currently correct, in exchange for a redundancy that is better
stated than deleted.

So the redundancy becomes a theorem instead. `Vegas.SourceProgram.ValueBinding`
names the policies that never bind failure,
`Vegas.SourceProgram.exists_valueBinding` shows the class is inhabited, and
`Vegas.SourceProgram.Setup.valueBindingGame` is the game they play: the same
program, the same setup law, the same public outcome, only fewer strategies.

`Vegas.SourceProgram.Setup.valueBindingSimulation` is the edge above it, a
mixture simulation to the full source game whose strategy map is the inclusion
and whose outcome map is the identity, so its honest law is reflexivity. Its
deviation certificate is stronger than the mixture the interface allows: each
covered deviation is matched by a *single* value-binding policy, which is
`Vegas.SourceProgram.exists_valueBinding_publicRun_eq`. So an analysis carried
out where failure is only ever a disclosure decision transports along the rest
of the tower unchanged.

What the edge covers is named rather than assumed.
`Vegas.SourceProgram.Setup.BindingConsidered` is the deviation class: every
value-binding policy, and every pure one. Neither contains the other, and their
union is not every policy — one that randomizes between binding failure and
binding a value is in neither. At that class
`Vegas.SourceProgram.Setup.isεNash_valueBindingGame_iff` reads: a value-binding
profile is ε-Nash in the value-binding game exactly when no covered deviation in
the full source game beats it by more than ε.

The proof is not the obvious translation. Replacing a failed binding by the
canonical value and refusing at that reveal is correct for one cell, but the
translated policy cannot tell a patched cell from one where the original
genuinely bound the canonical value, and it must refuse in the first case and
follow the original in the second. A mixture is allowed in the certificate, and
a pre-drawn component cannot depend on the view, so the mixture has to range
over deterministic policies: for those the ambiguity disappears, since a
deterministic policy's own past decisions are recomputable from the current
observation and history. `Vegas.SourceProgram.PurePolicy` names them, with
`PurePolicy.toBehavioral` reading one as an ordinary policy.

Recomputation is what the translation is built around, and it is why the obvious
structural recursion does not suffice. At a reveal, the translated policy must
decide whether *that* cell was replaced, which is the original's decision at the
view it held at the commit. That view is the current one with the cells added
since dropped, and with the own-action history truncated by one per own decision
point — both a fixed number of steps, determined by position in the program. It
is also the *un-patched* view: in the translated run the player's own cell and
its own recorded action differ exactly at replaced cells.

`PurePolicy.bindValuesFrom` is that translation, carrying the two maps the
reconstruction needs, and `bindValues_publicOutcome_eq` proves it preserves the
public outcome law against any fixed opponents. The proof runs the step
invariant `Patched` through the program: a public sample and the other players'
steps change nothing either run can distinguish, the replacement is made at the
translated player's own binding, and at its own reveal the refusal lands where
the original published failure anyway. Guard checks agree because
`Obligation.accepts` reads publications, never a raw binding.

What remains is the predraw, and it is exactly what would widen the deviation
class to every policy: the Kuhn-style statement that a behavioral policy's
law is a finite mixture of pure ones. Only the deviator randomizes in the
certificate, so the single-agent case suffices — but not a per-configuration
one. The mixture has to be drawn before the private initial law, and a single
pure policy has to serve every branch of every chance draw and of every other
player's action. So the naive induction fails: a mixture chosen per branch is
not a mixture chosen in advance.

The standard construction draws independently per *view* rather than per branch:
branches a player cannot distinguish share the draw, and a player meets each
view at most once because each decision point occurs once and views at different
points have different contexts. That needs the finite set of views reachable at
a decision point, which is what `GameTheory.Protocol.Information` supplies
generically through its support-site machinery.
`Vegas/EventGraph/SchedulerProtocol.lean` is a worked instantiation of it, at
the cost of first giving source execution a state-machine presentation.

The same construction is what a later "honest play" layer would need, where
players never refuse to open. Compilation cannot preserve that class
unconditionally, since a native player may always withhold; the interesting
statement there is a conditional one.

## Test programs

Each format exercises a different point:

- **Second-price sealed bid:** dominance, the free option, and ties.
- **First-price:** no truthfulness, and Bayes-Nash bidding needs a prior, so it
  depends on the V1 transfer question.
- **All-pay:** losers pay, which breaks A2, and withholding after seeing others
  is tempting.
- **Entry fee:** a participation decision before bidding.
- **Hidden reserve:** the reserve is operational, while the seller's value is
  analysis data.
- **Randomized tie-breaking through `sample`:** the allocation depends on chance,
  so risk attitude matters.
- **Multi-unit and combinatorial:** `GameTheory` has VCG and knapsack mechanisms.
  Deferred until the single-item questions resolve.

## Open questions

1. The value-binding edge covers pure deviations and value-binding ones, not a
   policy that randomizes between binding failure and binding a value. Closing
   that needs the single-agent predraw, whose mixture is drawn before the
   private setup law and per view rather than per branch. Until then the
   edge yields the class-relative ε-Nash reading, not the unconditional
   transfer. See [Retiring commit-time
   failure](#retiring-commit-time-failure).
2. Allocation encoding: A1, A3, or A4? Is A2 ever the right restriction?
3. Should VegasCore check payoff conservation?
4. Types: V1 alone, or V4 to reuse the prior inside the game?
5. Money: which properties are standing assumptions and which are theorem
   parameters?
6. The truthfulness notion for commit-reveal programs, and whether the source
   needs simultaneous disclosure.
7. The bridge theorem to quasilinear direct mechanisms.
8. Whether the medium's channels are answered by widening the source-side
   adversary, as the position above proposes, or by some change to the language
   itself. This is the open design question, not whether the channels exist.
9. Under that position: a source opponent class matching the medium's
   observations and a dominance certificate against it; a correlated coalition
   deviation class and a coalition certificate at the pending-message edge.
10. Collusion-resistance of the chosen settlement, which replaces
    collusion-impossibility.
11. An opponent-independent backtranslation at the pending-message edge, for
    Bayes-Nash under V1.
