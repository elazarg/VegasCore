# Intended-game equilibria and quit handlers

Quit handlers can substantially weaken the global-abort proposal. Preserving an
intended-game SE does not require every survivor to receive an abort floor.
A sufficient source-level construction caps the first quitter's utility and
completes the other players' handler continuations sequentially rationally.
The private-mempool compiler must additionally preserve the attribution and
information assumptions of that construction.

These are mathematical results and source-interface observations, not a newly
checked runtime theorem. See the [compiler analysis](se-private-mempool-compilation.md)
for the independent operational product theorem, and the
[mathematical foundations](se-private-mempool-mathematics.md) for simultaneous
completion on actual information sets.

## Which source equilibrium is being preserved?

There are two different targets.

* The **intended game** permits guard-satisfying owned commitments and requires
  owned reveals to open. An SE here need not remain an SE when quitting is added.
* The **game with exposed quitting** includes the legal Quit moves and their
  programmed consequences. Its SE already accounts for profitable quitting,
  possibly including quitting on the equilibrium path.

For intended-game preservation, the desired statement is

\[
 \forall \sigma\in\operatorname{SE}(G_{\rm int})\quad
 \exists \widehat\sigma\in\operatorname{SE}(G_{\rm runtime}):
 \operatorname{Law}_{\widehat\sigma}(\theta,\mathrm{terminal},\mathrm{result},u)
 =\operatorname{Law}_{\sigma}(\theta,\mathrm{terminal},\mathrm{result},u).
\]

In particular, the target has no quitting on paths of the selected intended
law. The product theorem in the compiler analysis can take \(G_{\rm int}\) as
its source; it does not require the chosen SE already to tolerate Quit.

This matches the existing [intended model](../Vegas/Source/IntendedGame.lean)
and the source-equilibrium premise of the
[concurrent contract](../Vegas/Game/ConcurrentRawSequentialPreservation.lean).
The separate existing source-level theorem
`Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_preserved` in
[IntendedPreservation.lean](../Vegas/Game/IntendedPreservation.lean) extends an
intended SE under the forfeit pass, for its stated finite, well-formed source
model. It does not remove the concurrent runtime's observation hypotheses.

If the target instead preserves the full quit-enabled language, its handlers
are part of the game being preserved. Replacing them with a global burn or a
different continuation changes that game. An intended-game theorem permits
more freedom on failure branches, but that freedom must be stated explicitly
when a program supplies its own handler semantics.

## What the Vegas language exposes

The sibling Vegas compiler represents persistent quitting explicitly. Its
[move enumeration](https://github.com/elazarg/vegas/blob/8d306fb21dd0aca30670b6589ca4d1f6e8894c2a/src/main/kotlin/vegas/semantics/Semantics.kt)
offers Quit to strategic roles at applicable move sites, and
[history semantics](https://github.com/elazarg/vegas/blob/8d306fb21dd0aca30670b6589ca4d1f6e8894c2a/src/main/kotlin/vegas/semantics/History.kt)
removes future moves after a role quits. Joins are preconditions, and chance
draws are not strategic Quit choices.

Subset-sensitive settlement is expressible through missing-value tests:
[CongestionRouting.vg](https://github.com/elazarg/vegas/blob/8d306fb21dd0aca30670b6589ca4d1f6e8894c2a/examples/CongestionRouting.vg)
distinguishes either singleton quitter and both quitters. The
[handler lowering](https://github.com/elazarg/vegas/blob/8d306fb21dd0aca30670b6589ca4d1f6e8894c2a/src/main/kotlin/vegas/frontend/ToIR.kt)
also produces conditional payout expressions for failure branches.

There is a distinction between that implemented payout machinery and general
continuation games. The
[handler design](https://github.com/elazarg/vegas/blob/8d306fb21dd0aca30670b6589ca4d1f6e8894c2a/docs/SUBGAMES.md)
describes transfers into other games, whereas the
[outcome AST](https://github.com/elazarg/vegas/blob/8d306fb21dd0aca30670b6589ca4d1f6e8894c2a/src/main/kotlin/vegas/frontend/Ast.kt)
contains payout/conditional/let outcomes and split/burn/null forms, and the
[handler checks](https://github.com/elazarg/vegas/blob/8d306fb21dd0aca30670b6589ca4d1f6e8894c2a/src/main/kotlin/vegas/TypeChecker.kt)
restrict direct multi-party handlers to those built-ins. The theorem below
allows general finite continuation games as a mathematical semantic extension;
it does not claim that every such handler is implemented.

## A first-quitter extension theorem

Let \(G\) be a finite perfect-recall intended game, with bounded terminal
utilities. Add a Quit action at each original information set. Its execution
enters a finite handler continuation, potentially with further moves, private
information, additional quits and subset-dependent payoffs. Retain the original
information, moves, chance laws and successful payoffs on every no-quit history.

Require that handler histories do not merge into original no-quit information
sets. A retained public quit marker suffices. This is not a prohibition on
reusing program locations: a continuation at the same code location with
\(Q\ne\varnothing\) is a distinct information state from one with \(Q=\varnothing\).
The whole extended game must have perfect recall.

For every possible first quitter \(i\), require

\[
 u_i^{\rm handler}(z)\le F_i\le\min_{z'\in Z(G)}u_i(z')
\]

at **every terminal continuation** after that first quit, regardless of later
quits, messages, handler choices or the final quitter set. This is a bound on
the quitter's actual utility, including penalties, not merely a payout field.
Other players' bounded utilities can be arbitrary.

For handlers indexed only by the final subset Q, a convenient stronger rule is
to cap every i in Q and make Q monotone. That keeps the first quitter's cap
without storing the order of quitting. If several quits are first recorded
together, cap every member of that first set. Survivors remain unrestricted.

**Theorem.** Every selected SE of \(G\) has an SE extension to this game with
the same initialized terminal/payoff law and no on-path quitting.

**Proof.** Let \(s_n\) be a common fully mixed consistency witness for the
selected source assessment. At original information sets prescribe

\[
 t_n(\mathrm{Quit}\mid I)=\delta_n,\qquad
 t_n(a\mid I)=(1-\delta_n)s_n(a\mid I),\qquad \delta_n\downarrow0.
\]

Complete all handler information sets simultaneously by constrained
information-agent equilibrium, using positive action floors whose total mass
tends to zero. Such a completion exists in the finite game. At a handler site,
exact agent optimality divided by its positive reach bounds the local regret
by its total floor mass times the terminal utility spread. The reach may be
arbitrarily small; this bound has no inverse-reach loss.

No handler strategy occurs on a path to an original information set. If such
a history contains \(k\le H\) strategic decisions, its target/source reach
ratio is \((1-\delta_n)^k\). After Bayes normalization these uniformly
multiplicative errors tend to one, including at source-off-path sites.

From an original history, either continuation follows the original source
until the horizon, or a future Quit occurs. The latter has probability at most
\(H\delta_n\) under prescribed play. Bounded utilities therefore make the local
gain of every original action converge to its source gain. Quit itself has
value at most \(F_i\), while the limiting source continuation has value at least
\(F_i\). Thus all original-site local gains have nonpositive limits.

Take one common subsequence of the entire target profiles and their Bayes
beliefs. It supplies consistency everywhere, handler rationality by constrained
completion, and original-site rationality by the preceding bounds. Perfect
recall gives sequential rationality. Quit probability tends to zero, so the
original initialized joint law is preserved. QED.

Private initial types can be arbitrarily correlated. A public quit marker does
not make hidden types common knowledge, and a public continuation region need
not be a classical singleton-root subgame. Joint completion handles this
without independently inventing entry beliefs for each handler.

This is the same mathematical pattern as action-restriction extension.
[PassageRestrictionExtension.lean](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean)
already provides generic comparison-based extension machinery; a handler
application should supply the restriction and payoff bound rather than add a
second generic equilibrium-existence layer.

## The cap can be weaker than a global worst-outcome bound

For one selected source assessment, the direct incentive requirement is

\[
 W_i(I,\mathrm{Quit};\tau,\widehat\mu)\le V_i^G(I;\sigma,\mu),
\]

where \(W_i\) is the expected utility in the actual handler continuation.
Its continuation must itself be sequentially rational, and its beliefs must
come from the same full-game consistency sequence as the original sites.
An arbitrary payoff promise or a separately chosen Bayesian prior does not
meet this requirement.

A uniform cap \(F_i(I)\le V_i^G(I;\sigma,\mu)\) on all continuations after
Quit at \(I\) suffices by the same proof. A pointwise cap below every source
outcome is convenient because it works for every source SE before selecting
one. It is not necessary.

For example, suppose normal play pays each player either 74 or 126. After
Alice quits, Bob can continue to receive 150 while Alice gets 50, or quit too
so both receive 100. Bob uniquely prefers continuing. Alice's credible handler
value is therefore 50, even though the handler contains a terminal outcome
paying her 100. An all-terminal cap of 74 fails, but this one-player handler's
unique rational continuation supplies the needed bound. With several players,
the continuation selection and common consistency obligations must be proved.

Handler subgames also allow survivors to be rewarded or to keep playing.
Only the first quitter needs the bound in the sufficient theorem; no uniform
all-player floor or burn of innocent participants' funds is required there.
For a finite handler with utility bounded above by \(U_i^{\rm handler}\), a
collectible, nonrefundable quitter penalty
\[
 D_i\ge \max\{0,U_i^{\rm handler}-L_i^{\rm intended}\}
\]
is one way to force the uniform bound. Later quit-set transitions must not
restore the penalty. Such a pass preserves intended successful utilities but
changes quit-enabled semantics if those penalties were not already part of it.

## Why subset-sensitive handlers change the runtime proof

The independent operational product theorem uses the payoff form
\(F_i+B(u_i-F_i)\), with a failure baseline unaffected by operational choices.
General handlers instead give failure value \(W_i(Q,h)\), possibly from a
continuation game. A player can prefer failure by someone else to successful
execution. The operational game is then not simply the common-interest game
of maximizing completion.

This need not prevent SE preservation. It changes what the compiler must prove:

* Legal native semantic choices must correspond to legal intended/source
  continuations using the player's actual information.
* A native deviation treated as the player's own Quit must incur the appropriate
  handler comparison, including every later quitter-set change.
* A player must not gain by forcing or falsely attributing somebody else's
  omission. Readiness, service isolation, phase barriers and audit enforcement
  must justify the attribution.
* The handler's ledger and private observations must match its source
  information model. Preserving only the set \(Q\) does not preserve beliefs
  after privately received openings or discarded attempts.

A minimal attribution counterexample makes the missing premise explicit.
Let the intended game have only payoff \((0,0)\). Alice's Quit pays \((-1,+1)\);
Bob's Quit pays \((+1,-1)\). The first-quitter theorem applies to the abstract
game: neither player wants to quit. But if the runtime lets Alice force a
timeout attributed to Bob, she gains \(+1\), and no equilibrium preserving
\((0,0)\) can use the prescribed successful behavior. This added runtime action
is excluded only by an actual attribution/isolation argument.

Thus subset-sensitive quit handlers offer a less destructive alternative to
global abort and can support intended-game preservation. They do not by
themselves solve private-mempool information transport or timeout attribution.
The choice is between a simpler common-interest operational proof and a richer
handler-aware proof, with the successful intended game unchanged in both.
