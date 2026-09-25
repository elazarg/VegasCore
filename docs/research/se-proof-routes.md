# Routes to source-to-native sequential equilibrium

## Recommendation and theorem contract

The first positive target is **A instantiated on the actual native terminal
sender/receiver decision protocol**, using passive monitoring and conditional
collection. The minimum goal is one fixed compiled game implementing every
source SE's joint outcome and net-payoff law; a playerwise strategy compiler is
a useful stronger guarantee where available. Keep source syntax unchanged.
Use **B, an independently specified ambient communication interpretation**, for
general playerwise semantics after this pilot, or if its audit exposes channels
that conformance cannot remove. C is an alternative for competitive games.
These assumptions are incomparable: changing the source environment,
restricting utilities, and adding enforcement have no globally weakest member.

Fix a source program `P`, utilities `u`, a native service `N`, and decoder `d`.
Let `Law` retain private initial parameters jointly with public game results;
include monetary deductions if claiming net payoff preservation. Distinguish:

1. **Outcome implementation:** for every source SE, some native SE has the same
   decoded law. Strategies may depend on the full source assessment without
   runtime access to opponents' policies. Additional native equilibria remain possible.
2. **Fixed playerwise preservation:** choose `C_i : Strategy_i(S) → Strategy_i(N)`
   once; for every source SE `(σ,μ)`, some `ν` makes `(Cσ,ν)` a native SE and
   `d_* Law_N(Cσ) = Law_S(σ)`. `C_i` cannot inspect opponents' supplied policies.
3. **Value equality:** expected utilities coincide. This is weaker than either.

A utility-indexed compiler may inspect the game's public utility specification.
That is different from choosing new fines, a new target game, or an off-path
completion separately for each equilibrium. Every claim below fixes the target
game before quantifying over source equilibria.

## Route comparison

| Route | Exact intended quantifiers and conclusion | Additional sufficient assumptions | Main unresolved proof |
| --- | --- | --- | --- |
| A. Genuine action restriction plus sanctions | For fixed payoff bounds, monitoring and fines: `∀ SE(S), ∃ SE(N)` extending compliant play and preserving its initialized law. A fixed playerwise `C` requires an additional local completion construction. | Same game/information on compliant histories; every first forbidden departure has a compliant replacement; bounded gain; sound, attributable, collectible conditional sanctions; finite perfect recall. | Complete optimal behavior at new sites using one consistent sequence, then instantiate every enforcement and conformance premise on the actual runtime. |
| B. Ambient source with direct native quotient | `∃ playerwise C, ∀ u,σ,μ, SE(S_ambient,u,σ,μ) → ∃ν, SE(N,u∘d,Cσ,ν)` with joint law equality. Ordinary-source SEs qualify only through a separate extension theorem. | Source communication opportunities and observations match the actual service; all retained deviations have source accounts; erased distinctions are operational/incentive aliases; finite belief-compatible lifting. | Prove the source service correspondence, conditional deviation transport and common Bayes lift; the current synchronous experiment is not the native service. |
| C. Two-player zero-sum repair | For one fixed native game: `∀ SE(S,u), ∃τ,ν, SE(N,u∘d,τ,ν)` with source initialized law, obtained by repairing `Cσ`. | Actual source Nash preservation into this same finite perfect-recall native game; exactly two strategic players; zero-sum native utility. | Finish the general law-preserving Nash-to-SE repair and the command-service/reactive-service bridge. |

Common finite-model obligations are substantive: finite legal responses and
bounded interaction, adequate evaluation fuel, positive chance reach for legal
histories, and the actual observation/recall structure. Timeouts do not bound
all pre-deadline communication. A decision antichain is not automatically the
global perfect-recall hypothesis used by A/C. Prove the required decision-recall
property or a semantics-preserving adapter; do not add scratch-memory states.

## A: what sanctions do and do not buy

The checked [finite sender/receiver theorem](../../GameTheoryExtensions/Analysis/Protocol/DisclosureEnforcementEquilibrium.lean)
already has fixed game-wide range fines and a playerwise compiler for all source
SEs. Its off-path completion is unusually simple: full disclosure identifies
the state, and the receiver has one final utility-maximizing decision.

Replacing its charge by probabilistic collection requires a bound conditional
on each sender type and forbidden action. Terminal collection changes expected
utilities without creating decision information; zero charges on prescribed play
retain its net-payoff law. Collection observed before the receiver acts must stay
in its observation. If lawful signals have a type-independent
law `L`, and forbidden trembles induce `Bθ`, Bayes weights are
`πθ((1−ε)L(y)+εBθ(y))`: their limit is the prior when `L(y)>0`, and the
normalized `πθBθ(y)` otherwise. A fixed optimal terminal response at each new
signal can therefore handle monitoring without an equilibrium-specific game.

For a general finite action restriction, the promising construction pins a
source consistency sequence at compliant sites and makes forbidden trembles
`o(minimum positive source-history reach)`. It completes new-only sites in
finite perturbed continuation games, then takes one common subsequence.
This preserves old beliefs while permitting rational reactions to disclosure.
New-site completion may depend on opponents' pinned policies: the construction
does **not** yet prove a fixed playerwise compiler. A public terminal abort or
a genuinely local terminal response could remove that dependence, but each is
a further service/game restriction.

Missing Lean obligations are finite constrained continuation equilibrium
existence, negligible contamination of old Bayes fibers, whole-policy
rationality of the completion, and a first-departure replacement argument.
The existing [local enforcement bounds](../../GameTheoryExtensions/Analysis/Enforcement.lean)
and [consistent completion](../../GameTheoryExtensions/Analysis/Protocol/ConsistencyCompletion.lean)
do not provide those conclusions jointly.

Runtime obligations remain even after that theorem: sanctions must be sound
for **all** permitted source strategies; observation/reporting/collection bounds
must hold conditional on the sender's information and chosen departure; the
liable account and remaining collateral must be justified. A spent deposit is
irrelevant to later disclosure. Strategic reporters need their own incentives.
Positive passive sampling alone supplies none of these guarantees.

**Decisive gate:** on an existing multi-stage Vegas graph and its actual raw
response menu, classify the first unsupported transmission and prove a sound
positive conditional collection bound. Include an early certificate and a
premature ordinary opening. If the latter is still admitted and changes a
later information set, stop: a larger fine cannot repair missing conformance.
The [shape checker](../../Vegas/Pending/ReactiveConformance.lean) explicitly
admits certificate-free early openings. Separately test whether off-path
completion can be playerwise before advertising that stronger compiler claim.

## B: semantic abstraction without hiding communication

Specify one source interpretation using named game facts, attempted game
actions, optional observations of pending communication, public recording, and
the service's observable opportunities/deadlines. Retain certificate forwarding,
setup correlations and evidence acquired before a candidate's game association.
The service must be defined independently of the compiled handler. It is a
parameter of strategic semantics, not another program language or tower stage.

The checked [response-alias theorem](../../Interaction/ReactiveAliasEquilibrium.lean)
is a real template: playerwise canonical strategies, every continuation-policy
deviation, projected beliefs from one common sequence, and initialized law.
Its scope is private names of operationally identical responses. It supplies
no license to erase observable packet variation, clocks or disclosure.

Required Lean work: implement source communication policies in the existing
reactive runner; prove source observation reconstruction and all-history
action correspondence; construct deviation backtranslations at each decision
fiber; prove finite perturbation/Bayes projection; compose with the existing
source/EventGraph relation and raw-response alias lift. The existing immediate
delivery roster in `Interaction.CommunicationInterface` must be reconciled with
delayed, partial native observation; calling both services “communication” does
not identify their games.

**Decisive gate:** use the existing selective-association native fixture, with
its real passive observation and later binding. Define its source trace using
the independent semantic interface, then prove the observation-fiber and
whole-continuation law correspondence for every bounded raw response, not just
the profitable witness. It must also represent failed authenticated publication.
One failure identifies a missing source-visible feature before generalizing.

This route preserves SEs of the communication-aware game. Extending an
ordinary-source SE is an additional theorem. Competitive finite decision games
and enforceable conformance are useful sufficient subclasses.

## C: outcome repair with a separate runtime bridge

The [written repair proof](../zero-sum-sequential-repair.md) protects the original
Nash profile's reached decisions, regularizes finite trembling plans, and
repairs only off-path behavior. Finite plan/tremble facts and the L1 saddle
construction are checked; conditional continuation locality, smoothing bounds,
the execution bridge and final common-limit argument remain open.

The [checked pending-game theorem](../../Vegas/Game/ZeroSum.lean) gives value
equality, including arbitrary coarse-correlated native equilibria. Its target
is the command-policy service. The required SE target is the finite reactive
service: use the [explicit bridge work list](../zero-sum-runtime-bridge.md),
not a change of names. Service completion alone is insufficient; the compiler
must conceal rejected openings and reconstruct effective source choices and
observations against all opposing native policies.

**Decisive gate:** prove one parameterized two-player source Nash certificate
for the actual recurring reactive service and full bounded raw response menu,
with joint initial-parameter/result law equality. Test malformed/unopenable
commitments, rejected openings and at-most-once premature inclusion. If this
bridge fails, completing the abstract repair theorem will not close native SE.
Repair remains whole-profile outcome implementation. A strategic watchdog adds
a player; burned fees or external transfers may destroy the zero-sum premise.

## Sources and stopping rule

[Dilmé (2024), §§2.4, 4.1](https://doi.org/10.3982/ECTA21402) relates sequential
outcomes to vanishing perturbations and distinguishes dominated-action
elimination for sequential stability. It does not establish route A's proposed
compiler theorem. [Halpern, Pass and Seeman, Theorem 4.6,
arXiv:1506.03030v1 (9 June 2015)](https://arxiv.org/pdf/1506.03030v1)
prove computational SE preservation from a history/strategy representation;
this supports B's obligation structure, not a present cryptographic result.
The same preservation statement is Theorem 4.5 in the
[Cornell author PDF](https://www.cs.cornell.edu/home/halpern/papers/kuhn.pdf).
[Geffner and Halpern (2024)](https://arxiv.org/abs/2309.14618) implement mediated
resilient SEs under explicit communication/participant assumptions; their
`n>3k` synchronous and `n>4k` asynchronous results do not give a two-player
blockchain shortcut. [Miltersen and Sørensen (2006)](https://pure.au.dk/portal/en/publications/computing-sequential-equilibria-for-two-player-games-2/)
construct an SE in finite two-player zero-sum perfect-recall games; preserving
an arbitrary prescribed Nash outcome is the additional unformalized claim in C.

Do not accept “assume target consistency and incentive-cone inclusion”, “assume
an optimal consistent completion”, or “assume no extra information” as the
remaining native theorem: these repackage its central obligations. Prove the
corresponding facts from actual transition and observation rules. Finish one
decisive runtime gate before introducing further semantic machinery or claiming
a smallest realistic assumption set.
