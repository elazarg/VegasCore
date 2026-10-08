# Sequential equilibrium under public stochastic scheduling

Analysis by Codex. This document gives a mathematical construction of a useful
source-to-runtime adapter and identifies its missing Lean implementation. The
general preservation theorem below is a paper proof, not a checked Vegas
capstone. It does not change the asynchronous target, checklist, or semantics.

The positive class is larger than a fixed calendar: delays can be random,
correlated across phases, and adapt to earlier public results. The decisive
restriction is that these are runtime chance moves. Players cannot use the
retained interface to choose an additional signaling channel or a risky
admission lottery.

## A finite public scheduling construction

Let G be a finite, turn-based extensive game with perfect recall. Its primitive
chance transitions, player action menus, and terminal payoffs are fixed.
Suppose logical stage is public at each decision. This holds for the existing
source language: the source view determines instruction position, including
the setup draw, by `Setup.decisionDepth_trace`.

Write h for a source history and I_i(h) for player i's source information.
Choose a public projection P(h). Require **public prefix recoverability**:
whenever two histories belong to the same decision information set, they have
the same logical stage and the same sequence of public projections at all
logical stages up to and including that decision. Equivalently, each P(h_k)
can be recovered from the current source information I. This is an observation
condition on legal
histories, not a condition on beliefs or an equilibrium strategy.

P must include every structural field that the backend exposes at a logical
boundary, such as the acting player or event identifier. Calling a schedule
public does not justify exposing an actor history that the source information
does not retain. The static event owners in Vegas are known from instruction
position; a general game needs the corresponding public-structure condition.

For Vegas, immutable public cells and the public instruction position are the
natural data from which to recover this sequence. Existing observation-back
lemmas recover earlier source views. A complete public-prefix interface still
has to be supplied; arbitrary values accessible to the runtime are not
automatically source-public data.

Expand G as follows. Before each primitive source transition, a scheduler
draws a finite public transcript of waits, public auxiliary results, and a
proceed instruction. Its primitive kernel has the form

\[
  K_k(P(h),\tau,b),
\]

where k is logical stage, tau is the already public auxiliary transcript, and
b is remaining scheduling budget. Every wait decreases b; at zero the
scheduler must proceed. A fixed finite budget bounds physical execution.
Each primitive public draw has finite support.
Kernels can depend on all earlier public auxiliary results and on the public
source history. Independence between delays is unnecessary.

Waits leave the source configuration unchanged and provide no player choice.
On proceed, the original source actor receives exactly its source action menu,
or the original source chance transition executes. Its primitive transition
law is unchanged. The action advances one logical stage. The scheduler starts
another bounded phase. At a player decision the expanded information is
exactly

\[
  J=(I,\tau).
\]

All scheduler draws are represented in tau. Serialization of a source history
and its public scheduling transcript determines an expanded history uniquely.
Private source chance outcomes remain private; they belong to h, not tau.
Terminal runtime payoff is the source payoff of the erased history. In
particular, fees, time discounting, and external opportunities do not introduce
additional action-dependent utility in this construction.

This describes a constructor for an expanded game. It avoids assuming that an
arbitrary target already has the desired posteriors. A concrete backend must
instead prove that its retained execution and observations realize this
constructor, or prove the corresponding primitive transition and observation
identities directly.

## The preservation statement

**Public scheduling preservation, paper theorem.** Under the preceding finite
construction, every sequential equilibrium A=(sigma,mu) of G has a sequential
equilibrium A' of the expanded game with the same distribution of erased
terminal histories and source payoffs. At every expanded decision J=(I,tau),
the strategy is sigma(I), and its belief projects to mu(I). The result also
holds at information sets that have zero probability under sigma.

The theorem asserts existence of a preserving target assessment. Extra public
randomness can support additional equilibria. It does not assert that every
target SE ignores that randomness.

Here is a constructive proof of the information and consistency claim.

Take a source consistency sequence sigma_n: fully mixed source strategies
converging to sigma, whose Bayes beliefs mu_n converge to mu. Lift sigma_n to
every expanded copy of a source information set by ignoring tau. Each lifted
strategy is fully mixed, because the player menus are unchanged; waits and
proceed are chance transitions.

For a compatible pair (h,tau), multiplication of primitive transition
probabilities gives

\[
  w'_n(h,\tau)=w_n(h)L(h,\tau),
\]

where w_n is source reach weight and L is the product of scheduler transition
probabilities along tau. This equality is proved by induction over the actual
expanded history: a wait multiplies only L, and a logical step multiplies
w_n by the original source chance or action probability. Nothing in L depends
on n.

If h and h' belong to the same source information set I, public prefix
recoverability makes every scheduler input in these two products identical
when tau is fixed. Hence

\[
  L(h,\tau)=L(h',\tau)=L_I(\tau).
\]

The same argument gives identical compatibility of tau across the entire
source information set: the primitive scheduling supports depend on those
same public inputs. For a legal expanded site J=(I,tau), L_I(tau)>0. Fully
mixed source strategies give positive reach to every legal source history, so
the Bayes beliefs at I and J are defined at every n. Consequently

\[
  \mu'_n(h,\tau\mid I,\tau)
  =\frac{w_n(h)L_I(\tau)}{\sum_{g\in I}w_n(g)L_I(\tau)}
  =\mu_n(h\mid I).
\]

The beliefs on expanded histories are thus the source Bayes beliefs lifted
through the fixed serialization map for tau. Their convergence follows
directly from source belief convergence. This constructs A' and its single
fully mixed consistency sequence. It never divides a limiting zero
information-set probability: cancellation occurs at each fully mixed index.
No uniform lower bound on off-path site probabilities is required.

If a backend leaves some scheduler randomness unobserved, unique serialization
must be replaced by a fiber sum. The required equation is then

\[
 \sum_{x:\pi(x)=h,\;\mathrm{info}(x)=J}w'_n(x)
   =L_Jw_n(h),
\]

with positive finite L_J independent of h within I. This is still a theorem
to derive from primitive kernels and observation maps. Listing it as an
unproved backend premise is weaker evidence than implementing the public
constructor above.

## Local deviations and terminal laws

Belief transport alone is insufficient for SE. For every compatible expanded
history x above source history h, and for every local lottery beta at J, erase
an expanded continuation in which beta replaces the current choice and all
later sites use lifted sigma. The resulting law equals the source continuation
law from h with beta at I and sigma afterward.

This equality has a separate induction proof. Wait phases do not change h and
must terminate. Their probabilities sum to one. The next logical transition
uses exactly the source action lottery or chance kernel. Future copied
strategies ignore the auxiliary transcript, so the induction continues after
that transition. Inserting beta changes only the current source action law;
its dependence on the fixed J does not produce a history-dependent source
lottery inside I.

Average this equality over the constructed target belief. Its projection is
mu(I), so beta's target continuation payoff equals its source continuation
payoff at I. Source sequential rationality bounds that payoff by prescribed
play. This proves local optimality at every expanded player site. Source
perfect recall, together with retained public auxiliary history, gives perfect
recall in the expanded game. The finite-game one-shot-deviation equivalence
therefore gives sequential rationality for whole continuation policies.

The initialized terminal law follows from the same execution induction without
a deviation. Equivalently, for each source terminal h, summing all compatible
scheduling transcripts gives total scheduler weight one, because every bounded
phase must proceed. The erased terminal law and payoff distribution are
exactly the source laws.

These are two distinct adapters: a prefix reach-weight argument establishes
consistency; a continuation argument establishes incentives. An initialized
outcome coupling by itself establishes neither.

## What the existing Lean APIs establish

The owning layers already provide the following reusable results.

- [SourceInformation](../Vegas/Game/SourceInformation.lean) identifies source
  decision depth and finite history conditions. The observation-back lemmas in
  [ObservationRecall](../Vegas/Source/ObservationRecall.lean) recover earlier
  views on legal source transitions.
- [ServiceInformation](../Vegas/Game/ServiceInformation.lean) and
  [SourceServicePrefixInformation](../Vegas/Game/SourceServicePrefixInformation.lean)
  decode source views from native checkpoints. They establish that native
  information refines source information. They explicitly do not show that
  the additional native fields have constant likelihood within source fibers.
- `conditional_observation_kernel` and
  `exists_updated_observation_kernel`, in GameTheory's existing
  `Math/Probability/ConditionalObservation.lean`, prove posterior cancellation
  and propagation of observation-local noise from primitive channel equality.
  The latter permits hidden-state-dependent source actions and requires the
  new observation to recover the old observation. These are suitable
  probability adapters for the scheduling induction.
- [ObservedChoice](../GameTheoryExtensions/Math/Probability/ObservedChoice.lean)
  turns an observation-local auxiliary readout into a source behavioral choice.
  It is useful when a continuation policy uses ancillary randomness. It does
  not establish that an actual runtime's noise is observation-local, or prove
  protocol-level SE preservation by itself.
- [ProportionalBeliefTransport](../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean)
  performs the exact Bayes cancellation once proportional reach-weight fiber
  sums have been proved. It does not require common decision depth.
- [LocalSimulationLimit](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean)
  can assemble a consistent target sequence with vanishing local comparison
  errors and law errors into a preserving SE. The public constructor should
  supply these inputs with zero errors. Its hypotheses are interfaces to
  discharge, not operational assumptions that a backend gets for free.

No current theorem assembles a general bounded public scheduler constructor,
derives its protocol reach weights, and proves these source continuation
identities. The fixed calendar supplies its own detailed phase and posterior
proofs. [SchedulerReplayLaw](../Vegas/EventGraph/SchedulerReplayLaw.lean) handles
deterministic public event scheduling, not this stochastic assessment adapter.

The smallest useful new formal work is therefore:

1. A protocol-history serialization/erasure interface for bounded public phases,
   with primitive wait/logical-step clauses and source-public prefix recovery.
2. An induction deriving scheduler-likelihood constancy and proportional
   information-history reach weights for every lifted source profile. This
   must start from primitive kernels, not posterior equality.
3. An induction deriving erased terminal continuation laws, including a local
   action replacement at each cloned source site.
4. A preservation theorem using source consistency sequences and the existing
   Bayes/local-optimality APIs. No equilibrium existence or local optimality at
   copied sites should appear as new backend hypotheses.

All four remain unimplemented for the general public constructor. The paper
proof above specifies their mathematics; it is not a claim of checked evidence.

The next formal lemma can be made particularly concrete. Build the expanded
protocol with state consisting of a source `ExecutionProtocol.History`, the
public auxiliary transcript, a waiting/ready flag, and a finite remaining
budget. Waiting states have no active players and require the joint empty
action. Their step draws from K, appends its public token, and either reduces
the budget or changes the flag to ready. A ready state's legal joint actions
and step are the source protocol's legal joint actions and step. Its supported
successor extends the stored source history by that actual source transition,
then resets the waiting budget. A source terminal history terminates immediately.
The expanded information model reads source information from the stored history
and pairs it with the public transcript. This uses the existing protocol and
history carriers; it requires no new equilibrium concept.

For this constructor the first substantive adapter theorem is, for **every**
source behavioral profile rho and **every** legal expanded history x,

\[
 w_{\mathrm{expanded}}(\operatorname{lift}\rho,x)
   =w_{\mathrm{source}}(\rho,\pi x)\,L(\pi x,\tau x).
\]

The multiplier is the explicit product of K's primitive probabilities, not an
existential posterior multiplier. The existing
[ReachBounds](../GameTheoryExtensions/Analysis/Protocol/ReachBounds.lean)
`historyReachWeight_eq_prior_mul` supplies the predecessor recursion. Wait and
ready clauses give its two induction cases. History serialization and public
prefix recovery then give the proportional fiber sums used by
`bayesBelief_projection_of_proportional_reach`. The separate next lemma erases
terminal continuations from any ready history after an arbitrary local lottery,
with all future choices copied from rho. Together these are the missing
noncircular source-information/execution adapter.

## Connecting the construction to messages and protected admission

The construction permits visible pending existence, clocks, lengths, fees, and
sender identities when their laws depend only on the public source prefix and
public auxiliary history. It does not require physical packets to disappear
from observers' views. A concrete refinement must account for every observed
field. A fixed-size encrypted packet can realize a source-private action under
an ideal secrecy model; actual cryptography requires a computational refinement.
Visible fee data must satisfy this information condition; fees actually charged
to players must also satisfy the payoff correspondence above.

Source-private own inputs already belong to I and are allowed. Additional
private handle aliases, encryption coins, and owner-only receipts are not
automatically part of this purely public scheduling constructor. A concrete
refinement must normalize them away without losing recall, or establish their
own observation-local ancillary law. The existing `ObservedChoice` and
conditional-observation APIs help with such an extension; the public-clock
argument alone does not discharge it.

A protected admission window can realize the logical-step clause if a selected
source response is irrevocably admitted and accepted before its deadline.
Deliberate withholding can realize an available source failure action. An
unrequested admission failure is allowed only if it is already a branch of
the selected source action's transition, with the same law and observations;
merely having some other source failure action does not justify a dropped send.
The application
must supply no intervening utility-affecting owned decision during transport.
Unowned callbacks and public delay draws are allowed. Payloads can become
public only when the resulting information is present in the source view at
the next player decision. Rejected openings need particular care: a source
failure that hides a value is not implemented by publicly exposing that value
in a rejected plaintext transaction.

This is an application-level service obligation. Ordinary liveness does not
give guaranteed admission before the deadline. Threshold encryption or a TEE
does not, by itself, establish source-compatible metadata or scheduling.
Owner-independent release still needs transmission, publication, and available
service funds. Stochastic duration must fit the physical budget for the logical
step. These obligations can be enforced by a reserved-admission service whose
execution times vary publicly; they do not describe an arbitrary public mempool.

The raw runtime can retain additional sends, silence, replacements, and fee
bids. First prove the public scheduling theorem for a retained protocol that
realizes the construction, then embed that protocol into the raw runtime using
the existing
[PassageRestrictionExtension](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean).
Extra raw actions need the existing continuation/comparator domination premise
to be derived from actual conditional incremental costs or another mechanism.
This requirement is separate from the scheduling information adapter.

The retained protocol is the *decorated* source game. Restricting the original
source game directly into the raw runtime generally cannot account for one
source information set having many random-clock copies. Nor can
[PrescribedCompletion](../GameTheoryExtensions/Analysis/Protocol/PrescribedCompletion.lean)
alone repair this gap: it preserves prescribed strategies and makes free sites
rational, but provides no copied-site belief or incentive transport.
[ComponentCompletion](../GameTheoryExtensions/Analysis/Protocol/ComponentCompletion.lean)
provides consistent mixtures and pooled best responses. Common weights require
separate memberwise rationality; source-private leakage does not become
ancillary by placing sites in a pool.

## Boundaries of the positive claim

A publicly visible delay can reveal a private bit if its primitive kernel
depends on that bit. Even if every message is admitted with certainty, a later
guessing player learns additional source-private information. This violates
public prefix recoverability/kernel locality and can change its uniquely best
response. Admission protection cannot compensate for that information leak.

Source-public scheduling also does not cover arbitrary order changes. Reordering
two source choices can move an observation across a decision or change which
actions a player remembers. Commutation of final stores alone does not preserve
conditional information or incentives. Here the logical order is preserved;
physical durations and public auxiliary results may vary.

Player-controlled packet timing is not a chance-only stutter. Its probabilities
can depend on private information and on trembles, so the scheduler likelihood
need not cancel. Likewise, any additional owned decision during a transport
phase needs its own incentive argument. The construction does not declare
these choices harmless, and the raw extension remains conditional until their
operational comparison bounds are checked.

The resulting opportunity is substantial but specific: exact SE preservation
under a broad class of bounded, public, adaptive delays is mathematically
available without exposing runtime clocks in the source language. Proving a
real backend realizes the retained information/execution constructor, and
enforcing departures from it, remains the compiler work.
