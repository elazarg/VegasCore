# Sequential equilibrium under ideal sanctions

## Claim and status

There is a general finite-game route from an abstract game to a larger game
with forbidden actions: retain the original information on compliant paths,
make each first departure sufficiently costly, and complete the new decisions
rationally. This note gives a mathematical proof of **forward extension of
every source sequential equilibrium (SE)**. The general theorem is not yet
formalized in Lean. The [actual native guessing instance](se-native-pilot.md)
is checked; it does not establish the general structural premises below.

The target game and fines are fixed before choosing a source equilibrium:

\[
  \forall(\sigma,\mu)\in SE(S),\quad
  \exists(\beta,\nu)\in SE(T_D)
\]

such that the initialized terminal law, including net payoffs, is unchanged.
The target assessment extends the source assessment on retained information
sets. This is stronger than matching expected payoffs. It neither rules out
additional target equilibria nor supplies a fixed playerwise strategy compiler:
the completion at new information sets may depend on the whole source assessment.

## A sufficient structural theorem

Let `T` be a finite extensive-form game with perfect recall. Nature's
probabilities are fixed. Remove histories requiring a zero-probability chance
move, so every remaining history has positive probability under completely
mixed behavioral strategies. Initial private types are part of nature's play.

Let `S` be a **genuine action restriction** of `T`. At each information set
meeting the compliant tree `C`, retain a nonempty set of actions, uniformly
across that information set. Keep their successors and every chance successor;
delete the other action branches. Source information sets are intersections
of target information sets with `C`. Chance probabilities and base terminal
payoffs are unchanged. Call a target information set *retained* if it meets `C`,
and *new* otherwise. A retained set may also contain noncompliant histories.
Every first exit from `C` is therefore a forbidden action at a retained set.

For player `i`, let base payoffs lie in `[L_i,U_i]`. A terminal charge indicator
`c_i` in `[0,1]` gives net payoff `u_i - D_i c_i`. A binary indicator means a
one-time collectible fine; a fractional indicator can represent its expected
terminal collection when that collection introduces no further observations.
Assume:

1. **Soundness:** `c_i = 0` at every fully compliant terminal history, for every
   player. This covers all source strategies and deviations using retained
   actions, not just one prescribed equilibrium.
2. **Uniform first-departure collection:** from every compliant history `h`
   owned by `i`, each forbidden action has conditional expected `c_i` at least
   `p_i > 0`, under every subsequent continuation profile. The bound applies
   separately at each history and action; averaging gives it under every belief
   on the compliant portion of that information set.
3. **Finite sufficient fines:** `D_i >= 0` and
   `p_i D_i > U_i - L_i`.

**Theorem.** Every SE of `S` extends to an SE of `T_D`, preserving its source
behavior and beliefs at retained sets, its initialized terminal law, and its
net-payoff law. The weak inequality `p_i D_i >= U_i-L_i` also suffices for forward
extension; strict inequality additionally makes current forbidden actions
strictly worse at retained sets in the constructed equilibrium.

This is an ideal enforcement benchmark. An automatic monitor and terminal
collection rule can satisfy premise 2 mechanically. A strategic watchdog that
may decline to report generally cannot satisfy a bound uniform over all its
policies. Replacing the mechanical primitive by an optimally participating
watchdog requires a separate equilibrium argument and conditional collection
bound; passive observation probability alone is insufficient.

## Proof

**1. Preserve the prescribed source trembles.** Fix a source assessment
`(sigma,mu)` and a completely mixed sequence `sigma_n` witnessing its
consistency. At every retained target set `I`, let `k_I` be its number of
forbidden actions. Assign each forbidden action probability `delta_n` and each
retained action `a` probability `(1-k_I delta_n) sigma_n(a|I)`.

All compliant histories have positive reach under `sigma_n`. Let `r_n > 0`
be their minimum reach, and choose positive `delta_n` tending to zero with
`delta_n/r_n -> 0` and `k_I delta_n < 1`. For example, a sufficiently small
constant times `r_n/(n+1)` works. This choice depends on the source consistency
sequence, not on any new-site completion. It does not alter the target game.

**2. Complete all new decisions simultaneously.** For each `n`, put one
normal-form agent at each new information set. Its payoff is its owner's
unconditional expected *net* payoff in `T_D`. An agent chooses a distribution
`x_I`; its actual local behavior is `(1-epsilon_n)x_I + epsilon_n uniform_I`,
where `0 < epsilon_n -> 0`. Retained-site behavior remains pinned as in step 1.
This is a finite game (equivalently take the local pure actions and mix), so it
has a mixed Nash equilibrium. Use one to define `beta_n`.

Every `beta_n` is completely mixed. At a new set `I`, its positive reach is
independent of its local agent's action: perfect recall precludes revisiting
`I`. Changing that agent changes payoffs only after reaching `I`. Divide its
unconditional best-response comparison by this positive reach **before**
taking a limit. The actions used by `x_I` maximize conditional continuation
payoff. Consequently `beta_n` has one-step conditional regret at most
`epsilon_n (U_i-L_i+D_i)` there. The new sets need not form a closed region;
subsequent retained-site behavior is simply fixed in these continuation payoffs.

**3. Show that old beliefs survive, including at off-path source sets.** Fix a
retained set `I`. On each compliant history, target reach is source reach times
a product of factors `1-k_J delta_n`. There are only finitely many factors,
so these multipliers tend uniformly to 1. Conditional on `I intersect C`, the
target Bayes belief therefore has the same limit as the source belief, namely
`mu_I`.

Every noncompliant history reaching `I` contains a first forbidden action at a
retained set. Its probability has a factor `delta_n`. A finite union bound
bounds all such reach by `K delta_n`, independently of the new agents' chosen
equilibrium. Compliant reach in `I` is at least `r_n` times a product tending
to 1. Thus noncompliant reach divided by compliant reach tends to zero.
Conditioning on all of `I` has the same limit as conditioning on `I intersect C`.
No positive lower bound on the *limiting* reach of `I` is needed.

**4. Take one common assessment limit.** Finite products of strategy and belief
simplices are compact. Extract a single subsequence on which `beta_n` and its
Bayes beliefs converge to `(beta,nu)`. This is a consistent target assessment.
At every retained set its strategy is `sigma`, and its belief is `mu` extended
by zero on noncompliant histories. At every new set, step 2 and continuity of
finite conditional continuation values give one-step optimality in the limit.

**5. Prove retained-site rationality.** At a retained set, beliefs assign total
mass to compliant histories. Forcing a retained action and then following
`beta` stays compliant, incurs no fine, and gives exactly the source
continuation value. Source sequential rationality therefore orders all retained
actions correctly, with prescribed value at least `L_i`. A current forbidden
action followed by `beta` gives at most `U_i-p_i D_i < L_i`, by premise 2.
It cannot improve payoff. With weak threshold it is merely weakly worse.

It is unnecessary for the pinned source trembles to be best replies at finite
`n`: retained-site optimality was proved at the limit using the prescribed
source assessment. The finite perfect-recall one-shot-deviation principle,
applied to the consistent limit assessment, promotes one-step optimality at
all sets to optimality against every continuation strategy.

**6. Preserve the law.** Starting from the common initial chance law, `beta`
never leaves `C` and follows `sigma` there. Terminal distributions coincide,
and all charges vanish. Any common observation of those terminals, including
initial types, public results and the entire net-payoff vector, has equal law.

## Why the qualifications matter

- **A sunk charge is not a fresh incentive.** A one-time fine may become
  unavoidable on a new branch. The proof allows rational behavior there; it
  does not require continued compliance. Retained-site limiting beliefs put
  zero weight on such branches. Perfect recall also distinguishes a player's
  own forbidden past from its own compliant past.
- **Vanishing is not rare enough.** If a compliant information event has mass
  `epsilon^2` but the extra histories entering it have mass `epsilon`, its
  posterior is dominated by the extra histories. The relative-rate construction
  is essential precisely at zero-probability source information sets.
- **Large fines do not give reflection.** The existing
  [dominated-action example](../sequential-enforcement-design.md) adds a costly
  action into an old off-path receiver set. If its trembles dominate the old
  path, they can support extra target SE outcomes for every fine. The theorem
  selects a consistency sequence preserving the source beliefs; it does not
  constrain every target consistency sequence.
- **Finite fines require a conditional gain/detection comparison.** Zero
  detection with a profitable violation defeats every fine. Without a uniform
  ratio bound, even positive detection at every comparison need not suffice:
  gains 1 and collection probabilities `1/(n+1)` require unbounded fines.
  Scaling unrestricted utilities likewise defeats a fixed fine. In the finite
  benchmark, the bounds and game-wide fines are chosen before quantifying over
  all source SEs, not separately for each equilibrium.
- **Literal minus infinity is a different model.** Completely mixed trembles
  assign positive probability to forbidden play; infinite charges can make
  expected utilities minus infinity and collapse continuation comparisons after
  sure collection. Lexicographic avoidance of sanctions is also a different
  preference model. Bounded real utilities and finite fines already prove the
  stated standard-SE result.
- **The action-restriction premise is substantive.** It does not justify
  erasing timing observations, changing inclusion probabilities, merging source
  information, or admitting unmonitored signaling through legal fields. Those
  changes require their own semantic correspondence. This theorem concerns
  unilateral SE deviations, not correlated equilibria or coalition robustness.

### Forcing failure is a payoff-dependent alternative

If detection occurs with probability `p`, the actual caught continuation has
value `f`, the missed continuation has value `m`, and compliance has value `v`,
deterrence holds exactly when `m-v <= p(m-f)`. This criterion is checked as
`failure_deterrence_iff` in
[FailureEnforcement.lean](../../GameTheoryExtensions/Analysis/FailureEnforcement.lean).
Certain detection suffices exactly when `f <= v`; a result named failure need
not be a utility loss. Partial detection cannot deter a strictly profitable
missed continuation when failure is at least as good as compliance.

[ForcedFailureEnforcement.lean](../../GameTheoryExtensionsTests/ForcedFailureEnforcement.lean)
uses the existing disclosure protocol to prove a stronger concrete limitation
of excluding only the discloser: that player has no remaining source decisions,
yet disclosure prevents implementation of the fair source SE law. Exclusion
cannot revoke information already held by the receiver. This does not refute
global abort or a suitable low-valued failure continuation; those mechanisms
must satisfy the displayed value comparison. Its second example also checks
that abort can reward a deviation by avoiding a costly obligation. Conversely,
the four-unit failed-opening loss in the guessing example suffices at detection
probability one half, with a missed-deviation payoff at most one and lawful value
at least zero. The numerical comparison is checked; a service actually forcing
that failure has not been implemented.

### Operational boundary in the current commitment runtime

Omitting unopenable commitments from the source does not make them detectably
nonconforming. [EventBindingAction.lean](../../Vegas/Pending/EventBindingAction.lean)
uses the same opaque commitment packet for a value and forfeiture; supplied
opening material is private. The actual handler in
[EventApplication.lean](../../Vegas/Pending/EventApplication.lean) can accept
either, storing a hidden binding success or failure. This differs from a
syntactically `.malformed` call, which it rejects. The checked
`playerStore_foreign_binding` and `publicStore_binding` laws in
[Information.lean](../../Vegas/EventGraph/Information.lean) hide that binding
result from foreign players and the public observer. Later withholding is
source-legal and yields publication failure for either binding. Thus packet
shape, acceptance and eventual failure do not supply the uniform collection
premise for an omitted unopenable binding. Inspecting the ideal private catalog
would give the monitor an additional power, absent from ordinary passive reads.
The existing [conformance audit](se-conformance-audit.md) therefore calls for
source forfeiture, a program-specific omission proof, or a separate validity
proof backend; increasing the fine supplies none of these.

Permitted encodings impose a related boundary. The checked support criterion
in [ObservableEnforcement.lean](../../GameTheoryExtensions/Analysis/ObservableEnforcement.lean)
forbids zero-false-positive detection on observations admitted by lawful play.
[MonitoredSignaling.lean](../../GameTheoryExtensionsTests/MonitoredSignaling.lean)
exhibits this with an allowed field and shared private pad, including monitors
of the later public guess. Any source-visible signaling already belongs in
the source game; any additional admitted signaling must be normalized or
otherwise accounted for. Cryptographic randomness is a further refinement
obligation, not a field modeled or controlled by the current ideal catalog.

## Checked ingredients and next proof boundary

[NegligibleContamination.lean](../../GameTheoryExtensions/Math/Probability/NegligibleContamination.lean)
checks `conditional_contamination_bound`: each posterior-coordinate error is
at most contaminating mass divided by compliant mass.
`conditional_contamination_converges_of_bound` turns a vanishing upper/lower
mass ratio into preservation of conditional beliefs, even when compliant
reach tends to zero.
[RelativeConditioning.lean](../../GameTheoryExtensions/Math/Probability/RelativeConditioning.lean)
checks the clean-fiber step: relative point-mass losses bounded by `eta < 1`
change a posterior coordinate by at most `eta/(1-eta)`; uniformly vanishing
relative losses therefore preserve the conditional limit.
[FirstDeparture.lean](../../GameTheoryExtensions/Math/Probability/FirstDeparture.lean)
checks a kernel union bound: if each not-yet-bad state has probability at most
`delta` of departing next, bad mass after `n` steps is at most initial bad mass
plus `n delta`, with unrestricted behavior after departure. A game restriction
must still supply its local first-departure and multiplicative reach bounds.

[ConsistencyCompletion.lean](../../GameTheoryExtensions/Analysis/Protocol/ConsistencyCompletion.lean)
provides common assessment subsequence and preserved-belief machinery.
[ConstrainedNash.lean](../../GameTheoryExtensions/Analysis/ConstrainedNash.lean)
checks existence of jointly optimal residual responses with pinned agents and
mandatory trembles. [AgentForm.lean](../../GameTheoryExtensions/Analysis/Protocol/AgentForm.lean)
identifies mixed information-agent play and local agent updates with execution
and local behavioral updates in the original protocol.
[LocalDeviation.lean](../../GameTheoryExtensions/Analysis/Protocol/LocalDeviation.lean)
checks the positive-reach cancellation between root and Bayes continuation
comparisons, with explicit perfect recall and common-depth premises.
[AgentCompletionLimit.lean](../../GameTheoryExtensions/Analysis/Protocol/AgentCompletionLimit.lean)
constructs one consistent assessment with jointly optimal local responses at
all free information sites. Its exact approximating sequence remains available
for proving source belief and strategy preservation.

[SequentialOneShot.lean](../../GameTheoryExtensions/Analysis/Protocol/SequentialOneShot.lean)
checks that local optimality in a consistent assessment implies actual
whole-policy sequential rationality for finite perfect-recall protocols with
common-depth information sets. The quantitative intermediate theorem bounds
whole-policy gain by remaining horizon times local regret. It retains and then
cancels the starting site's reach mass, so the estimate stays uniform at rare
information sets. These are operational law and incentive facts, without an
assumed target-optimal assessment.

[SequentialExistence.lean](../../GameTheoryExtensions/Analysis/Protocol/SequentialExistence.lean)
composes the construction with all information agents free, proving standard SE
existence for that finite clocked protocol class and its stated remaining-horizon
contexts. A terminal-payoff interpretation additionally needs enough evaluation
fuel to complete play. Existence alone does not establish compilation preservation.

[EnforcementLimits.lean](../../GameTheoryExtensions/Analysis/EnforcementLimits.lean)
characterizes finite families of comparisons admitting all sufficiently large
fines, and records the failure of a uniform bound for shrinking detection.
The remaining general formalization is the action-restriction adapter: derive
compliant-history reach bounds, retained belief and strategy transport, permitted
continuation laws and first-departure incentive bounds from structural embeddings
between the existing source and target protocols. A narrower information menu
alone is invalid: execution legality and the resulting history space must agree.
Forced administrative steps require their own observation-preserving elimination.
Native conformance and collectible monitoring remain further runtime obligations.

## Primary literature

[Myerson and Reny, author version of 2 December 2019, Theorem 6.4](https://home.uchicago.edu/~rmyerson/research/seqm.pdf)
characterize SE strategy profiles in standard finite games through vanishing
conditional approximation. This supports taking conditional incentive limits;
it does not itself establish the compiler or collection premises here.

[Dilmé, updated 21 February 2024, Proposition 2.1 and §4.1](https://www.econtribute.de/RePEc/ajk/ajkdps/ECONtribute_254_2023.pdf)
relates sequential outcomes to vanishing perturbed approximate equilibria and
uses relative tremble rates in action-elimination arguments. His elimination
result concerns sequentially stable outcomes; it must not be quoted as the
ordinary-SE extension theorem proved above. The construction here pins a
specified source assessment and only optimizes the newly available decisions.
