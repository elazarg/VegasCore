# Sequential equilibrium under ideal sanctions

## Claim and status

There is a general finite-game route from an abstract game to a larger game
with forbidden actions: retain the original information on compliant paths,
make each first departure sufficiently costly, and complete the new decisions
rationally. This note gives the mathematical proof of **forward extension of
every source sequential equilibrium (SE)**. The general legal-comparator theorem
and its range/collection corollary are checked in
[RestrictionExtension.lean](../../GameTheoryExtensions/Analysis/Protocol/RestrictionExtension.lean)
for finite, clocked perfect-recall execution protocols with an adequate horizon.
The [actual native guessing instance](se-native-pilot.md) is also checked by a
direct continuation proof; it does not establish these structural premises for
arbitrary source programs.

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
\(c_i\) in `[0,1]` gives net payoff `u_i - D_i c_i`. A binary indicator means a
one-time collectible fine; a fractional indicator can represent its expected
terminal collection when that collection introduces no further observations.
Assume:

1. **Soundness:** `c_i = 0` at every fully compliant terminal history, for every
   player. This covers all source strategies and deviations using retained
   actions, not just one prescribed equilibrium.
2. **Uniform first-departure collection:** from every compliant history `h`
   owned by `i`, each forbidden action has conditional expected \(c_i\) at least
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
`(sigma,mu)` and a completely mixed sequence \(sigma_n\) witnessing its
consistency. At every retained target set `I`, let \(k_I\) be its number of
forbidden actions. Assign each forbidden action probability \(delta_n\) and each
retained action `a` probability `(1-k_I delta_n) sigma_n(a|I)`.

All compliant histories have positive reach under \(sigma_n\). Let `r_n > 0`
be their minimum reach, and choose positive \(delta_n\) tending to zero with
`delta_n/r_n -> 0` and `k_I delta_n < 1`. For example, a sufficiently small
constant times `r_n/(n+1)` works. This choice depends on the source consistency
sequence, not on any new-site completion. It does not alter the target game.

**2. Complete all new decisions simultaneously.** For each `n`, put one
normal-form agent at each new information set. Its payoff is its owner's
unconditional expected *net* payoff in `T_D`. An agent chooses a distribution
\(x_I\); its actual local behavior is `(1-epsilon_n)x_I + epsilon_n uniform_I`,
where `0 < epsilon_n -> 0`. Retained-site behavior remains pinned as in step 1.
This is a finite game (equivalently take the local pure actions and mix), so it
has a mixed Nash equilibrium. Use one to define \(beta_n\).

Every \(beta_n\) is completely mixed. At a new set `I`, its positive reach is
independent of its local agent's action: perfect recall precludes revisiting
`I`. Changing that agent changes payoffs only after reaching `I`. Divide its
unconditional best-response comparison by this positive reach **before**
taking a limit. The actions used by \(x_I\) maximize conditional continuation
payoff. Consequently \(beta_n\) has one-step conditional regret at most
`epsilon_n (U_i-L_i+D_i)` there. The new sets need not form a closed region;
subsequent retained-site behavior is simply fixed in these continuation payoffs.

**3. Show that old beliefs survive, including at off-path source sets.** Fix a
retained set `I`. On each compliant history, target reach is source reach times
a product of factors `1-k_J delta_n`. There are only finitely many factors,
so these multipliers tend uniformly to 1. Conditional on `I intersect C`, the
target Bayes belief therefore has the same limit as the source belief, namely
\(mu_I\).

Every noncompliant history reaching `I` contains a first forbidden action at a
retained set. Its probability has a factor \(delta_n\). A finite union bound
bounds all such reach by `K delta_n`, independently of the new agents' chosen
equilibrium. Compliant reach in `I` is at least \(r_n\) times a product tending
to 1. Thus noncompliant reach divided by compliant reach tends to zero.
Conditioning on all of `I` has the same limit as conditioning on `I intersect C`.
No positive lower bound on the *limiting* reach of `I` is needed.

**4. Take one common assessment limit.** Finite products of strategy and belief
simplices are compact. Extract a single subsequence on which \(beta_n\) and its
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

## A finite certificate for inferring sanctions

Uniform positive collection is sufficient, but an extra action that is already
unprofitable needs no collection. The following certificate gives a sharper
version of the extension theorem. Its mathematical argument is given here;
the finite execution extraction and the composed Lean theorem remain open.

Keep the finite action restriction and perfect-recall hypotheses. Fix
nonnegative terminal charge features `C_ij(z)` and net utility
`u_i(z) - sum_j d_j C_ij(z)`, with `d_j >= 0`. All features vanish on every
compliant terminal history. Features describe actual collectible consequences
in the game; they are fixed independently of deposit amounts. Reports and
collection observations that affect later play remain in the execution tree.

For each retained information set `I` of player `i`, forbidden action `a`,
compliant history `h` in `I`, and pure future policy table `tau`, compute:

- `B(h,a,tau)`: expected base utility after choosing `a` at `h`.
- `L(h,b,tau)`: expected base utility after legal action `b` at `h`.
- `c_j(h,a,tau)`: expected charge feature after choosing `a` at `h`.

The table chooses one action per information set, legal at retained sets and
unrestricted at new sets. The bad and legal runs use the **same** table. All
expectations use the actual chance and service laws. For each pair `(I,a)`,
choose one lottery `lambda_(I,a)` over legal source actions and require

```text
B(h,a,tau) - sum_b lambda_(I,a)(b) L(h,b,tau)
  <= sum_j c_j(h,a,tau) d_j
```

for every `h` and `tau`. The lottery must be shared across every such row. A
different comparator chosen using a hidden history or the future policies of
other players would not be a source action available to the player.

**Certificate theorem.** Feasible deposits and comparator lotteries give the
same forward SE-extension and joint-law conclusions as the theorem above.

**Proof.** Construct the common consistent completion as in steps 1--4, using
the finite range of the resulting net utility for each player's regret bound.
At a retained set its belief is supported on compliant histories, its retained
behavior is the source strategy, and its future behavior is legal at retained
sets. Independently predraw one action from each future local behavioral law.
Perfect recall ensures no information set is visited twice along a play, so
each finite path has the same product probability as behavioral execution.
Thus these draws realize both the bad and legal continuation laws as mixtures
over the same pure tables. Average the displayed inequalities over this table
distribution and the retained belief. Action `a` has net value no greater than
the legal deviation that plays `lambda_(I,a)` now and follows the source
strategy thereafter. That deviation is bounded by the source SE's prescribed
value. Retained actions inherit source rationality, and new sets have optimal
local responses from the completion. The consistent one-shot principle and
zero charges on compliant play finish steps 5--6. Equality suffices. Deposits
and comparators are fixed before quantifying over source equilibria. This proof
does not produce a fixed playerwise compiler. End of proof.

With fixed rational execution coefficients, this is a finite linear feasibility
problem in `d` and `lambda`: lawful zero charges avoid a product of lottery and
deposit variables. Jointly synthesizing detection probabilities and deposits
generally introduces products and is a different optimization problem.
A linear objective can minimize total collateral or a common
deposit. The range/detection certificate follows by bounding all bad base values
above, all legal values below, and bad collection below. The finite certificate
instead keeps gain and collection from the same execution together.

For a fixed scalar comparison family `g_k <= c_k D`, with `c_k >= 0`, feasibility
requires `g_k <= 0` whenever `c_k = 0`. Subject to those tests, the least weakly
deterring nonnegative deposit is the maximum of zero and `g_k/c_k` over positive
coefficients. Division by positive coefficients proves both directions; an empty
family of positive coefficients needs only zero. A strict guarantee should use
an explicit positive margin rather than claim this boundary value is strict.

If `q_k >= 0`, `g_k <= q_k G` and `c_k >= alpha q_k` for one `alpha > 0`, then
`D >= G/alpha` and `D >= 0` imply all comparisons, by multiplication and
transitivity. Taking \(q_k\) to be leak probability requires a proof that failed
leakage has no other beneficial effect; silence and timing can themselves carry
information. No independence between leakage and collection is used.

Certificate infeasibility is not an impossibility result: the rows include
irrational completions and histories assigned zero belief by some source SEs.
Conversely, a strategic reporter allowed to stay silent produces zero-collection
rows. The certificate cannot assume that reporter away; a reporting-equilibrium
proof or an explicit mechanical collection primitive is needed. Monetary
amounts implement these utility inequalities only under a stated utility model.

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

## Checked proof and native boundary

The formal proof follows five obligations; none assumes a target equilibrium.

1. [ActionRestriction.lean](../../GameTheoryExtensions/Protocol/ActionRestriction.lean)
   embeds histories, information and choices, with one local execution square.
   [RestrictionExecution.lean](../../GameTheoryExtensions/Protocol/RestrictionExecution.lean)
   derives every continuation and initialized execution law from that square.
2. [RestrictionDomination.lean](../../GameTheoryExtensions/Protocol/RestrictionDomination.lean)
   propagates the retained fraction of each local choice through actual execution.
   With tremble rate `epsilon`, source history mass at depth `d` survives with
   factor `(1-epsilon)^(numberOfPlayers*d)`, whatever happens after departure.
3. [RestrictionBeliefs.lean](../../GameTheoryExtensions/Analysis/Protocol/RestrictionBeliefs.lean)
   derives retained Bayes beliefs from that mass bound.
   [RelativeTremble.lean](../../GameTheoryExtensions/Math/Probability/RelativeTremble.lean)
   chooses a rate negligible relative to all source information-set reach masses.
   [RestrictionCompletion.lean](../../GameTheoryExtensions/Analysis/Protocol/RestrictionCompletion.lean)
   then constructs one consistent extension with all new decisions locally optimal,
   using the common information-agent completion.
4. [RestrictionIncentives.lean](../../GameTheoryExtensions/Analysis/Protocol/RestrictionIncentives.lean)
   transports source-legal deviations and bounds actual forbidden continuations
   by fixed legal comparator lotteries. It does not require detecting harmless
   added actions. The comparison is pointwise in hidden history and covers
   arbitrary paired continuation profiles, without assuming their rationality.
   [SequentialOneShot.lean](../../GameTheoryExtensions/Analysis/Protocol/SequentialOneShot.lean)
   converts consistent local optimality into whole-policy sequential rationality.
5. [RestrictionExtension.lean](../../GameTheoryExtensions/Analysis/Protocol/RestrictionExtension.lean)
   composes these facts into SE extension, exact retained behavior and beliefs,
   and a joint completed-history/net-payoff law. Its bounded-horizon premise
   proves the returned execution laws are terminal laws.

[RestrictionEnforcement.lean](../../GameTheoryExtensionsTests/RestrictionEnforcement.lean)
checks a nonvacuous two-player instance of this capstone. Alice's additional
action creates a new Bob decision; Bob prefers a response that also benefits
Alice. A deposit of one preserves every source SE and the exact zero-payoff
law. The fixture proves actual collection, finite play, perfect recall, clock
alignment, structural correspondence and source equilibrium existence.

[EnforcementSynthesis.lean](../../GameTheoryExtensions/Analysis/EnforcementSynthesis.lean)
implements the scalar finite-table calculation, including minimality among real
deposits and an infeasible-row witness. The SE theorem accepts legal comparator
lotteries and their actual continuation inequalities. Generic extraction of
finite pure-profile rows and synthesis of those lotteries remain unimplemented;
the finite linear reduction is proved mathematically above. No general optimizer
or exact SE decision procedure is implemented.

The structural correspondence preserves active players and step counts. The
target's common-depth information sets are an additional restriction beyond
boundedness and perfect recall. Thus an arbitrary native service calendar does
not automatically instantiate the theorem. A compiler must align forced steps
or prove their elimination preserves observations and decisions. Source and
target chance behavior on compliant histories must also satisfy the local square.

The uniform collection certificate covers arbitrary continuation policies.
A strategic watcher with a legal option to remain silent need not satisfy it.
The native pilot instead proves rational reporting and receiver completion
directly; an automated collection backend or a more selective completion proof
would discharge a different contract. Finite rational bounds alone do not prove
attribution, reporting or collectibility. Native conformance and the operational
limits above remain the decisive compiler obligations.

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
