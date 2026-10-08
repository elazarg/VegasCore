# How close we are to general sequential-equilibrium preservation

Analysis by Codex, with independent mathematical investigations of enforcement,
belief transport, and information leakage. The strongest useful result is a
composition: preserve the source game through a faithful runtime service, then
extend its equilibria to the raw runtime by deterring departures from that
service. The enforcement part is checked in general finite protocols. The
source-to-service part is checked for the calendar and has a paper proof for
bounded public stochastic scheduling. A general blockchain compiler theorem
still needs the operational adapters between those parts.

This analysis does not change the target, boxes, or semantics in the
[asynchronous checklist](se-async-checklist.md).

| Result | Status | Limit |
| --- | --- | --- |
| One finite deposit vector extends every source SE through a structural restriction | Checked | Requires clean matching and uniform actual collection after excluded actions |
| Positive collection for every finite pure plan gives a uniform mixture bound | Checked | Behavioral protocol realization and pure-plan positivity remain to be supplied |
| Bounded public stochastic scheduling preserves every source SE | Paper proof | General protocol constructor and its two inductions are not mechanized |
| Honest off-path disclosure can prevent SE and weak-PBE preservation while allowing Nash preservation | Paper proof | Fully specified finite game, not yet a library protocol instantiation |
| A profitable comparison is finitely punishable by a sound transcript audit iff it has positive mass outside clean transcripts | Checked | One comparison and a fixed evidence interface |
| Arbitrary-source weak-PBE preservation through a clean restriction | Paper proof | Requires finite perfect recall and a separate completion/repair construction |
| A general public-mempool compiler theorem | Open | Its source-information and collection adapters are not supplied |

## The checked general enforcement theorem

Let H be a retained finite protocol, R a finite raw protocol, and r a structural
action restriction from H into R. This can be supplied by the existing
[menu restriction](../GameTheoryExtensions/Protocol/MenuRestriction.lean): it
preserves retained transitions, information histories, and choices, while R
may offer additional actions and new decision sites. Let u_i be source utility,
b_i raw base utility, and a_i(t) the probability of actually collecting player
i's escrow after terminal history t. The audit observes an admissible final
transcript and can randomize its verdict; it is a settlement service.

The following sufficient conditions are operationally meaningful:

1. Every retained history matches source base utility and is audit-clean:
   b_i(r(h)) = u_i(h) and a_i(r(h)) = 0. This covers all retained histories,
   including legitimate deviations from a particular source equilibrium.
2. There are finite bounds L_i <= u_i(h) and b_i(t) <= U_i.
3. After committing any excluded action at any retained decision, from every
   hidden retained history in that information set, every remaining raw
   continuation gives collection probability at least rho_i > 0.
4. Source decisions form a decision-information antichain, the raw protocol has
   decision recall, and the legal history carriers are finite. Ordinary fallback
   policies supply the nonempty action choices.

Then one finite deposit vector, chosen before the source equilibrium, works:

\[
 D_i=\max\{0,(U_i-L_i)/\rho_i\}.
\]

For **every** SE of H there is an SE of R extending its retained strategy and
beliefs, with exactly the embedded terminal-history law and the joint law of
terminal history and realized settlement payoffs. Initialized equilibrium play
collects no deposits. This is forward preservation; it does not reflect every
raw equilibrium back to H.

Both the no-clock audit extension and the finite-deposit capstone are checked
in [TerminalAudit](../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean),
as `sequential_equilibrium_extends_of_terminal_audit` and
`exists_deposits_preserving_sequential_equilibria`. The latter constructs its
fully mixed reference internally, using the existing finite-game perturbation
machinery. No common-depth calendar is required.

The proof is direct at retained decisions. An excluded action has expected net
payoff at most U_i-rho_i D_i <= L_i, while a retained continuation has payoff at
least L_i. The existing consistent completion then optimizes all new raw
decision sites. It does not demand continued compliance after a penalty becomes
sunk. The first departure from retained play is compared against arbitrary
future behavior; later dirty behavior is rationally completed.

This distinction matters. A previously charged player at a new dirty site is
not a counterexample to the theorem. Counting an already inevitable charge as
an additional cost at a retained comparison would invalidate its premises.

## What finiteness contributes to the collection bound

For a finite nonempty set of complete deterministic continuation plans P,
let c(p) be expected actual collection under plan p. If c(p)>0 for every p,
then

\[
 \rho=\min_{p\in P}c(p)>0,\qquad
 \mathbb E_{p\sim\lambda}c(p)\ge\rho
\]

for every distribution lambda over complete plans, including correlated joint
plans. This is checked in
[PositiveCollection](../GameTheoryExtensions/Analysis/PositiveCollection.lean).
Its game-form corollary supplies a uniform bound over all mixed profiles.
The finite-minimum order lemma lives in
[FinitePayoffBounds](../GameTheoryExtensions/Analysis/FinitePayoffBounds.lean).

To use it for a runtime, prove that every behavioral continuation has such a
pure-plan mixture realization and that collection is positive for every pure
plan from every relevant retained hidden history. The new mixture theorem
does not itself prove this protocol realization. Finitely many retained
histories, excluded choices, and players then allow a common minimum.
Here plans are observation-local contingent policies, with the same information
constraints as the player. Sampling their choices in advance must preserve
the behavioral execution law; decision recall supplies the relevant absence
of repeated decisions at one information set.

This validates part of the fixed-horizon intuition: in a genuinely finite
physical model, strictly positive risk for every complete deterministic plan
is enough for a positive uniform bound. A fixed source horizon alone does not
give finite physical plans. Unbounded retries, arbitrarily fine timing, or
unbounded fee choices can leave infimum risk zero even though every particular
plan has positive risk.

For bounded adaptive opportunities, the checked
[survival bounds](../GameTheoryExtensions/Math/Probability/Survival.lean) and
[reactive evaluator adapter](../Interaction/ReactiveSurvival.lean) give another
route. If the relevant charge-avoiding recovery attempts each leave a bad
state with conditional survival probability at least epsilon, and surviving
terminal states collect with probability at least alpha, a physical bound N
gives rho >= alpha*epsilon^N. Independence is unnecessary. The conditional
floor must cover all permitted fees, routing, retries, observations, and
subsequent policies. A recovery path into guaranteed clean execution prevents
using this survival predicate.

Neither argument gives practical capital requirements. The minimum can be
extremely small and the deposit correspondingly large. Utility must include
fees and redistribution, with base payoffs and bounds fixed before the entire
deposit vector. Deposit-dependent redistribution requires separate coupled
bounds, which the checked capstone does not solve. Capital constraints,
participation, strategic auditors, and coalition deviations need additional
models.

## A uniform failure floor is sufficient, not necessary

There is a sharper economic boundary for a fixed family of valid continuation
comparisons, fixed independently of the deposit being selected. Write g(d) for
a deviation's base gain, including fees, and r(d) for its additional collection
probability relative to a lawful comparator.
Assume r(d)>=0. A single finite nonnegative deposit works for this entire family
exactly when

\[
 r(d)=0\implies g(d)\le0,\qquad
 \sup_{d:r(d)>0}\frac{\max\{g(d),0\}}{r(d)}<\infty.
\]

Here bounded supremum means a finite common upper bound; the empty positive-risk
family imposes no bound. The proof is the elementary inequality g(d)<=r(d)D:
necessity divides by positive r, and sufficiency chooses D at least that common
bound and zero. For a finite comparison family this characterization is
covered by the checked
[enforcement limits](../GameTheoryExtensions/Analysis/EnforcementLimits.lean).
The arbitrary-family ratio statement is a paper calculation, not a new Lean
capstone. Applying it to SE still requires the comparisons at retained sites
and an observation-local lawful comparator.

Consequently, late inclusion probabilities approaching one do not alone prove
impossibility. One needs positive net gains whose ratio to additional
collection becomes unbounded, with no other mechanism covering the comparison.
For example, if every plan giving small failure risk requires fees that exceed
its possible benefit, those plans are already unprofitable. If gains vanish
at least proportionally to collection risk, a finite deposit can also suffice
without a uniform positive risk floor. Conversely, risk approaching zero while
net gain stays bounded away from zero rules out a common finite deposit for
that family. An audit with zero additional collection and positive gain fails
even for one comparison.

This is why fee costs and the exact continuation gain must appear in any
chain-level negative corollary. The simpler range/rho capstone deliberately
uses a stronger operational premise to avoid solving these comparisons
separately. The existing localized extension and repair-coupling interfaces
allow sharper bounds when a backend can derive them.

## A source adapter beyond the fixed calendar

The structural restriction above is between protocols at the same execution
granularity. It does not directly connect an abstract source choice to many
runtime waiting steps, or one source information set to several clock copies.
The retained protocol H should therefore be a scheduling expansion of the
source G. This keeps physical timing in the compiler/service semantics.

The [public scheduling construction](public-scheduling-se-preservation.md)
gives a precise positive paper theorem. Expand each logical source step by a
bounded finite sequence of public chance waits. The scheduler may be adaptive
and correlated across phases, but its primitive inputs must depend only on
recoverable source-public history and the public auxiliary transcript. It must
eventually execute the original source action or chance kernel. Logical stage
and relevant public boundary history must be recoverable from source
information. At each expanded decision, information is exactly the source
decision view paired with the public auxiliary transcript. Player menus and
source utilities stay the same; waits add no owned decisions.

Fee neutrality here is a real obligation, not a claim that blockchain execution
is free. A service charging a fixed prepaid amount F_i, independent of every
retained choice, gives the elementary variant with utility u_i-F_i. The same
assessment remains sequentially rational because this constant cancels in all
continuation comparisons; consistency is unchanged. Source outcomes are still
preserved, while realized net payoffs have that explicit fixed shift. This
variant is a paper corollary, not the exact unshifted settlement conclusion of
the checked capstone. Variable action-dependent fees need a separate incentive
argument or inclusion in the source payoff semantics.

At a copied decision J=(I,tau), lifted source trembles give reach weights

\[
 w'_n(h,\tau)=w_n(h)L_I(\tau).
\]

The primitive scheduler likelihood L_I(tau) is constant across hidden histories
h in source information set I. It therefore cancels in Bayes' rule at every
fully mixed index n, including sites whose limiting reach is zero. Erasing a
continuation with one local action replacement also gives exactly the source
continuation law. These two inductions prove consistency and sequential
rationality separately. Together they give an SE lift with the exact erased
outcome/payoff law.

The composition we can aim to formalize is consequently:

\[
 \text{source SE}
 \longrightarrow \text{publicly scheduled retained SE}
 \longrightarrow \text{raw runtime SE}.
\]

The second arrow is checked generically. The first is checked for the current
calendar, and proved on paper for the stated public scheduler constructor.
Its missing general Lean work is history serialization, primitive reach-weight
induction, and erased local-deviation continuation induction. The existing
probability and SE limit APIs should assemble those results; another abstract
theorem assuming desired posterior equality would not close this gap.

This weakens deterministic scheduling substantially. It does not justify
player-controlled timing signals or unrequested failed admission. A source
action with a deterministic transition must retain that transition; a separate
source failure action does not justify randomly replacing a selected success
action by failure. Admission uncertainty can be modeled by an explicit source
chance kernel, but then the source game being preserved is different.

## Necessary boundaries and PBE

On-path information fidelity alone is insufficient. A general adapter must
control information on legitimate off-path continuations too, or prove that
added information leaves the required continuation choices optimal. The
[honest disclosure example](honest-disclosure-preservation-boundary.md) has a
source SE where both sender types choose Out. A legitimate off-path In choice
keeps the bit private in the source but discloses it in the runtime. A receiver
then has a strictly better informed response, which makes the true-bit sender
enter. Every target SE and compatible-belief weak PBE has entry probability
9/20. The source entry probability is zero. A target Nash equilibrium still
implements Out. This complete two-player example is a paper proof, with exact
consistency witnesses and a quantitative outcome gap.

Thus weakening SE to weak PBE cannot generally repair this information defect.
Weak PBE here means sequential rationality and Bayes updating at reached
information sets, with beliefs supported on the information set elsewhere.
It need not have an SE consistency sequence. Other uses of PBE impose further
belief conditions; a preservation result should name its definition explicitly.

The checked late-leak
[weak-PBE positive result](../Vegas/Examples/LateLeak/CalibratedPenaltyPreservation.lean)
is specific to that finite family and its cost inequalities. General source
weak-PBE preservation has not been established by the new SE capstone: an
arbitrary source weak PBE need not satisfy its consistency premise. Conversely,
the SE capstone does give a target weak PBE for every source SE, since its
target assessment is an SE.

There is now a separate
[weak-PBE restriction preservation paper theorem](weak-pbe-restriction-preservation.md)
for finite perfect-recall games under the same clean matching and robust
collection bounds. At a new information set, perfect recall prevents the
acting player from later returning to one of its own copied sets. Freeze
fully supported raw lotteries at copied sites into chance, solve the remaining
new-site games, and take a strategy/belief limit. Then install the source's
possibly inconsistent off-path beliefs at copied sites. New-site full-policy
rationality survives the replacement. At copied sites, a direct first-departure
repair bounds every whole-policy deviation; it does not use a one-shot
principle with arbitrary off-path beliefs. Reached Bayes beliefs transport
through clean execution.

This proves more on paper than the SE capstone alone implies, but the new
weak-PBE completion and repair adapters are not Lean-checked. Stronger PBE
definitions imposing relations between off-path beliefs need separate analysis.
The honest-disclosure counterexample still applies because its legitimate
information refinement fails the clean structural premise.

There is also a sharp checked audit boundary. For a single strictly profitable
comparison, a sound final-transcript audit can deter it with a finite penalty
iff it has positive observable probability outside the admitted clean
transcript family. See `exists_sound_deterrent_iff` in
[ObservableEnforcement](../GameTheoryExtensions/Analysis/ObservableEnforcement.lean).
If a profitable pending-leak deviation's entire final observation law is
supported on admitted transcripts, that audit cannot punish it soundly. This
is a statement about the specified evidence interface;
authenticated ingress evidence or irrevocable obligations may change it.

Positive observable mass for each individual deviation is weaker than a
uniform rate for an infinite deviation family. Nor is this single-comparison
characterization a necessity theorem for all possible compilers or equilibria.
Unprofitable departures, different comparators, and alternate mechanisms can
preserve SE without the coarse bound used above.

## The realistic target and the next mathematical step

A backend need not make pending messages physically invisible. It must explain
all decision-visible contents and metadata through the source decision view
and ancillary runtime observations, with scheduler inputs source-public, or
classify a revealing departure as an excluded action with
a sufficient incremental cost. Encryption alone does not establish that law.
Ordinary liveness alone does not supply protected admission or a conditional
collection bound. The concrete deployment obligations remain those in the
[blockchain target analysis](blockchain-se-preservation-target.md); no general
public-mempool blockchain corollary follows from this round.

The next useful formal result is the bounded public scheduling constructor and
its two inductions, followed by its composition with the checked audit theorem.
It would be a general SE compiler theorem for a stated class of services,
keeping clocks out of the source language. A concrete chain or sequencer then
needs a separate refinement of that service and its actual evidence/escrow law.
This is much closer than an entirely new equilibrium theory: enforcement and
rational completion are available; information and execution refinement are
the remaining mathematical substance.
