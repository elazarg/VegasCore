# Weak PBE for the native two-late-opening game

Analysis by Codex. The exact finite native game in
[the two-late-opening counterexample](native-late-action-analysis.md) has a
weak perfect Bayesian equilibrium with the selected source law, although
for the high inclusion probabilities specified there no sequential equilibrium
has that law. This is a paper result for the full bounded raw response menu.
It is not a general PBE preservation theorem or a machine-checked result.

Here **weak PBE** means sequential rationality at every information set,
against every available continuation policy, and Bayes' rule at every
information set reached with positive probability from initialization.
At a zero-probability information set, beliefs may be any distribution
supported on its legal compatible histories. They need not be limits of one
common sequence of fully mixed profiles, or agree across different off-path
information sets. The proof uses this precise convention.

## The concrete game

Alice initially owns a successful commitment to a Boolean bit `b`. She also
knows a separate private label `l` in `{A,B,C}`. The bit is one with probability
`9/20`; the independent label is uniform. The label is an ordinary private
input, with no associated commitment or reveal obligation.

The source program first reveals Alice's bit, then lets Bob commit an
unguarded answer, then requires Bob to reveal that answer. His six answers
are Safe, three label guesses and two bit guesses. If Alice's reveal succeeds,
Bob receives `2/5` for Safe, one for a correct label guess and zero for a bit
guess. Alice receives `R/2` for Safe; any label guess pays her `R` at labels A
and B and zero at C. If Alice's reveal fails, Bob receives one for a correct
bit guess and zero otherwise. Alice receives `R` for a guess of one at label
A, `R` for a guess of zero at B, and zero otherwise. A failed Bob answer
reveal gives both players zero gross reward.

Use `R>0`, a source forfeit `D>max(R,1)` for each failed reveal, and target
audit deposits `K_A>R`, `K_B>1`. The audit observes the whole actual signed
traffic and charges each author at most once. An unaccepted identifier or an
accepted packet with forbidden settled content triggers that author's charge.
The source SE has both openings succeed, Bob chooses Safe, and its joint law
is

`(b,l, successful bit b, successful answer Safe, R/2, 2/5)`.

The native public builder offers Alice a protected activation at clock zero,
then late activations at clocks one and two. A protected proper opening is
included immediately. After protected silence, a sole proper late opening is
included at clock two with probability `q`, where `0<q<1`. With two proper
openings, either identifier is included with probability `q/(1+q)` and neither
with probability `(1-q)/(1+q)`.

Bob's first activation is at clock one, between the late turns. If Alice's
event is still unresolved, his binding is not ready. If her protected opening
already completed the event, this is his only timely binding opportunity.
His later binding activation is clock three, after Alice's acceptance or
expiry. A completed Bob binding permits another activation at that clock for
its immutable opening; an incomplete binding does not grant another binding
choice. Clock six offers a remaining opening activation, after any incomplete
binding has expired. All events expire by clock ten. Every Bob activation
immediately receipts his latest emitted identifier, regardless of its call.

At each activation, each foreign pending identifier is independently sampled
with probability `lambda`, `0<lambda<1`. Learned packets persist. A dropped
Alice opening remains pending and may later be learned. All private action
aliases, prepared candidate states and remembered samples remain in players'
information.

The relative deadlines, opportunity bounds, protected receipt bounds, fixed
finite padding and complete raw menu are exactly those of the linked native
counterexample. In particular, the finite raw alphabet contains both Boolean
values, all three typed labels and all six typed answers; any finite superset
is allowed. Prepared-slot capacity is at least the finite command horizon.
Malformed packets, wrong addresses, withholding, duplicate identifiers,
private opening material and every bounded owned or known-forwarded evidence
request are available. The public builder satisfies its service promises on
every legal raw history.

**Claim.** For every `0<q<1` and `0<lambda<1`, this full native game has a
weak PBE with the selected source joint law. No large-`q` condition from the
SE-negative proof is required here.

The collateral is fixed before `q` and the builder are chosen. This is a
pointwise existence claim for each configured service; the off-path priors
and optimal raw continuations may depend on that service. It does not assert
one assessment for players who know only bounds on an unknown builder.

## Why Bob can have uniform label beliefs everywhere off path

The label has a stronger property than being hidden along honest execution.
Changing Alice's initial private label while keeping the bit and all raw
action labels fixed gives a bijection between legal histories. The public
application transitions, scheduler inputs, packet observations, candidate
catalogues and Bob's full remembered information are unchanged. Alice's
private observation of her input changes, as do the utility functions that
depend on that input. The action menus are unchanged.

This follows from the particular program: its guards are empty, and no
transition or opening obligation reads Alice's private label. The raw menus
also do not require a packet's supplied value to equal an ordinary private
input. A certificate of an Alice-prepared candidate containing A authenticates
that candidate's value. It does not authenticate that her original private
label was A. Opening certificates for her initial bit authenticate only the
bit. This relabeling keeps every transmitted value and candidate meaning
fixed; it does not erase a remembered attempted value or its certificate.

Consequently every legal Bob information set has compatible histories for all
three labels. Arbitrary dirty traffic cannot structurally exclude a label.
This fact also holds when Bob remembers his own earlier raw transmissions,
including their private registration material.

Choose a full-support reference distribution on all legal native prefixes
through Alice's last clock-two response. One concrete choice uses the original
initial law, the actual public builder and observation kernels, and uniformly
mixed raw responses at every pre-tail information set. Alice's uniform
reference kernels commute with the label relabeling because the menus are the
same. Thus the reference distribution, conditional on any Bob information,
has uniform label marginal.

The reference distribution is only a device for specifying legal off-path
beliefs. It is not the equilibrium distribution. It includes dirty prefixes,
unseen extra Alice packets, Bob's private aliases and his possibly poisoned
candidate slots. No dirty history is deleted or declared distinguishable.

Bit beliefs are obtained by conditioning this reference distribution on the
**whole compatible native history**. They are not assumed to remain `9/20`
whenever no certificate was observed. For example, a handler's rejection of a
wrong-bit opening may itself constrain the bit. Authentic evidence and public
acceptance are also respected. The uniform-label conclusion survives all
these restrictions because the label relabeling preserves them.

## Bob's full continuation, including charged histories

After Alice's clock-two response, she has no further strategic move. Bob's
remaining problem is therefore a finite single-player decision problem with
Nature, under the reference prior just specified. Its states retain the
entire actual prefix and Bob's full recall. Use the actual future scheduler,
observation rule, raw menus, forfeits and capped audit.

Solve that decision problem sequentially. To make its off-path beliefs
coherent, keep the reference prior fixed and use a full-support Bob response
sequence. Perfect recall makes the probability of his own past behavioral
choices common to every history in a current information set. Those factors
cancel in Bayes' rule. His counterfactual posterior therefore does not depend
on which full-support response probabilities were used. A finite
single-player optimal-control limit gives an optimal continuation at every
information set with these posteriors. Equivalently, maximize expected utility
over floor-constrained fully mixed policies and divide by positive reach
before passing to a compact limit.

All these posteriors have uniform label marginal. More importantly, this is
one coherent continuation assessment under a full-support prior over actual
prefixes, rather than independent guesses at each future information set.
It establishes optimality against arbitrary multistep raw policies.

The construction leaves unrestricted what Bob optimally does after a charge
is already unavoidable. He may use another prepared handle, additional
traffic or a retained certificate. There is no claim that an already collected
deposit charges every later deviation again.

Some choices of this optimum are nevertheless determined on the histories
needed below. If Bob reaches a live binding with no previous transmission,
his next prepared slot is fresh. A correctly registered typed answer followed
by its protected opening is free. Under uniform labels, after Alice succeeds,
Safe strictly beats every label guess: `2/5>1/3`; bit guesses give zero.
After Alice fails, a typed bit guess maximizing the reference posterior is
optimal. This continuation has nonnegative net reward in every actual hidden
state, even if that bit guess is wrong.

Once a typed answer is immutably bound to Bob's owned openable candidate,
successful protected opening maximizes its fixed gross reward and avoids the
forfeit. Choose the optimal continuation to open at the first timely callback
on these histories. After completion choose silence. These choices are
optimal pointwise in the hidden state, so they can be imposed as tie breaking
within the reference optimum. An authored commitment fixes its fresh
candidate to its supplied value or to an unopenable meaning; omitting its
private value does not create a later free value-choice opportunity.

## Bob's first activation

At clock one Bob has no previous response, so his own audit is clean at every
one of his information sets.

If Alice's event is unresolved, his binding is not ready. Every transmitted
packet is permanently forbidden and gives utility at most `1-K_B<0`, even
under the best later raw continuation. Silence leads to the protected binding
and opening choices just described, with net reward at least zero in every
hidden state. Prescribe silence at all these information sets.

If Alice's event already completed at clock zero, his binding is ready. This
is his only timely binding callback. Use a label-uniform reference belief
supported on that whole information fiber. Correctly binding Safe gives
`2/5`; a label guess gives `1/3` and a bit guess zero. An invalid packet either
incurs `K_B` or makes the answer opening fail and incurs `D`. Waiting loses
the timely binding opportunity. Prescribe the canonical typed Safe binding.
His later immutable opening succeeds under the specified tail policy,
regardless of Alice's remaining raw moves.

This proves sequential rationality at the first activation, including all
its dirty Alice observations. Alice cannot induce a different answer simply
by putting her label in an unauthenticated raw packet: Bob's off-path
label-uniform belief remains supported on legal histories with every label.

## Completing Alice coherently

Fix Bob's entire policy from the preceding construction. It is defined at
every raw information set, not only at clean success and failure records.
We now construct Alice's strategy and beliefs without forcing them to equal
Bob's reference beliefs.

Perturb every Bob response toward full support, obtaining policies converging
to this fixed policy. For each perturbation, maximize Alice's initialized
expected utility over her policies subject to a positive probability floor
$\delta_n$ on every available action, with $\delta_n\to 0$ and each floor below
the reciprocal of the maximum finite action count. The constrained sets are
therefore nonempty. This is a finite
single-player control problem. Its compact strategy space has a maximizer.
The perturbed Bob policy and Alice's floors give positive reach to every legal
Alice information set, so use actual Bayesian beliefs there.

At an information set with `m` actions, approximate any pure local alternative
by probability $1-(m-1)\delta_n$ on that action and $\delta_n$ on each other one.
Perfect recall ensures that changing the current response does not change
the probability of reaching this information set. Global optimality therefore
implies a conditional one-shot regret bound of at most

\[
(m-1)\delta_n(R+D+K_A).
\]

Divide out the positive reach probability **before** taking limits. Thus the
bound also holds at information sets whose reach tends to zero arbitrarily
fast. The utility diameter used here is valid for all raw terminal histories:
Alice has one reveal and one capped audit charge, so her net reward lies in
`[-D-K_A,R]`.

Take a common compact subsequence of all strategies and actual Bayes beliefs.
Alice's limiting local inequalities hold at every information set. Her
beliefs are limits of this actual fully mixed sequence and consequently have
the conditional coherence needed for the perfect-recall one-shot-deviation
principle. They establish sequential rationality against all her continuation
policies, including policies following dirty private memories or Bob raw
signals. This is not an appeal to local optimality with independently chosen
weak-PBE beliefs.

For this argument one may retain the unused limiting Bob beliefs from that
same sequence, making a complete consistent assessment and proving Alice's
sequential rationality in it. Subsequently replacing **Bob's** beliefs by his
reference beliefs changes neither the behavioral profile nor Alice's
continuation utility comparisons. Bob was already sequentially rational
under the separately constructed reference assessment.

## Alice's initialized choices and the source law

Against the fixed Bob policy, a proper protected opening followed by silence
gives Alice exactly `R/2` at every initial type. Bob binds Safe and eventually
opens it, with no charge or forfeit for either player.

Any other emitted Alice root packet is permanently forbidden and gives at
most `R-K_A<0`. Only root silence needs a further comparison. Under that
choice, partition terminal paths of any Alice continuation policy:

- A forbidden Alice identifier gives at most `R-K_A<0`.
- If there is no such identifier but her reveal fails, the net reward is at
  most `R-D<0`.
- Otherwise exactly one proper late Alice packet was emitted and accepted.
  Bob was silent at his unresolved clock-one activation, so his next prepared
  slot is fresh. His label-uniform success choice is Safe, and Alice gets
  exactly `R/2`.

All Alice responses finish before the late inclusion lottery. The last
category has probability at most `q`: a sole proper packet is accepted with
that probability; an additional identifier puts the path in the first
category even if one packet succeeds. Define

`c = max(R-K_A, R-D) < 0`.

Every root-silence continuation is therefore bounded above by

`q R/2 + (1-q)c < R/2`.

This bound covers deliberate withholding, retries, raw signaling and their
adaptive or mixed combinations. It does not assume the large-`q` canonical
late-action reduction of the SE-negative proof. At small `q`, an off-path
Alice optimum may withhold or send additional packets; the preceding control
construction supplies whatever rational continuation is required.

Sequential rationality at Alice's root now forces a proper protected opening,
up to private aliases of its unique permitted public packet. At her remaining
initialized activations, silence keeps the reward `R/2`, whereas an extra
identifier gives at most `R-K_A<0`. Hence the limiting strategy is silent
there. The initialized source parameters, successful publications and net
rewards have exactly the selected source law.

## Actual Bayes' rule and the dirty-history merge

Alice's limiting beliefs already satisfy Bayes' rule at every information
set with positive limiting reach, by continuity of the finite conditional
probability formula. Bob's reference beliefs may give positive mass to unseen
Alice extras that his current record does not distinguish from honest play.
Replace his beliefs at every actual positive-reach information set by the
actual initialized posterior.

This replacement preserves his optimality. At his initialized binding choice,
the protected public bit is known and the independent label is still uniform,
so Safe remains strictly optimal. At later initialized information sets his
own typed Safe answer is already fixed; protected opening or silence after
completion is optimal pointwise in every compatible hidden state. The
replacement removes reference-only dirty histories without changing those
comparisons. Bob's zero-reach information sets retain the legal reference
beliefs and their coherent optimal continuation.

In particular, an unseen extra Alice packet after her first late opening
can merge into the clean late-success records used in the SE-negative proof.
We do not split that information set. Bob's label-uniform reference belief
and optimal policy are specified for its **entire** actual information fiber.
It is globally off path under Alice's protected opening, so weak PBE imposes
no actual-profile Bayes relation tying its posterior to Alice's rational late
timing choices. Bob's continuation is rational under his reference prior;
Alice's late timing is rational against his continuation under her own
limiting beliefs. Neither player is assumed to forget a raw action or
candidate value.

The resulting assessment is sequentially rational everywhere and obeys
Bayes' rule at every positive-reach information set. It is therefore a weak
PBE under the stated convention, with the exact selected source law.

## What this separates

For the high values of `q` in the native negative, one common fully mixed
witness would impose the success-belief cross identity incompatible with
Alice's type-dependent late timing and Safe at both late records. The weak
PBE construction does not supply that common witness. Its two off-path belief
constructions are deliberate and permissible under the stated definition.

Thus this one full native fixture distinguishes exact source-law preservation
by weak PBE from preservation by SE. It proves neither general weak-PBE
preservation nor a result for stronger PBE conventions imposing additional
off-path consistency. The result concerns an ideal-certificate finite symbolic
runtime with fully collectible capped audits. It includes actual pending
observations and raw packet deviations. Fees, outside signaling, strategic
builders, capital timing, physical chain capacity and finality are excluded,
as in the companion native result.

Status: the complete paper construction passed independent mathematical review
and the coordinating review. These cover the full raw menu, label symmetry,
coherent Bob continuation, Alice's normalized control limit, merged dirty
information fibers and actual-positive Bayes override. No Lean theorem,
runtime change or owner-controlled checklist completion is claimed.
