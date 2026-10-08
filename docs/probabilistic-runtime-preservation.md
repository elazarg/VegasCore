# Equilibrium preservation when honest publication can fail

Analysis by Codex. A finite-horizon runtime with unavoidable unrecovered
publication failure presents a limitation before strategic incentives are
considered: its observable law cannot equal a source law that always
publishes. Making that failure probability tiny also does not guarantee
preservation of every selected source equilibrium by an exact target
equilibrium. Source indifferences can disappear under arbitrarily small noise.

This analysis concerns a different backend assumption from the native
`AsyncContract`, which supplies sure delivery for protected conformant
submissions. That contract and the current runtime semantics are unchanged.
The probabilistic model below is an explicit alternative service, not an
instantiation claimed to satisfy the native contract.

## A quantitative obstruction independent of equilibrium

Let $F$ be the observable event that a required publication has not succeeded
by the fixed horizon. Suppose the source outcome law $\mu$ has $\mu(F)=0$.
If every target policy profile $\sigma$ has

$$
\nu_\sigma(F)\ge\beta>0,
$$

then every target profile, including every Nash equilibrium, weak PBE, or SE,
satisfies

$$
d_{\mathrm{TV}}(\nu_\sigma,\mu)\ge\beta.
$$

This follows by evaluating the total-variation difference on $F$. It does
not depend on pending-message visibility, belief consistency, deposit size,
or the presence of other equilibria. Charges can change preferences over
failed executions; they cannot make a missing typed publication appear.
Failure must remain in the compared observable outcome. Conditioning the
target law on success would define a different preservation claim.

A primitive service model supplies the premise rather than assuming it.
Let the physical state contain the full execution history, and let $F'$ be
the states whose publication readout lies in $F$. At each opportunity use
the kernel

$$
K_\sigma(s)
=\rho\,\delta_{o(s)}+(1-\rho)L_\sigma(s),
\qquad 0<\rho\le1.
$$

Here $o$ advances the outage execution without repairing publication:
$s\in F'\Rightarrow o(s)\in F'$. It may advance clocks and record that an
opportunity was consumed. The nonoutage kernel $L_\sigma$ is unrestricted;
it can incorporate adaptive fees, retries, private submission paths, and
policy-dependent history. Every state in $F'$ has conditional probability
at least $\rho$ of remaining there. Starting unpublished, after $N$ finite
opportunities the law therefore has

$$
\nu_\sigma(F)\ge\rho^N,
\qquad d_{\mathrm{TV}}(\nu_\sigma,\mu)\ge\rho^N.
$$

The product proof needs no independence between different opportunities or
between counterfactual policy choices. It needs the conditional floor after
the entire current history and the chosen action, uniformly over every
available continuation. Time-dependent kernels are included by storing the
stage in the state. At most $N$ opportunities can be padded with idle rounds
that preserve the missing-publication event.

An even simpler primitive has one initial outage lottery. With probability
$\beta$ the ledger remains unavailable through the horizon, so all policies
produce failure. The other branch can be any policy-dependent service,
including sure inclusion for some observed circumstances. Mixing these
branches gives the same all-policy bound $\beta$. A global outage suffices
for this observable-law obstruction even when a uniform conditional floor
at every later decision is false.

Neither fixed horizon nor a public mempool alone establishes either
primitive premise. A favorable observed proposer schedule, a guaranteed
reservation, or an available alternate service may eliminate conditional
risk. Any application of the bound must quantify over the actual available
fees, submission paths and recovery mechanisms, and explain why an outage
is unrecovered before the compared horizon. These are operational
assumptions, not consequences of the game-theory theorem.

The probability statements are formalized in
[PublicationFailureObstruction.lean](../GameTheoryExtensions/Analysis/Protocol/PublicationFailureObstruction.lean):

- `outageKernel_failure_floor` derives the conditional floor from the
  explicit primitive lottery.
- `outageRun_failure_probability` and
  `outageRun_totalVariation_lower_bound` derive the finite-horizon bound
  for an arbitrary nonoutage kernel and an observable readout.
- `outageRun_not_realized` rules out exact law equality.
- `binary_publication_error` starts with an unpublished Boolean and compares
  against a surely published source; every such service has error at least
  $\rho^N$.
- `global_outage_totalVariation_lower_bound` covers the initial unrecovered
  outage lottery with an arbitrary normal branch.

The targeted `lake --wfail build` passes for this module. They are
probability obstructions, not a checked compiler impossibility result or a
change to `AsyncContract`.

## Small physical error can still remove a selected exact equilibrium

Consider a finite perfect-recall one-player source game. The player chooses
a value $A$ or $B$, then chooses whether to open it or lawfully withhold.
Let $R>0$ and $D>R$. Opening succeeds surely and gives payoff $R$ for either
value. Withholding gives payoff $R-D$ for $A$ and $-D$ for $B$.

Opening strictly dominates withholding after either choice. Both successful
value choices tie. Every mixture of $A$ and $B$, followed by opening, is a
source SE, weak PBE, and Nash equilibrium. In particular, pure $B$ gives
the source observable law concentrated on $(B,\mathrm{success})$.

Now give either actual opening the same failure probability
$\varepsilon\in(0,1)$. Failure keeps the chosen value in the observable
terminal record and gives the corresponding withholding payoff. No other
feature of the game changes. The payoffs from opening are

$$
U_A=R-\varepsilon D,
\qquad U_B=R-\varepsilon(D+R).
$$

Opening remains strictly optimal at either continuation: its advantage
over withholding is $(1-\varepsilon)D$ for $A$ and
$(1-\varepsilon)(D+R)$ for $B$. But $U_A-U_B=\varepsilon R>0$.
Every exact target equilibrium therefore selects $A$.

No exact target equilibrium approaches the selected pure-$B$ source
equilibrium's outcome: the event "chosen value is $B$" has source
probability one and target-equilibrium probability zero. Their
total-variation distance is one for every $\varepsilon>0$, despite uniformly
vanishing transport and payoff perturbations as $\varepsilon\to0$.
This is a failure of preservation of each selected source equilibrium;
other source equilibria, including pure $A$, do have nearby target
equilibria. It is unrelated to message leakage or an inconsistent belief
assessment. There are only singleton player information sets.

The target policy that selects $B$ and opens has whole-continuation regret
exactly $\varepsilon R$ at the initial choice and zero regret at the opening
decisions. It has a consistent assessment and is an
$\varepsilon R$-approximate SE, with observable-law distance exactly
$\varepsilon$ from the selected source law. Thus this example admits a
useful approximate preservation statement while exact target SE
preservation fails. The example is a paper proof, not linked to the Lean
equilibrium definitions.

## What an approximate theorem would have to prove

There are two distinct possible targets:

- an exact native SE whose observable law is close to each selected source
  SE's law;
- a consistent native assessment with small sequential regret whose law
  is close to that source law.

The example disproves a general implication from arbitrarily reliable
transport to the first target. It does not disprove the second. The second
still needs a proof: small initialized outcome error alone does not control
conditional continuation payoffs at rare information sets, and a common
global consistency sequence remains necessary. A bound such as
$\delta$ times the payoff range is justified when the relevant
whole-continuation laws are uniformly within $\delta$ under the deviations
being compared. An unconditional honest-execution bound is insufficient.

The protected-success model used in the
[fully public disclosure-phase theorem](full-public-disclosure-phase-preservation.md)
avoids the physical failure obstruction by assuming a sure protected turn.
That paper theorem constructs a target SE for every source Nash outcome in
its single fixed-value phase, even with many finite late opportunities.
Replacing that sure turn by an unrecovered probabilistic service is a
material assumption change. Neither finite penalties nor complete public
observation repairs exact law equality under the outage premises above.
