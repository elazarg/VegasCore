# Pending-message strategic preservation: mathematical proof

This is a working proof, not a statement of mechanized completion. The target
is the actual principal-scoped message-policy execution, with visible pending
payloads and separate sealing and opening. The mathematical construction below
identifies the whole-program coupling to prove in Lean. Section 8 distinguishes
the argument established here from its unimplemented operational premises.

## 1. Statement and scope

Write `S` for the written-order game of a checked source program, `C` for the
playerwise compilation of source policies, and `R_E` for execution of its message
application against a fixed environment policy `E`. The environment controls
delivery and inclusion using its complete observable pool and history. It does
not receive unopened service values or the honest players' private randomness.
Its choices may depend on observed payload contents, including pending openings.

The immediate executable fragment has finitely many source sites, homogeneous
commitment values, unrestricted guards, and reveals of program-created
commitments. Source policies may depend on all their declared reads. For this
proof use finite value domains and a bounded native execution tree. This is a
proof scope, not a claim that the existing source-to-graph theorem needs finite
value domains. Samples, nontrivial validation, and heterogeneous encodings
remain requirements for the broader compiler; they are not silently covered by
the current sealed backend.

The desired inequality, for every source profile `sigma`, player `i`, and
arbitrary native player policy `D`, is

```text
E[U_i(R_E(C(sigma_-i), D))]
    <= sup_tau E[u_i(S(sigma_-i, tau))].                         (1)
```

Here `u_i` measures source outcomes, and `U_i` measures actual runtime outcomes.
Their agreement on successful compiled execution is proved by an outcome law.
A quitting settlement has the meaning supplied by the program's resolution
mechanism, not an arbitrary utility assigned to an unfinished prefix. Utilities
in (1) exclude extra preferences for packet order, time, fees, and raw traces;
those need an additional comparison at the relevant runtime edge.

The current untimed application does not instantiate the resolving `R_E`
required here. The coupling can first be proved for its actual bounded prefixes;
Section 7 specifies what the resolution edge still has to implement.

Together with the honest outcome law, (1) gives Nash and same-error epsilon-Nash
preservation and reflection at compiled profiles. There is no claim about every
runtime equilibrium, coalitional deviations, or every utility of an affected
opponent. A bound on the deviator's utility alone does not transport an honest
player's worst-case guarantee against adversaries with other preferences.

## 2. Concrete compiled behavior and service assumptions

The source-policy implementation is a mathematical strategy translation, not
mandatory client code imposed on players. Unilateral replacements remain arbitrary.

At each invocation a compiled policy selects the first owned unfinished ready
node in source order. Readiness and this selection use public node metadata and
event presence, not sealed values.

* At a commit, recover exactly the site's declared source reads from initial
  visible inputs, included public events, and the owner's accepted commitments.
  If the slot is empty, draw once from the source kernel and privately register
  that value. Otherwise submit the canonical opaque `(owner, node)` handle.
  Repeated invocations reuse the registered value.
* At a reveal, submit the opening of that same registered value only once its
  public prerequisites are satisfied. Retransmission is allowed.
* Ignore unrelated pending payloads, receipts, and delivery order when choosing
  a source value. These remain visible to an arbitrary replacement policy.

The proof uses the following operational facts, each with a concrete obligation:

1. **Binding and ownership.** Only a principal can register its slots. The first
   value is fixed. Inclusion validates the sender, endpoint, prerequisites, and
   opening. Replays cannot overwrite an accepted source binding.
2. **Value-independent hidden traffic.** Before publication, an honest value
   affects neither packet contents nor control flow visible to `E` or `i`.
   Registration is private; handle identities and retry rules do not encode the
   value. Rejected attempts cannot test another owner's secret through a public
   validation oracle. This last point uses ownership checks as well as hiding.
3. **Publication barrier.** Before an honest opening at source position `r` is
   submitted, every source-earlier commitment is already accepted and bound.
   This is a submission condition, not just an inclusion check. A deviator may
   publish its own values earlier; they are already known to that deviator.
4. **Declared reads and recall.** An honest decision uses precisely its source
   view at that site. Source views retain previous own choices and prior public
   values, so a source strategy can reconstruct its simulated private memory.
5. **Service and resolution.** The invocation/service assumptions give every
   timely valid honest message an opportunity to be included before its relevant
   timeout. Waiting does not keep the bounded execution unresolved indefinitely.
   A failure invokes the program's specified quitting continuation. In particular,
   arbitrary traffic does not consume the honest service guarantee by flooding.

Fairness is an explicit hypothesis, not a theorem that a blockchain must be fair.
It must hold uniformly over the unilateral policies quantified in (1), not just
on the honest execution. An absolute deadline that can expire before its node
becomes enabled does not satisfy this requirement merely because the environment
is eventually fair. The currently fixed invocation list is also part of the
service condition; an adaptive invocation scheduler would require its own
observation-local instance.

## 3. The coupling to construct

Fix `sigma_-i`, `D`, and `E`. The target is a joint finite law of

```text
(X, Y, B, H),
```

with these properties:

* `X` has exactly the actual native execution law with deviator `D`.
* There is a finite distribution `mu` of legal source policies for `i` such that

  ```text
  law(Y) = sum_tau mu(tau) * law(S(sigma_-i, tau)).              (2)
  ```

  Opponents' policies are unchanged. The mixture is chosen independently of
  their private random draws; it may depend on their policy functions.
* `B` says a runtime-only quitting resolution occurs. On `not B`, the actual
  outcome of `X` is the observation of the complete source execution `Y`.
* On `B`, `H` is the prefix at the first such resolution. The source execution
  `Y` agrees with the compatible pre-resolution choices, accepted bindings, and
  disclosed values. It then completes legally. It does not rewrite a commitment
  that was already fixed on that prefix.

The last requirement is a counterfactual source completion, not a command that
opens an expired runtime slot. A normal source execution can complete even when
the coupled runtime execution refuses to do so. We need no executable runtime
strategy that travels back to a missed deadline.

Explicitly committing the legal source quit value is an ordinary source choice.
It is not automatically classified as `B`. The flag concerns extra runtime
resolution behavior, such as withholding a previously committed non-quit value.

For the current untimed kernel, a useful precursor replaces `B` by failure to
finish within the invocation horizon. It gives a coupling of a genuine native
prefix to a source completion. It does not give that unfinished prefix a payout
or identify it with a source quit. The resolution edge must supply those facts.

## 4. Constructing the source policy without future information

This is the substantive mathematical construction. The required Lean theorem
is the joint law in Section 3, not another record assuming that law.

### Fix only the deviator and environment randomness

Predraw the random decisions of `D` and `E`, obtaining deterministic contingent
policies indexed by a seed `w`. Do not fix the honest players' private random
choices and give them to the extracted policy. The resulting `mu` averages the
source policies constructed for the possible `w`.

For finite domains and a finite horizon, the relevant interaction tree is
finite: branch over honest source values and each fixed policy's finite-support
commands, including the fallback continuations used below. Unbounded numeric
packet identifiers do not require a distribution over all possible identifier
tables. Only finitely many policy queries occur in this finite tree. Predrawing
must share a draw at equal local policy inputs, rather than assigning inconsistent
decisions to occurrences of the same information state.

### Replay a symbolic native execution at each source decision

At a source decision `c` of player `i`, the extracted policy receives the source
view `v`. Replay the native machine from the initial state with seed `w`:

* Execute `D` and `E` on their actual reconstructed observations.
* Represent an honest registered value at node `d` by a private placeholder
  labelled `d`. Its presence is known; its value is not supplied to `D` or `E`.
  Do not evaluate the honest choice kernel inside this replay.
* Honest private registration and opaque submission have value-independent
  command shapes. Readiness, slot occupancy, message identifiers, and receipts
  can therefore be replayed without evaluating those placeholders.
* When an honest opening is submitted, substitute the corresponding published
  value from `v`. Deliveries and inclusion then expose the actual payload, and
  `D` and `E` may use its contents without restriction.
* Return `i`'s first registered value for slot `c`. If resolution or the finite
  horizon is reached first, use a fixed legal fallback at `c`.

Returning at registration is useful: before that instant the slot cannot have
been accepted, and every subsequent attempt has the same value. Registration
for a future source site may occur early; replay reconstructs that private
memory when the future source site is reached. No source strategy is given an
extra memory argument.

**Why an opening query is available in `v`.** Before returning the first
registration for `c`, an honest opening at a position `r > c` cannot be submitted:
the publication barrier would imply acceptance, hence prior registration, of
`c`. Every honest opening encountered is therefore source-earlier than `c`, and
its public value is present in `v`. The native scheduler may learn this value
before inclusion; the source policy at `c` already knows it by source order.
An early cleartext packet from `D` contains a value computed by `D`, not an oracle
for a hidden honest value.

This proves the replay does not need future source information. On arbitrary
unreachable source views, a mismatch with earlier own choices can return the
legal fallback. On reachable views, the induction below proves consistency.

### Coupling invariant and induction

Use one joint construction with the actual source runner and actual native
runner. Its invariant records:

1. matching source variables and native slots for the choices already coupled;
2. matching included public fields, plus the identities of honest pending draws;
3. the exact native pool, receipts, focal history, and environment history
   produced by symbolic replay when its published placeholders are instantiated;
4. honest draws have the joint law generated by their source kernels at the
   corresponding source views. Conditioning on a shared disclosed value updates
   the latent joint law identically on both sides, including the posterior of
   values that remain unopened. No hidden value is resampled from its old prior.

The last clause is a distributional invariant. Merely proving that some source
completion exists for each native trace is insufficient.

There is a direct finite-probability check for the two marginals. With `w`
fixed, let `t` be a complete native command prefix up to, but not beyond, its
first extra resolution. Include private registration commands in this
proof-facing prefix, although they remain absent from opponent observations.
Let `J(t)` be the honest sites freshly registered in `t`, and `a_d` their
values. For a valid prefix, the actual probability is

```text
p_w(t) = product over d in J(t) of sigma_owner(d)(a_d | v_d(t)). (6)
```

Every other transition is deterministic at fixed `w`. Each `v_d(t)` is already
fixed by the prefix when registration happens. Readiness implies that any
predecessor on which its kernel depends has already been supplied. The set
`J(t)` need not be a prefix of written source order.

The source construction gives exactly the same probability to the cylinder of
complete source runs that replay `t`. To see this, induct on native commands.
For focal or environment commands, the next command is constant throughout the
cylinder: the replay uses only already exposed values. For a fresh honest draw,
its declared inputs are fixed in the cylinder; refine the cylinder by its chosen
value, multiplying its mass by the factor in (6). Unexposed honest draws have no
descendant data tested by this prefix unless that data has already been generated
and included in the cylinder's constraints. In particular, an unregistered
honest predecessor cannot be read by a later honest registration. Speculative
focal registrations are also constant across completions, because replay returns
at that registration before consulting any later opening.

Equivalently, expand the source run into the product of its honest kernels,
with the extracted focal choices deterministic. Factors for exposed draws are
fixed as in (6); sum out unconstrained choices in reverse dependency order.
Their normalized kernels contribute one. This establishes the cylinder law,
including dependence between honest choices, without a conditioning library.
The source marginal is the source runner by construction, and these cylinder
probabilities establish the actual native prefix marginal. After a quitting
resolution, generate the native suffix using its actual kernels; do not require
its choices to agree with the counterfactual source completion.

Induct over the finite source sites, with the bounded native replay between
sites. The cases are:

* **Honest registration.** Source and runtime use the same kernel at equal
  declared reads. Couple the draw once and remember its node identity. If native
  registration precedes the source site's position, defer its value in symbolic
  replay. Such deferral is valid because command shape and all intervening tests
  ignore the value until its publication; its kernel depends only on source
  predecessors. Independent draws can be exchanged; dependent draws retain
  their predecessor order. This is repeated finite bind/map algebra, not a
  claim that all honest draws are mutually independent.
* **Focal registration.** Replay reaches the same command on the same local
  input. The extracted source choice is its value. Previous own choices agree
  by induction and source recall. A repeat registration changes neither side.
* **Submission, delivery, inclusion, rejection, wait.** Replay preserves the
  observable state and histories exactly. An honest handle contains no unresolved
  placeholder. Validation either uses known focal data, a correctly constructed
  honest message, or rejects an unauthorized attempt independently of the secret.
  Accepted graph writes preserve the binding correspondence.
* **Honest opening.** The barrier argument supplies its value from the relevant
  source view. Pending delivery may disclose it immediately; the coupled replay
  then exposes the same value. An opening of `i`'s own slot is already known.
* **First extra resolution or exhausted prefix horizon.** Stop exact-prefix
  matching. Preserve choices already bound on that prefix; use the extracted
  policy's recorded choices or legal fallbacks at the remaining focal sites and
  the unchanged honest source kernels at the others. Earlier speculative honest
  draws remain coupled at their source sites. This completes a legal source run.

Returning at each first registration prevents later runtime observations from
changing an earlier source decision. Replaying from the initial state makes the
source policy a function of `v` and `w`, rather than a separately chosen action
for each terminal trace. The source runner supplies the honest draws, giving
(2); the paired native transitions give the other marginal. On completed runs
with no extra resolution, every binding matches, hence so does the outcome.

For the honest-law instance, keep the focal compiled policy's draws as source
kernel draws as well. Each first registration uses the specified kernel exactly
once; value-independent scheduling cannot select or reroll its result. The
same induction then has source marginal `S(sigma)`, not merely an unspecified
mixture against `sigma_-i`. An arbitrary-deviation coupling alone would not
establish this additional identification.

Two parts of this induction need particularly explicit formal treatment:
deferral of honest draws with dependent kernels, and consistency of replay
across successive source views. They are the mathematical proof obligations to
test first. The argument above is not yet a checked operational coupling.

### Worked multistage test: a disclosure correlated with an unopened value

Consider this source order, with `B` the deviator and `A`'s policy fixed:

```text
A commits X, uniformly in {0,1}
B commits b0
A commits Y, equal to X with probability 3/4
A reveals Y
B commits b1
A reveals X
B reveals b0 and b1
```

`A` may read its own `X` when choosing `Y`. Its policy induces the joint law

| X | Y | Probability |
| --- | --- | --- |
| 0 | 0 | 3/8 |
| 0 | 1 | 1/8 |
| 1 | 0 | 1/8 |
| 1 | 1 | 3/8 |

The environment can see the pending opening of `Y`, choose inclusion order from
its value, and deliver it to `B` before inclusion. This conveys information about
the still-sealed `X`: conditional on `Y`, the probability that `X = Y` is `3/4`.
There is no unconditional "scheduler is independent of every unopened value"
claim. Its visible input is legitimately correlated with `X`.

Nevertheless, `b0` was bound before `Y` could be submitted. At the source choice
of `b1`, the source view already includes `Y`. The extracted policy for `b1`
can therefore replay all those value-dependent scheduler decisions without
knowing `X`. The pending opening of `X` cannot be submitted until `b1` is bound.

For payoff `+1` when `b1 = X` and `-1` otherwise, choosing `b1 = Y` earns `1/2`
at the source. Observing pending `Y` permits the same choice, not a better-informed
one. If extra quitting pays `-2`, continuation is better by at least `1` on
every complete outcome, so (5) applies to this disclosure decision. If extra
quitting instead pays `0`, stopping only on a mismatch after observing `X` earns
`3/4`; that fails the continuation comparison. This latter comparison concerns
the fixed opponent policy, not strict dominance against every opponent strategy.

The replay carries placeholders for `X` and `Y`, substitutes the source's `Y`
when it is published, and later uses the same source draw of `X`. Independently
resampling `X` after seeing `Y` would replace the displayed joint law and give
the wrong answer. The coupling must preserve the whole dependency, not just
the two marginal distributions. No native chance publisher is added here:
`A`'s randomized source policy generates both choices.

## 5. Quitting comparison and its exact consequence

Assume the coupling has been constructed. Put `Q_i(X) = U_i(X)` and
`V_i(Y) = u_i(Y)`. On non-quitting runs these agree by the outcome law.
Let `J` record the available stopping information on quitting runs. It includes
the player's actual observations and remembered commands, not hidden service
values or an omniscient future random tape. For each supported `j`, require

```text
E[Q_i(X) | B, J = j] + delta <= E[V_i(Y) | B, J = j],           (3)
```

where `delta >= 0`. The right side is the specific legal source-completion law
constructed above. It is not a choice of a new source action after seeing the
terminal hidden state. Condition (3) concerns complete continuations, including
later decisions and settlements; comparing only the immediate transfer is not
enough. It must hold for the profiles and deviations quantified by the theorem.

This is an inequality on first-resolution branches, not a claim that opening
remains feasible after expiration. No decision at the expired state is used
to establish the source marginal or the Nash improvement.

**Theorem (coupling consequence).** Under the honest outcome law, the coupling,
and (3),

```text
E[U_i(R_E(C(sigma_-i), D))] + delta * Pr(B)
    <= sum_tau mu(tau) * E[u_i(S(sigma_-i, tau))].              (4)
```

**Proof.** Partition the finite joint probability space into `not B` and the
events `B and J = j`. On `not B` the utility difference is zero. Multiply (3)
by `Pr(B and J = j)` and sum. This gives
`E[V_i(Y) - Q_i(X)] >= delta * Pr(B)`. Substitute marginal (2). This proves
(4), including zero-probability and randomized stopping cases. No closure of
source policies under mixtures is used. A component of a finite mixture attains
at least its average, so some single legal source policy attains the right-hand
bound needed in (1).

For a source epsilon-Nash profile, each term on the right of (4) is at most the
baseline source utility plus epsilon. Honest-law equality gives the same bound
in the target. Conversely, compiling any profitable source deviation preserves
its utility and the baseline, proving reflection at compiled profiles.

If `delta > 0` and `Pr(B) > 0`, the extracted mixture has strictly greater
utility than `D`; some component does too. Its compiled strategy is a feasible
ex-ante improvement against the unchanged compiled opponents. Thus such `D`
is not a best response against those opponents. This is not an assertion about
arbitrary opponent runtime policies or about off-path quitting prescriptions.

### A stronger, source-facing sufficient condition

Condition (3) is less demanding than a pointwise comparison, but depends on the
coupled continuation law. A simpler sufficient certificate for a mechanism is:
for every possible first-resolution prefix `h`, every settlement `z` obtainable
through its declared quitting continuation, and every legal complete source
outcome `y` compatible with the locked choices and disclosed values of `h`,

```text
U_i(z) + delta <= u_i(y).                                     (5)
```

The coupling's compatibility invariant makes (5) imply (3). Deposits or bounded
payoff ranges can make (5) provable without a prior over hidden values. Requiring
it for every possible compatible completion is deliberately stronger than
necessary. It is a usable sufficient condition, not a characterization of all
implementable equilibria. Its runtime settlement must still be connected to
the programmer's actual resolution code.

## 6. Why ordinary strict dominance is not the complete condition

Consider one strategic player and a mandatory fair public chance draw. The
source first commits either `play` or `quit`, draws a public bit, and then
deterministically reveals the committed choice. The utility of `quit` is zero.
The utility of `play` is `3` on heads and `-1` on tails.

At the source, `play` strictly dominates `quit`: its expected utility is `1`,
against `0`. If the runtime permits withholding after observing the bit and
settles withholding as quit, the policy "commit play; open on heads; withhold
on tails" earns `3/2`. The random draw is chance, not a strategic publisher.
It is observed at the same source stage; the new capability is the later exit.

This example does not refute (3): on tails its comparison is `0 <= -1`, which
fails. Nor does it say that visible pending openings intrinsically break Nash.
It identifies the information at which the quitting comparison must hold.
The current sealed backend does not implement sample nodes; this example tests
the broader proposed theorem, not an alleged executable fixture in that backend.

## 7. Runtime resolution must respect the source meaning

The written core's `reveal` copies its existing sealed value. The nullable
surface `yield` commits an optional value and reveals that same option. If it
committed `some a`, expiration cannot produce a full source environment in which
that very reveal instead copied `none`. Such an environment violates the source
equation. This is independent of utility dominance.

There are two distinct obligations:

* Implement the programmer's intended quitting settlement, with its real output
  and continuation. Recover that meaning from the program/compiler artifact;
  do not manufacture a default payout or add an extra player choice to the source.
* Compare that settlement with a legal committed source continuation using (3)
  or a sufficient condition such as (5). Utility preservation does not require
  falsely identifying the two full terminal environments.

The source currently records nullable values and commitment-accounting
obligations; the surface explicitly does not yet attach quit handlers. The
timeout adapter sets a resolution status. Neither fact alone implements a
general per-site quitting continuation. The connection to the richer compiler's
timeout clauses is therefore an operational implementation obligation, not a
missing probability lemma. The minimal core need not acquire the richer surface
syntax to express the compiler-side resolution contract.

## 8. What this settles, and the next iteration

The finite coupling consequence (Section 5) is a complete mathematical argument.
Section 4 gives a concrete construction and induction for the causal completion
coupling; its symbolic execution and draw-deferral steps still need a precise
operational proof. No end-to-end Lean theorem is claimed here.

The next work should directly serve the following two proofs:

1. Construct the Section 3 coupling for the actual bounded sealed policy runner,
   including arbitrary local deviations and pool-observing adaptive delivery.
   Implement the compiled policy used by that statement. Prove its honest law
   with the same coupling, not a second independent whole-program proof.
2. Supply source-accounted deadline resolution and discharge its compatibility
   and incentive premises. Instantiate the existing `UtilitySimulation`; no new
   generic strategic framework is needed.

Before expanding the Lean support library, test the coupling on multistage
programs with early future registrations, pending openings delivered before
inclusion, value-dependent scheduling after disclosure, and dependent honest
choices. A pointwise trace decoder, a source policy selected after observing a
terminal secret, or a terminal-state completion argument without marginal (2)
does not pass this test.

The existing native binding and opening-barrier theorems support Section 2.
The source-to-declared-read-graph certificate already supplies the written
source correspondence. Local history reconstruction serves the concrete
compiled policy; it is not a substitute for (2). The full pending-message
strategic theorem remains the completion criterion.
