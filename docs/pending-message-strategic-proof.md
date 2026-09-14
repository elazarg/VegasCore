# Pending-message preservation: model and mathematical argument

This note specifies a finite commit/reveal source, its compiled policies, and
a resolving public-message runtime. It proves a causal coupling for the
pre-resolution execution and derives a utility-specific end-to-end theorem.
The coupling is constructed, not assumed as a theorem premise.

The operational resolution rules in Section 3 are implemented by
`Interaction.SealedResolution`, with a shared policy-runner round driver.
The source-policy translation implements those completion checks and retains
own private memory across nullable defaults; its before-timeout policy law is
checked. The source/native execution coupling, including the actual timeout
continuation and arbitrary randomized focal and environment policies, is checked.
Finite termination, deadline-relative service excluding honest timeouts, and
the exact source/native coupling are checked for the fixed-clock round driver,
including decoding at normal completion. The all-compiled honest outcome law
is checked against the original written-source profile, under periodic service.
`SealedCompilation.RoundModel.isεNash_iff_of_checkpointDominance` proves
end-to-end Nash and same-error epsilon-Nash preservation and reflection under
the conditional utility comparisons of Section 6. Its quantitative version
charges a margin times the actual probability of timeout. The compiler's joint
law retains actual timeout-checkpoint information and a legal source completion
with focal registrations fixed. A uniform cap on own timeout utility is a
checked sufficient case. Every completed public settlement, including after
timeouts, agrees with a legal source execution. That support theorem does not
preserve private registrations or fixed source policies. For utilities valuing
the programmed payout, `RoundModel.isεNash_iff_of_sourcePayoutBound` discharges
the incentive premise from a uniform bound over legal source executions.
More general source continuation tests remain obligations.

## 1. Exact scope and conclusion

Fix a finite player set and a checked source program with these properties:

- It has finitely many commitment and reveal sites, and no chance sites.
- Commitment values belong to a finite nonempty common domain
  `D = Option A`. Write `bottom` for `none`.
- Every commitment guard accepts every value in every typed source view.
- Each reveal targets a source commitment, not an initial sealed input.
  Source accounting implies at most one direct reveal per commitment. A
  commitment need not have a direct reveal. The initial environment is fixed.
- A decision's source information contains earlier public fields and the
  player's earlier private choices. The compiler retains exactly those reads.
- Outcomes are computed from the terminal public environment by a total
  function `O`. It can retain the entire public environment, evaluate the
  program's payout expressions, or both. Utilities `u_i : Outcome -> Real`
  are supplied separately.

The no-sample, common-type, unrestricted-guard, and reveal-origin conditions
are backend admission conditions, not a weakening of source well-formedness.
Direct-reveal uniqueness is derived from checked source accounting rather
than required separately. The broader compiler still needs heterogeneous
values, nontrivial guards, and samples. The Lean settlement theorem permits
any common value type with a chosen default; the nullable type here gives that
default its intended source-level quitting interpretation.

Let `S(sigma)` be the program outcome of written-order source execution.
Let `C` translate each source policy to the native policy in Section 4.
Let `R_E` be the resolving runtime in Section 3 with a fixed environment
policy `E`. Native deviations
are arbitrary observation-local policies, not restricted to compiler output.

The theorem proves an honest outcome law and a deviation bound. Under the
continuation incentive condition in Section 6, for every player `i` and
native unilateral replacement `D_i`, there is a finite mixture `mu` of legal
source policies, with unchanged opponents, such that

```text
E[u_i(R_E(C(sigma_-i), D_i))] + delta * Pr(B)
    <= sum_tau mu(tau) E[u_i(S(sigma_-i, tau))].               (1)
```

`B` is the event that at least one timeout resolution occurs. The comparison
is made at the first such resolution; it concerns complete settlements, not
an immediate transfer. Weak comparison (`delta = 0`) suffices for Nash and
same-error epsilon-Nash preservation and reflection at compiled profiles.
Strict comparison has the additional consequence stated in Section 6.

A native utility may instead depend on the entire runtime record. The same
argument applies if its honest values agree with the source utility and it
satisfies the continuation comparison. Extra trace preferences are therefore
an additional incentive obligation, not automatically preserved.

## 2. Source and graph semantics

Number all source events `0,...,n-1` in written order. Let `K` be the
commitment sites. Each `c in K` has owner `owner(c)` and at most one direct
reveal `r(c) > c`, when it has a direct reveal. A complete assignment is
`a in D^K`.

Written-order execution assigns a value at each commitment and copies that
value at its reveal. Initial inputs and these choices determine the full
source environment. Let `I_c(a)` be the visible source input before decision
`c`. It depends only on source-earlier events; it contains no unopened value
belonging to another player. A behavioral policy supplies a kernel

```text
sigma_owner(c),c(- | I_c) in FinDist D.
```

Write `O(a)` for applying the outcome function to the public terminal
environment generated by assignment `a`. Every assignment is legal because
guards are unrestricted. This fact is used both for source-policy totalization
and for nullable resolution; it cannot be dropped merely because `bottom` is
legal.

Compilation assigns one graph node to each source event and emits:

1. ownership and the source commitment referenced by each reveal;
2. edges from every producer of a declared decision input to that decision;
3. an edge from every source-earlier commitment to every reveal;
4. any further dependency edges required by the existing graph compiler.

All edges point backwards in source order. Graph execution writes immutable
fields; its decision kernel reads precisely the source input. In particular,
unrelated ready nodes may execute out of written order, but a decision cannot
read a field whose producer has not completed.

The existing source-to-graph law identifies written-order execution with the
canonical declared-read graph policies. For this note it also follows directly
by evaluating the same finite kernels in a topological order: exchanging
independent steps leaves the product law unchanged. Dependencies are not
treated as independent draws.

## 3. A resolving public-message runtime

### Native state, observations, and commands

Keep the current message application's ideal write-once service and message
pool. The service maps owner-scoped handles `(owner,slot)` to absent or
registered values. Only that owner can register a slot. Registration is a
private local operation; handles contain no value-dependent data.

The pool has pending messages, an included ledger, recipient inboxes, and
sender histories. An included message remains available as ledger data.
Delivery and replay copy preexisting messages. They do not change the
authenticated author or payload. Players see their own inbox/sent data, the
public ledger and receipts, public application state, clock, and their own
command history. The environment sees the entire pool, public application
state, clock, and its own command history. Neither interface contains the
ideal service table.

The player command set includes arbitrary private registrations, submissions,
replays, and waits. Payloads include commitments, openings, cleartext attempts,
and malformed messages. Payloads for arbitrary numeric sites are permitted in
the pool; validation determines whether they affect the application.

A commitment at node `c` is accepted only for its owner, its canonical handle
`(owner(c),c)`, an occupied service slot, satisfied dependencies, and a node
not already completed. An opening at `r(c)` additionally requires that
accepted handle and a claimed value equal to the registered value. Authentication
is checked before any value comparison can affect a public result. An attempt
to open another owner's handle is rejected independently of its hidden value.
Cleartext and malformed application payloads are rejected.

Acceptance, rejection, inclusion, and delivery are publicly observable as
specified by the pool and receipts. The environment can adapt to their contents;
it is not restricted to a schedule sampled independently of disclosed data.

### Logical completion and nullable resolution

Distinguish private registration from the program's public resolution:

- A commitment is pending, accepted with its canonical handle, or defaulted.
- A reveal is pending or published with a value in `D`.
- A completed node never changes its public result.
- Private service values are never overwritten, including on timeout.

Registering `bottom` is an ordinary sealed source choice: the service contains
`some bottom`, not an absent slot. Its compiled policy sends an opaque handle
and later opens it normally. A public timeout default is a distinct event;
the compiler does not replace an honest commitment to `bottom` by cleartext.

A node is ready once every graph prerequisite is complete. Defaulted
commitments count as complete. A ready reveal of a defaulted commitment
automatically publishes `bottom`; no missing secret is needed to do so.

When an unresolved ready commitment times out, mark that commitment defaulted.
This does not insert a fake private registration. When a ready reveal of an
accepted commitment times out, publish `bottom` at that reveal and record its
failure. The original service value and acceptance record remain unchanged.
Late messages cannot rewrite either result.

Continue executing the same graph after a timeout. Honest policies see
`bottom` through the appropriate public reveal field and keep using their
declared source kernels. Arbitrary deviators remain arbitrary; a single
timeout does not implicitly ban a player from future sites. This is per-site
resolution, not the richer compiler's persistent per-role bail policy.

Once all nodes are complete, evaluate the *same program outcome function*
`O` on the final public environment. In particular, evaluate the same payout
expressions; do not substitute a new default payout or ascribe utility to an
unfinished prefix. All program reveal fields now have values of their original
nullable types.

This rule is a precise meaning of continuing with a missing value as `null`.
It is not an implementation of arbitrary `||` subgames or quit handlers.
Those need their own continuation semantics and compiler edge.

**Settlement interpretation.** For a completed native run define its effective
assignment `e_c` to be the published value at the unique direct reveal of `c`,
or `bottom` if that commitment has no direct reveal.
The source execution with commitment assignment `e` is legal, and its final
public environment equals the runtime's: each source reveal copies `e_c`,
which is exactly the runtime field. Hence the runtime outcome is `O(e)`.

This is a pointwise public-outcome statement. It neither backtranslates
strategies nor equates all private histories. If a player registered `some x`
and then withheld its opening, the effective assignment has `e_c = bottom`,
whereas the actual private service still contains `some x`. The incentive
proof retains that original locked choice in a *different*, counterfactual
source execution.

Source accounting rules out conflicting direct aliases. Unrestricted guards
also matter: a later guard invalidated by replacing a value with `bottom`
would invalidate this settlement interpretation.

### Clock, service, and termination

Here is one explicit bounded clock discipline. It is enough for the theorem;
it is not a statement that every real network provides these bounds.

Each round has one invocation opportunity for every principal in a fixed
order and then a fixed finite number of environment command opportunities.
The environment chooses deliveries, inclusions, or waits adaptively. The clock
advances by one at the next round boundary. Readiness timestamps are recorded
when nodes first become ready. Deterministic propagation of defaulted reveals
is applied after changes to completion state. At a round boundary, expired
ready nodes are resolved in increasing source order before further commands.
Completion is tested at round boundaries. If the last node completes during
a round, the remaining wire opportunities still occur; completed program
fields cannot change. The round then ends and the driver stops.

Assume that every nondeviating rule owner occurs in the fixed roster at least
once per round, and assume a finite service bound `b`: every canonical message
submitted in round `r` is offered inclusion by the end of round `r+b`, unless
its application node has already completed by that service checkpoint. The
checkpoint qualification matters: a later deadline timeout cannot discharge
the service premise retroactively. The bound is uniform over all replacements
of the other policies. A stronger all-message service condition is independent
of designating a player honest and avoids needing to recognize hidden validity:
each envelope is included by its service checkpoint unless the whole application
has already completed by then. It concerns inclusion attempts, not guaranteed
acceptance of invalid payloads. Early termination does not erase a missed
service deadline earlier in the run.

There must be enough environment command opportunities to realize this
condition. It is nonvacuous without forcing immediate service. Let `m` be the
roster length, counting duplicate invocations. During any block of `b+1`
rounds, at most `(b+1)*m` new pending copies can arrive, even under arbitrary
deviator traffic. Starting from an empty queue at the previous drain, reserving
that many inclusion opportunities at the end of the block empties the queue;
all other opportunities may still be used adaptively for deliveries,
inclusions, or waits. Thus every submission is included within `b` rounds
unless the driver has already terminated by that checkpoint.
A capacity-constrained or censoring runtime requires a different bound or a
different theorem.

Set, conservatively,

```text
L = n * (b + 3) + 2
deadline(d) = firstReadyRound(d) + L.
```

For an honest-owned target `d`, include `d` itself and all source-earlier sites
owned by the same player. Charge each such commitment `b+2` rounds and each
such reveal `b+1` rounds. If the resulting prefix charge is `W_b(d)`, a
sufficient clock condition is `W_b(d) + 2 <= window`; the uniform coarse
condition is `n*(b+2) + 2 <= window`. A timestamp may be recorded just after
its owner's call,
and expiration runs before the next round's player calls at clock
`firstReadyRound(d) + window`. In this worst placement there are only
`window-1` designated owner polls before expiration. The condition supplies
`W_b(d)+1` such polls, strictly more than their possible total charge. The
displayed `L` is a deliberately looser bound. If there is no honest-owned
node, the service statement is vacuous and no positive-window premise is
needed.

The clock and relative deadlines are part of the runtime definition. A real
ledger implementation must realize the clock and timeout checks, for example
through included timeout transactions. Eventual fairness alone does not
establish this finite service guarantee.

**Service lemma.** No compiled player times out under the service bound,
including after other players' defaults.

To prove it, suppose a ready node `d` of a compiled player remains unfinished.
Every subsequent invocation of that player selects an unfinished ready node
`c <= d`. A commitment is privately registered at most once; the next selected
invocation submits its handle. A reveal submits its cached opening at its
first selected invocation. These packets are valid: the local cache and service
agree, dependencies persist, and all declared reads are present. A reveal of
a defaulted producer is propagated automatically.

Designate the first invocation of that owner in each round and charge the
round to its selected node. A commitment has at most one charged fresh
registration. Every other charged invocation at that site submits its cached
handle. If its first submission is in round `r0`, subsequent charged
submission rounds lie in `r0,...,r0+b`, including the round whose service
phase includes it. Thus a commitment receives at most `b+2` charges and a
reveal at most `b+1`. The first submission need not occur at a designated
poll: extra roster invocations or an earlier submission only shorten this
interval. A completed node cannot be selected again.

Sum these fiber bounds over the owned prefix through `d`. More than
`W_b(d)` charged polls are impossible while `d` remains ready and incomplete.
Other owners' completions can enable an earlier node and change the selector;
this argument does not require a constant selector or an uninterrupted block
of service to the same node. The chosen `L` supplies the required number of
pre-expiry polls with slack. A missed service checkpoint earlier than expiry
cannot be discharged by the later timeout.

The required cache/read facts hold initially and are preserved by legitimate
completions and nullable defaults: defaults supply typed public fields; own
registered commitments retain their cached values. The phase argument does
not require absence of earlier defaults. Every putative honest timeout has a
retained readiness timestamp, and the preceding polling interval forces that
site to have completed before expiry. A completed site cannot subsequently
acquire a timeout. Consequently every failure in a unilateral-deviation run
belongs to the deviator.

The checked periodic implementation reserves sufficient capacity at every
block-final wire phase, maintaining empty queues at the block boundaries.
Its finite invocation horizon contains whole service periods; a horizon that
is a sufficiently large multiple of `b+1` also contains the termination bound.
The actual round driver still stops at first application completion. This
whole-period condition concerns the retained proof trace's service checkpoints,
not additional actions after the runtime has stopped.

**Termination lemma.** Every policy profile and every environment policy,
even an unfair one, terminates under the clock/timeout mechanism within
`n*(L+1)` rounds.

Once all prerequisites of a node are complete, the first following round either
completes it or records a readiness timestamp no later than that round's clock.
The timestamp persists. After `L` further rounds the node cannot remain
unexpired. Induction over the source-ordered rules completes the first `k`
nodes within `k*(L+1)` rounds; earlier completion ends the run immediately.
For `n=0`, completion already holds without a round.

This supplies a finite horizon independently of the service hypothesis.
Service is used to rule out honest failures, not to define payoff at a
nonterminating execution.

The bound is checked by `SealedResolution.runRounds_complete` for any enabled
backward-dependency rule list and initial state whose recorded timestamps are
no later than its clock. `SealedFragment.resolvingRuntime_runRounds_complete`
discharges both rule conditions from the fragment certificate and the timestamp
condition from canonical initialization. It permits arbitrary player and wire
policies, including an empty roster and zero service slots. It does not identify
the public settlement with a source outcome. The fixed-clock, early-stopping
driver and the finite-invocation runner used by the coupling are executions of
the same application. `MessageApplication.RoundDriver.runRounds_eq_tracePolicies` accounts
for the clock commands and early completion, and
`SealedCompilation.exists_randomized_round_source_coupling` supplies the
resulting exact source-mixture/native-round marginal laws.

## 4. Actual compiled player behavior

At each invocation, select the least owned unfinished ready source node.

- At a commitment, if its private registration cache is empty, reconstruct
  exactly the declared source input and draw from that source kernel. Privately
  register the value. On subsequent invocations, submit the canonical opaque
  handle without drawing again.
- At a reveal of an accepted commitment, submit the cached opening only once
  the public prerequisite check succeeds.
- An automatically propagated reveal requires no player command.
- With no eligible node, wait.

The cache is computed from the owner's command history. Public source inputs
come from immutable included application fields; own private inputs come from
accepted own commitments and the cache. Unrelated wire contents, receipts,
and clock values are not inputs to an honest source kernel. They remain visible
to an arbitrary replacement policy.

A registration for an unaccepted future site is not treated as an available
source field merely because it occurs in the owner's private history.

## 5. Constructing the whole-program coupling

Fix an opponent source profile, a focal native deviator `D_i`, and environment
policy `E`. This section constructs, rather than postulates, the source
mixture and the joint law.

### 5.1 Finite predrawing

The preceding horizon and finite value domains give a finite reachable tree
for the fixed native policies. Although numeric message identifiers are
unbounded types, each queried policy has finite support and there are finitely
many invocations. Take the union over all honest value assignments; it is
still finite.

Predraw only the deviator's and environment's responses at their reachable
local policy inputs. A seed `w` specifies deterministic policies `D_w,E_w`.
Its distribution is independent of the honest players' private draws.
Equal local inputs in different hypothetical runs use the same table entry.
Within one run an actor's local command history grows at every invocation,
including waits, so a given local input is not queried repeatedly along that
run. The table sampling therefore has the original behavioral law.

Do not predraw the honest values into a tape accessible to the source
deviator. Their kernels can depend on earlier private values and disclosures.

The checked `MessageApplication.exists_native_response_mixture_tracePolicies`
predraws the focal player with other policies unchanged;
`exists_environment_response_mixture_tracePolicies` predraws the environment
with every player policy unchanged. Both instantiate one shared proof for a
selected native invocation and preserve the entire invocation trace law.
Neither changes the environment's full-pool observation or the application's
stochastic kernels. Selecting an environment invocation in the singleton
analysis protocol does not add a strategic player to the runtime game.

Composing these decompositions yields a finite joint mixture of deterministic
focal and environment responses. The second mixture may depend on the first
response; an independent product is not assumed. This is an analytical joint
draw, not a runtime mechanism giving players access to shared randomness.
The result needs neither finite native command types nor a uniform cover over
all honest assignments.
It may depend on the fixed opponent profile. The stronger common-seed
construction across environments and opponent profiles described above is not
claimed by these theorems. Exact trace preservation transports any almost-sure
property of the actual executions; it does not claim that each deterministic
environment obeys a service condition at unreachable histories or against all
other profiles.

### 5.2 Value-substituted replay and read-boundedness

Let `H` be the honest commitment sites and let `a in D^H`. Run the actual
native machine with `D_w,E_w`, replacing each fresh honest draw at site `d`
by `a_d`. All other policy code, histories, pool operations, validations, and
clock transitions are unchanged. Stop immediately before the first clock step
that performs timeout resolution, or at a successful round boundary. Denote
this deterministic prefix by `T_w(a)`. This is a proof-side evaluation, not an
extra runtime strategy.

For each focal commitment `c`, let `F_c(w,a)` be its first correctly owned
private registration in that prefix, or a fixed legal fallback `beta_c` if
absent. Registrations at unrelated owner/slot pairs are ignored. Choose the
fallbacks explicitly; they need not be `bottom`.

Let `V_c` consist of honest commitment sites whose reveals precede `c` in
written source order.

**Read-boundedness.** If `a` and `a'` agree on `V_c`, then
`F_c(w,a) = F_c(w,a')`, including agreement on whether that registration
occurs before stopping.

Here is the lockstep invariant up to the first focal registration at `c`:

- equal pool, public events, receipts, clock, readiness timestamps, focal
  command history, and environment command history;
- equal service-slot occupancy everywhere;
- equal service values at all focal handles and at honest handles in `V_c`;
- at each honest owner, its cache agrees with its own service; the two
  honest histories need not be equal;
- every authenticated opening retained in the pool refers to one of the
  handles whose values agree.

It holds initially. The following cases preserve it.

1. **Focal or environment invocation.** Their local inputs agree, so the fixed
   policies choose the same command. A focal registration writes the same
   value to its own slot. Its early cleartext or opening attempts may say
   anything computable from that input, identically in both runs.
2. **Honest node selection.** Completion, readiness, and ownership are public.
   Cache occupancy and public events determine typed read availability;
   replacing a present value by another value of the same type cannot change
   that check. Thus the same node and command shape are selected.
3. **Honest registration.** The same slot is queried. If its producer is in
   `V_c`, the assigned values agree; otherwise only the private values may
   differ. First-registration caches continue to match their services.
4. **Honest opening.** An opening at `r > c` cannot be submitted: its
   prerequisites include commitment `c`, hence acceptance and prior
   registration of `c`. An opening cannot be at `c`, which is a commitment.
   Thus any honest opening before this stopping point is at `r < c`; its
   value is in `V_c` and the payloads agree.
5. **Delivery and replay.** They copy identical known messages, preserving
   authentication and the opening condition.
6. **Inclusion.** Commit validation depends on occupancy. A correctly
   authenticated opening checks a handle with equal values. An opening of
   another owner's handle is rejected by ownership checks independently of
   its claimed or hidden value. Consequently acceptance, rejection, and
   their receipts agree, not just the successful application changes.
7. **Clock and stopping.** Equal completion and timestamp data give equal
   deadlines, automatic actions, and first-timeout decisions. There has
   been no earlier default, because this is the first-resolution prefix.

An honest history can contain different private values; the argument does not
feed that history to the deviator. At the focal registration the commands
agree, and if no registration occurs the fixed fallbacks agree. This proves
read-boundedness by induction over the finite invocation prefix.

Therefore each `F_c` factors through `a restricted to V_c`. Define a
deterministic source policy `tau_w` using this factor and the corresponding
values from its source view. Use a fixed extension of that partial assignment
when evaluating the factor; read-boundedness makes the extension irrelevant.
Every full assignment is legal. On unreachable inconsistent source views,
totalize with the fixed fallback.

This defines a *single policy family for all focal sites*. It is not a
collection of source actions selected after inspecting terminal secrets.
All arguments of `F_c` precede `c`; its definition never refers recursively
to future source play. Early speculative focal registrations are reproduced
at their own source sites by this same family.

### 5.3 The source law and exact prefix cylinders

Execute the source with `tau_w` and the unchanged honest policies. Let
`q_w` be the resulting law of its honest assignment. Its mass is

```text
q_w(a) = product over honest sites d in source order of
           sigma_owner(d),d(a_d | I_d(a,F(w,a))).              (2)
```

The factors are causal, not independent: a factor can depend on earlier honest
choices and earlier focal decisions. Read-boundedness makes every focal
decision causal as well. Summing variables in reverse source order proves
normalization.

The checked source point-mass theorem is `Vegas.denoteSource_prob_eq_prod`,
audited as `Vegas.Paper.source_point_probability`. It applies to the existing
written-source denotation, with every binding retained in its terminal
environment. The factors include sample probabilities, guarded commitment
probabilities, and a final equality check. The cylinder calculation below works
directly on these complete source environments; it does not need a separate
point-mass formula for the projected honest assignment law in (2). The dependent-choice
regression copies a first draw at a later source decision: its factors are
`[law.prob value, 1, 1]`, including when `law.prob value = 0`.

Consider any supported full native prefix `t` before the first resolution,
including private registration commands and the invocation records for waits.
Let `J(t)` be its honest registration sites and `b_d` their values. An honest
site is registered at most once: after registration its cache is occupied,
all future invocations use the cached handle, and the cache never empties.
Consequently the native prefix probability at fixed `w` is

```text
p_w(t) = product over d in J(t)
           sigma_owner(d),d(b_d | nativeInput_d(t)).           (3)
```

There is no probability factor for deterministic messages, retries, rejection,
clock advancement, or waiting.

At the native level, `MessageApplication.tracePolicies_prefixThrough_prob_eq_prod`
proves the exact product of invocation probabilities for the existing stopped
trace projection, including zero-mass and inconsistent trace queries. It
integrates the unrecorded suffix, without stopping or changing the runner.
`invoke_player_prob_of_step` reduces a player's invocation factor to its command
probability; recorded histories distinguish commands with identical native
effects. These results are runtime-general. The compiler reduction to precisely
the fresh honest registrations in (3), with the same source inputs and fixed
native responses, is established by `replay_prefix_prob_eq_product` below.

Define the rectangle

```text
C_t = { a in D^H : a_d = b_d for every d in J(t) }.
```

**Cylinder lemma.** `T_w(a)` extends `t` if and only if `a in C_t`.

The forward implication reads the private registrations in the trace. For the
reverse implication, induct over `t`. At a fresh honest registration the
queried coordinate is fixed by `C_t`. Every other command uses already
registered data or the fixed policies. Hence the *entire* native state and
histories are equal at each stage, including private values already used.
Clock and stopping decisions are consequently equal too. This lemma is about
a proof-facing prefix, not what a player can observe.

**Kernel agreement.** For every `d in J(t)`, its factor in (2) is constant
over `C_t` and equals its factor in (3).

The checked local probability identity is
`SealedCompilation.restrictedSourceRun_registration_probability`: at a selected
fresh registration before timeout, every reference source realization gives
the same original written-source decision probabilities as that native input.
It identifies the source occurrence by its instruction position and recovers
the source view from terminal compiler-field agreement. Its equality covers
all queried values, without assuming they have positive probability.
`restrictedSourceRun_weight_eq_product` applies it to every occupied honest slot
and proves the source likelihood constant. `replay_prefix_prob_eq_product`
identifies the same product with the native prefix mass; the two equalities
yield `extractedSourceRun_native_prefix_law`.

At that native registration, all producers of declared reads are complete.
An honest producer has already registered, constraining its value in `C_t`.
A focal producer has a first registration in the prefix. The cylinder lemma
makes it identical in every replay in `C_t`; it is exactly the source value
`F_c(w,a)`. Reveals copy those values, and fixed initial inputs agree.
These are all the declared inputs, so the source and native kernel arguments
agree. This also handles a native choice performed ahead of unrelated earlier
source events: those events cannot be missing producers of its read set.

**Prefix mass.** `q_w(C_t) = p_w(t)`.

Construct a source restriction `rho_t` that fixes each honest site in `J(t)`
to its recorded value `b_d` and leaves every other source kernel unchanged,
including the focal policy `tau_w`. These forced values are legal in the
admitted unrestricted-guard fragment. Let `nu_t` be the ordinary normalized
source execution under that restricted profile. This reference law is used
only to calculate probabilities, not as the backtranslated deviation: the
source marginal to be simulated still has the original opponents.

For a complete source environment `s`, let `W_t(s)` be the product of the
original conditional probabilities of the forced choices. The exact identity is

```text
1_{C_t}(s) * mu_w(s) = W_t(s) * nu_t(s),
mu_w(C_t) = E_{s ~ nu_t}[W_t(s)].
```

Here `mu_w` is the original full source-environment law, whose honest-coordinate
projection is `q_w`. The Lean theorem `denoteSource_restriction_density` proves
the pointwise identity for general source restrictions, and
`denoteSource_restriction_probability` sums it. It allows samples, guards, and
restrictions selected at source policy inputs. `denoteSource_restriction_support`
proves that all reference runs satisfy the restriction. No positive mass or
conditional distribution is needed; a forced choice may have probability zero
under the original policy.

Kernel agreement gives `W_t(s) = p_w(t)` throughout the support of `nu_t`.
The reference law is normalized, so
`denoteSource_restriction_probability_of_constant` gives the required mass.
Equivalently, the free-coordinate sums in (2) can be eliminated in reverse
source order after pulling out the fixed factors. The reference-law proof
uses the existing source denotation to perform that normalization directly.

The general source identities are checked and audited in `Paper.lean`.
`SealedCompilation.recordedChoiceRestriction` constructs `rho_t` from the
private service in the recorded prefix. Only occupied slots at honest source
decisions are fixed; the extracted focal policy and unoccupied honest kernels
remain unchanged. The compiler proves that these source choices recompile to
the recorded graph values. `restrictedSourceRun_source` identifies the reference
execution with the ordinary restricted written-source law.
`restrictedSourceRun_replay_prefix` proves that every supported reference
realization reproduces `t` exactly, including private histories, pending traffic,
receipts, and clock. Its arbitrary-cutoff statement is a support result, not a
probability identification beyond first timeout. Neither construction grants
players access to the proof-facing service snapshot.

`restrictedSourceRun_registration_kernel` applies the original source/native
kernel comparison throughout this reference support, at every selected
pre-timeout checkpoint of the same recorded trace. It does not require positive
mass under the original profile. Reassignment changes a registration's value,
not its selected slot, so the comparison uses the same native input for every
reference realization.

`extractedSourceRun_replay_iff_restriction` identifies the restriction event with
the exact replay cylinder on every supported original source outcome. It uses
the recorded decision values in the terminal source environment, their compiler
field correspondence, and the occupied native honest slots.
`extractedSourceRun_replay_probability` transports this event probability through
the checked whole-program source law. `extractedSourceRun_replay_likelihood`
then instantiates the source restriction identity above: the replay cylinder
mass is exactly the expectation of `W_t` under the ordinary reference source
execution. `Vegas.Paper.pending_source_cylinder_likelihood` audits this formula.

`restrictedSourceRun_weight_eq_product` proves `W_t` constant throughout `nu_t`.
`VegasCore.decisionPositions` enumerates the owners and source instruction
positions; `SourceChoiceRestriction.weight_eq_decision_product` indexes the source
likelihood by these positions. At every occupied honest slot, the native theorem
`SealedResolution.registrationCheckpoint_selected` supplies a pre-timeout snapshot
whose owner policy can select the recorded registration. The source/native
decision identity supplies its factor at every reference realization. No positive
mass under `mu_w` is required. The theorem
`extractedSourceRun_replay_prob_eq_product`, audited as
`Vegas.Paper.pending_source_prefix_product`, eliminates the expectation and
identifies the source cylinder mass with this fixed product.

`replay_registration_factor` proves that the selected checkpoint and the actual
invocation have the same original kernel. Both reconstruct the declared reads
of the same complete source realization; equality of snapshots is not assumed.
`IdealCommitments.registrationWeight_sealValue` counts each tracked first
registration once, and `SealedResolution.tracePolicies_prefixThrough_prob_eq_registrationWeight`
identifies the resulting product with the original native stopped-trace mass
under the local command-probability equations. The compiler discharges these
equations in `replay_prefix_prob_eq_product`. All remaining invocations have
unit factors, including repeated submissions and focal registrations.
The proof multiplies equations without dividing, so zero factors are allowed.

`extractedSourceRun_native_prefix_law`, audited as
`Vegas.Paper.pending_source_native_prefix_law`, equates the entire prefix law
with replay of the ordinary source execution against the extracted focal policy.
Agreement of masses on the normalized source law's support also rules out extra
native mass outside that support. Both marginals are therefore checked for fixed
deterministic focal and environment responses, up to and including first timeout.

This step preserves dependent honest draws. It does not assume that a
scheduler's public input is independent of every still-unopened value.

### 5.4 Both marginals and the continuation

Draw `a ~ q_w`. Let `s_w(a)` be the corresponding complete source assignment
with `tau_w`, and let `Y = O(s_w(a))` be its program outcome. Retain the source
assignment in the joint record. Let the native pre-resolution prefix be `T_w(a)`.
The cylinder and mass lemmas identify its *entire* native prefix law, hence
its stopped-prefix marginal, with the actual native runner at seed `w`.

If it completes normally, its assignment is `s_w(a)` and its program outcome
is `Y`. Otherwise, retain the first-timeout prefix `h`, execute its prescribed
clock-and-resolution step, and generate the remaining native execution from
its actual kernels. Future honest choices on this native suffix need not agree with
`s_w(a)`: they may see `bottom` where the counterfactual source continuation
reveals the original committed value. Integrating this normalized suffix
preserves the native-prefix marginal and gives the correct complete native
marginal. Let `X` be its program outcome, retaining the native execution in
the joint record as well.

The complete source marginal remains its ordinary source law. It is not
restarted or conditioned by choosing a new source policy at the timeout.
Every source-site registration fixed before `h`, including speculative
registrations, is retained in `s_w(a)`. There is no claim of post-timeout
private binding equality.

The actual suffix attachment is checked by
`MessageApplication.tracePolicies_prefix_last_law`: a stopped prefix of length
`k` resumes the original policies on `schedule.drop k` from its last complete
state, including all private and environment histories. In particular, the
first-timeout snapshot already includes the clock transition that produced it;
resumption does not repeat that transition. `SealedCompilation.extractedSourceCoupling`
uses this identity, and its source and native marginals and joint stopped-prefix/
final-native law are checked. `exists_randomized_source_coupling` averages these
couplings using a joint finite predrawing of the focal and environment responses.
Both native policies can be randomized, and the mixture may depend on the
opponent profile.
`extractedSourceCoupling_clear` proves pointwise that a timeout-free final state
is the full replay of the retained source realization: timeout records cannot
be erased, so the cutoff retained the entire invocation list. If the native
program is complete as well, `extractedSourceCoupling_decode_of_complete_clear`
recovers exactly that realization through the native event decoder. Its
finite-mixture version is audited as `Vegas.Paper.pending_normal_completion`.
The proof uses the actual binding invariant and retained registrations, rather
than deriving outcome equality from marginal identities. The round driver
below separately establishes completion. Post-timeout settlement identification
still requires a program-outcome argument.

Finally average over `w`. If `mu` is the distribution of `tau_w`, this gives
a joint law `(X,Y,B,H)` with:

- the exact resolving-runtime outcome law as its `X` marginal;
- `law(Y) = sum_tau mu(tau) law(S(sigma_-i,tau))`;
- equal program outcomes on `not B`;
- compatibility of the retained source assignment with every locked source
  choice and public field before the first resolution.

The source mixture is sampled independently of honest private draws. For
this fragment the extraction ignores the numerical honest kernels entirely;
with `D_i,E` fixed, the same predraw construction can be taken over all
honest assignments. Thus the mixture can be uniform over opponent profiles.

### 5.5 Honest outcome law

For the all-compiled profile, predraw only `E`; retain every player's source
kernel in the source law. The same cylinder and mass argument applies with
no focal extraction. The service lemma rules out timeouts for every such
profile, including profiles that honestly commit `bottom`. Every first
registration samples exactly once at the correct declared input, and every
reveal publishes that registered value. Therefore

```text
law(R_E(C(sigma))) = law(S(sigma)).                            (4)
```

This is a separate identification within the same coupling construction.
An arbitrary-deviation mixture alone would not prove (4). Finite default
termination is also insufficient: an unpolled source decision can resolve by
timeout, and the extracted policy uses a fallback at an unregistered site.
The honest-law proof must identify the actual registration kernels with the
original source profile, under the service guarantee excluding honest timeouts.

## 6. The precise incentive premise and strategic theorem

Let `J` describe the deviator's local information at the first timeout:
its observations and remembered commands, without unopened opponents' values
or an omniscient future random tape. Use the joint law constructed above.
This is the first-timeout checkpoint, which can follow the player's last
opportunity to avert timeout. It need not coincide with a decision point.
For each supported stopping information value `j`, require

```text
E[u_i(X) | B, J=j] + delta <= E[u_i(Y) | B, J=j], delta >= 0.  (5)
```

These are final program outcomes. The right side is the particular legal
source-completion law already constructed. The condition must hold for the
opponent profiles and replacements quantified by the desired preservation
theorem. It is not an assumption that a native deviation already has the
payoff of a source strategy.

A stronger sufficient condition can be checked without posterior beliefs.
For a first-timeout prefix `h`, let `K(h)` be all legal complete source
assignments matching its first registrations at source-owned handles and
its included public fields. This set is nonempty: values are typed, guards
are unrestricted, and authenticated openings agree with their registrations.

For every complete runtime continuation `z` after that prefix and every
`y in K(h)`, require the following, writing `O(z)` for the same program outcome
function evaluated on `z`'s terminal public environment:

```text
u_i(O(z)) + delta <= u_i(O(y)).                               (6)
```

Compatibility of the coupling makes (6) imply (5). This pointwise condition
is deliberately stronger than necessary. A nonvacuous class satisfying its
weak version has nonnegative source utilities and zero utility for a player
whenever one of its own published choices is `bottom`: under fair service
the first timeout defaults the deviator's own choice, so every runtime suffix
gives that deviator zero. These utilities are program/analysis conditions,
not features hard-coded into the runtime.

**End-to-end theorem for the specified model.** For every admitted program,
fair environment, source profile, focal player, and native deviation satisfying
(5), inequality (1) holds.

**Proof.** On `not B`, outcome utilities agree. On each `B and J=j`,
multiply (5) by its probability and sum. This gives

```text
E[u_i(X)] + delta Pr(B) <= E[u_i(Y)].
```

Substitute the constructed source-mixture marginal. This proves (1).
A finite mixture has a component attaining at least its average. Therefore
there is a single legal source deviation with utility at least that of the
native deviation; closure of the source class under mixtures is unnecessary.

If (5) with `delta=0` holds for every unilateral native replacement at a
source epsilon-Nash profile, every term in (1) is bounded by baseline source
utility plus epsilon. Apply (4) to the baseline: its compilation is
epsilon-Nash with the *same* error. Conversely, a profitable source deviation
compiles to a profitable native deviation by (4), proving reflection at
compiled profiles. There is no claimed bijection with all native equilibria.

If `delta>0` and `Pr(B)>0`, a component of the source mixture has utility
strictly larger than the native deviation. By (4) its compilation is a feasible
ex-ante improvement against the same compiled opponents. Hence that native
deviation is not a best response. This does not eliminate off-path quitting
instructions or concern arbitrary noncompiled opponent policies.

For an affected honest player `j != i`, the same coupling also transports a
source worst-case lower bound when its own continuation inequality is reversed:
`E[u_j(X) | B,J] >= E[u_j(Y) | B,J]`. Every component of the source mixture
then clears the lower bound, irrespective of the deviator's utility. The
deviator's inequality (5) alone does not provide that protection.

Coalitions, correlated-equilibrium recommendations, computational commitment
security, fees, and censorship are not covered by these unilateral ideal-model
conclusions.

## 7. Two checks on the argument

### Source strict dominance alone does not suffice

Use the following source, with no chance node:

```text
A commits Safe, Risky, or Quit
B commits H, T, or Quit
B reveals
A reveals
```

Both domains are `Option Bool`, with Quit as `none`. A's utility is:

| A | B: H | B: T | B: Quit |
| --- | ---: | ---: | ---: |
| Safe | 1 | 1 | 1 |
| Risky | 3 | -1 | 1 |
| Quit | 0 | 0 | 0 |

B receives 1 for H or T and 0 for Quit, regardless of A. Thus Safe strictly
dominates Quit for A, and H strictly dominates Quit for B, both against
every opponent strategy. At the source, Safe against B's fair H/T mixture
is Nash: A receives 1, Risky also yields 1, and B already receives its maximum.

In the specified resolving runtime, A can commit Risky, open after H, and
withhold after T. Its expected utility is `3/2 > 1`. The service can be
completely fair; A withholds its own message. Binding and the publication
barrier hold, and B is an ordinary strategic player using a randomized policy.

On T, the locked source continuation pays -1 while the runtime's programmed
Quit settlement pays 0. Condition (5) fails. The source's dominating Safe
action cannot replace Risky after the commitment is locked. This gives an
impossibility for a universal preservation theorem based only on ordinary
source quit dominance, even in the nullable unrestricted-guard fragment.

### A pending disclosure can be correlated with a still-hidden value

Consider:

```text
A commits X, uniformly in {0,1}
B commits b0
A commits Y, equal to X with probability 3/4
A reveals Y
B commits b1
A reveals X
B reveals b0 and b1
```

A's joint law is `P(0,0)=P(1,1)=3/8` and
`P(0,1)=P(1,0)=1/8`. Pending Y can be delivered to B before inclusion, and
E may use its value to choose service order. Conditional on Y, the still-hidden
X equals Y with probability 3/4. The scheduler's signal is not unconditionally
independent of X.

Nevertheless b0 is already locked before Y can be submitted, and Y belongs
to the source view at b1. Replay at b1 can therefore use Y without obtaining X.
The joint source law (2) retains the correlation; independently resampling X
after observing Y would give the wrong coupling.

## 8. Repository obligations and the next proof iteration

The mathematical model above supplies operational resolution rules and a
coupling construction. Its theorem does not assume deviation simulation as
an input. It still needs independent mathematical scrutiny and mechanization.

The current repository has:

- the checked written-source to declared-read-graph strategic correspondence;
- the actual sealed source-policy translation, own-history cache invariant,
  and local source-kernel law;
- exact value-substituted replay cylinders for bounded untimed executions and
  arbitrarily stopped resolving executions; the latter's probability theorem
  allows any joint honest-assignment law, including correlated coordinates;
- local knowledge-indexed native hiding and the compiled submission barrier;
- a whole-prefix registration read bound for the resolving runtime:
  `SealedFragment.resolvingBindingLaw_read_bound` allows arbitrary randomized
  native deviator and full-pool environment policies, and compares assigned
  honest values agreeing at source-earlier disclosures;
- a fixed-response resolving replay and its causal action extraction, with one
  native response pair shared across all source decisions;
- `SealedCompilation.extractedSourcePolicy`, a legal written-source policy
  reading the corresponding earlier public fields, and its exact local
  registration law under matching disclosure inputs;
- its actual complete source law with unchanged opponents,
  `SealedCompilation.extractedSourceRun_source`, and focal-choice consistency
  at every supported terminal realization;
- exact source-restriction likelihood identities and native stopped-trace
  factorization; the reference profile constructed from occupied honest slots
  reproduces the full recorded prefix, with original-kernel agreement throughout
  its pre-timeout reference support;
- exact equivalence of the written-source restriction event and native replay
  cylinder, and the compiler-specific source cylinder probability as an
  expectation of original-choice likelihood under the normalized reference law;
- constancy of that likelihood across the complete reference law, giving an
  explicit source cylinder product of original native registration probabilities;
- equality with the original native invocation product and the complete native
  prefix law through first timeout, including pending traffic, for fixed
  deterministic focal and environment responses;
- exact attachment of the actual post-timeout native continuation, preserving
  both the ordinary source marginal and the joint stopped-prefix/final-native law;
- trace-preserving predrawing of both focal and environment responses and the
  resulting source/native coupling mixture for arbitrary randomized unilateral
  replacements and randomized environments, with unchanged opponent kernels;
- pointwise identification of a completed, timeout-free coupled native run
  with the retained source realization under event decoding, also for mixtures;
- retention of all focal source-owned registrations at a common first-timeout
  snapshot, including speculative registrations;
- private-registration provenance and agreement of all players' source-owned
  slots at that snapshot; agreement of included openings with complete source
  values at every selected pre-timeout replay checkpoint;
- transport of successful local reads and fresh registration kernels to the
  complete source under an explicit own-cache/service agreement premise;
- own-cache/service agreement throughout arbitrary resolving-runtime policy
  runs, including retries and execution after timeout;
- per-node readiness timestamps, nullable resolution, and continued native
  execution without overwriting the private service;
- a shared-runner round model separating adaptive wire scheduling from the
  fixed clock boundary, with exactly one clock unit per round proved;
- private-binding persistence under arbitrary resolving-runtime policy runs,
  and exact untimed validator/event projection before the first timeout;
- compiled resolving policies using the same sample-once command generation,
  with exact before-timeout policy agreement and no cleartext commitments;
- a checked multistage-source regression continuing after a missing commitment
  or opening, while retaining existing private values and reading public defaults;
- a checked-source regression whose missing commitments resolve to the public
  values of a legal written-source execution;
- generic utility-based Nash transport;
- a fixed-clock round-driver termination bound of `n * (window + 1)` for
  enabled backward-dependency programs, instantiated for every compiled sealed
  fragment from canonical initialization under arbitrary player and wire policies;
- exact full-state identification of the early-stopping round driver with a
  block-boundary readout of the shared invocation trace, and the resulting
  source-mixture/native-round coupling for randomized focal and wire policies.

The registration read bound is checked over the actual shared policy runner,
including clock transitions and rejection receipts. The paired execution
relation carries the before-timeout binding invariant established under
arbitrary native traffic. It cuts off at the focal registration or first
timeout; the latter snapshot follows the tick, which leaves private service
values unchanged. This gives the required equality of registration laws under
changes to hidden future assignments. The deterministic replay function uses
this result to fill undisclosed assignment coordinates with a fixed fallback.
Compiler coverage of earlier public bindings turns that function into an
ordinary declared-read graph policy; the exact graph-policy roundtrip supplies
its written-source policy. For each supported complete source realization,
`disclosureInputs_eq_nodeValues` derives its disclosure-input agreement from
the graph's reveal semantics. `extractedSourceRun_consistent` then identifies
every focal choice with replay's extracted registration. These results use
the actual source law, not a postulated assignment distribution.
`extractedSourceRun_locked` retains all focal registrations at the same
first-timeout snapshot. That snapshot is after the tick, which preserves
private service values but may have defaulted public fields. Agreement with
the pre-resolution public prefix is checked by `extractedSourceRun_opened`:
selecting any checkpoint within the stopped replay retains actual supported
execution on both sides, so its registrations persist to the common cutoff.
The before-timeout binding invariant identifies its included openings with
those registrations. No equality is asserted for public timeout defaults.
`commitCommand_source_kernel` identifies successful local kernel inputs under
own-cache/service agreement. The checked
`SealedResolution.RegistrationMemory.runPolicies` supplies that invariant on
resolving runs, and `eventHistory_cache` supplies its projected-history form.
`extractedSourceRun_registration_kernel` applies it at every selected pre-timeout
replay checkpoint. An actual honest registration supplies its selected site,
fresh cache, and successful reads; the original compiled policy then has exactly
the source kernel at that realization's declared inputs. The theorem does not
assume cache correctness, read availability, or equality of source/native inputs.
For the finite-sum calculation, kernel constancy must cover the entire assignment
cylinder, including assignments with zero mass under the original honest profile.
`assignmentRealization` realizes every assignment using deterministic honest
source policies while retaining the same extracted focal policy. Its honest
values equal the assignment, and its entire native replay is unchanged.
`assignmentRealization_registration_kernel` compares any original source policy's
kernel at those source inputs, without requiring the assignment to have positive
probability under that policy. The regression exhibits a realized nullable quit
whose probability is zero under the compared non-quitting policy.
The general source factorization, restriction likelihood and summation laws,
and native stopped-trace factorization are checked. The compiler constructs the
reference restriction, proves exact prefix replay for its supported source
realizations, and compares each original source kernel at their recorded native
inputs. The restriction event is exactly the replay cylinder on the original
source law, and its probability is the expected original-choice likelihood under
the restricted reference source law. That likelihood is proved constant, with
one factor per source decision and unit factors for focal or unoccupied slots.
`replay_registration_factor` derives the same local invariants at each actual
invocation from its supported prefix and suffix. The source decision index is
duplicate-free; native write-once registration counts each occupied honest slot
once. `replay_prefix_prob_eq_product` and the normalized-source support argument
close the fixed-response native marginal in `extractedSourceRun_native_prefix_law`.
`extractedSourceCoupling_prefix_native` attaches the original suffix using the
retained state and histories, preserving the joint stopped-prefix/full-trace
law; `exists_randomized_source_coupling` lifts that law to randomized focal
and environment policies.
`Vegas.Paper.pending_randomized_source_coupling`
audits the joint law and both marginals by direct delegation.
`MessageApplication.RoundDriver.runRounds_eq_tracePolicies` identifies the actual round
driver with the first complete block-boundary snapshot of that trace. The
periodic environment performs wire actions at its service opportunities and
the mandatory clock command at the boundary, using its own history length to
select the phase. No memory is reset and no snapshot is given to a player.
`exists_randomized_round_source_coupling` applies this readout to the same
constructed coupling. The native marginal includes exactly the stopped
histories, pool, receipts, and application state; the source marginal retains
the same mixture of source deviations. Selecting the trace's final snapshot
would be wrong for this purpose: later clock calls and histories need not
freeze after application completion.
`mixtureRoundSourceCoupling_decode_of_complete_clear` proves normal-completion
agreement at the selected boundary. A supported
prefix supplies its binding invariant; a supported suffix preserves occupied
registrations and keeps the completed event log timeout-free. The retained
source realization therefore agrees with the selected native decoding, not
only with the final snapshot of the longer trace. No equality between a
timeout default and a private registered value is used.
The fallback is only source-policy totalization, not an identification of
runtime timeout with a source action.

The operational service accounting in `Interaction.SealedResolutionService`
permits messages to remain pending across player polls.
`round_pending_bound` counts all arrivals, including replays and malformed
submissions, and subtracts reserved inclusion opportunities. The block theorem
`runRounds_complete_or_pending_empty` permits unrestricted earlier wire phases:
enough reserved capacity in the final phase drains the block's arrivals unless
the application has already completed. `reserveInclusion` witnesses the local
service predicate while retaining the supplied adaptive wire policy at every
unreserved opportunity. A two-round regression checks an actual player reaction
to a delivered packet while the ledger is still empty. Queue clearance does
not itself prove acceptance or exclude honest timeouts.

`SealedResolution.EventInvariant` is preserved by arbitrary native policy
execution, including timeout resolution. Ordinary commit completion supplies
its canonical accepted handle and occupied private slot; every completed reveal
supplies a public opening, including defaulted reveals. Combined with retained
registration memory, the compiler theorem
`SealedFragment.resolvedPlayerStore_reads_of_ready` proves that every declared
read of a ready commitment is available after defaults. Its proof uses source
read provenance and the actual local-store reconstruction, without a decoded
post-timeout source configuration. An own timed-out commitment retains its
cached value when present and supplies the configured null otherwise. Public
reveal fields and initially visible inputs remain readable. This is a
read-availability result, not equality with the locked source continuation.

`SealedResolution.PublicState.ResolutionClosed` records automatic propagation:
a ready reveal of a timed-out producer is already completed. A full ordered
refresh establishes this invariant, and arbitrary native policy execution
preserves it. The compiler discharges the ordering premises from graph
well-formedness. Together with read availability, this proves
`SealedFragment.resolvingPolicy_progress_of_ready`: every supported command
when an owned node is ready and unfinished registers a fresh choice, submits
an occupied commitment, or opens its cached value. The theorem retains the
exact finite selected node, its readiness, and its index bound by the ready
target. It does not assume that successive polls select the same node.
`resolvingPolicy_registration_fresh` and `runPolicies_no_reregistration`
establish the one-registration charge: an emitted registration uses an empty
native slot, and arbitrary subsequent execution cannot make the compiled
policy register an occupied slot again.

`includePending_commitment_completed` and `includePending_opening_completed`
prove that including the corresponding canonical pending envelope completes
its node when its private slot and public prerequisites are ready. Already
completed nodes remain completed when a late message is rejected. These are
local inclusion laws. `runPolicies_commitment_pendingOrCompleted` and
`runPolicies_opening_pendingOrCompleted` retain the exact pending envelope
and its readiness under arbitrary intervening commands unless its node
completes. Queue drainage therefore implies completion of that ready site.
`runRounds_ready_commitment_completed` and
`runRounds_ready_opening_completed` combine this invariant with delayed
reserved capacity in the actual stopped round driver. They do not assume
acceptance and permit player reactions before inclusion. Completion may still
be through timeout; the phase count and clock comparison distinguish that
case for compiled players. The checked source regression
continues to its next commitment after earlier defaults and includes that
commitment and its opening through the actual pending-message interface.

The finite phase count is checked over adjacent snapshots of the shared runner.
`tracePolicies_drop_support`, `tracePolicies_between`, and
`tracePolicies_drop_invoke` supply the actual invocation prefixes, intervals,
and executed steps without resetting policy memory. `RegistrationAt` records
an executed compiled registration, and `registrationAt_unique` rules out two
different positions for the same source slot. `SubmissionAt` records a
canonical submission from an unfinished ready site. Its private binding and
accepted producer are derived from the compiled phase and native invariants;
queue drainage completes the site under arbitrary intervening policies.

`submission_count_le` bounds a site's designated submission polls by `b+1`.
The service premise gives an actual checkpoint after the submission step and
no later than the poll in round `r+b+1`, where the queue is empty or the whole
application is complete. An excess later submission would require the site
to be unfinished after that checkpoint, contradicting completion persistence.
Thus the completion alternative cannot discharge missed service retroactively.
`ready_poll_count_le` sums registration and submission charges and gives the
coarse bound `(d+1)*(b+2)` through target index `d`. Other players' progress may
change the least ready selector; it need not remain constant. A concrete
checked-source trace witnesses a real registration after earlier defaults.

`completed_by_poll` concludes completion **before the last poll** of an
interval exceeding that budget. This endpoint matters: using the next round's
poll would unnecessarily spend another unit of the timeout window.
`SealedResolution.PublicState.ReadySound` derives prerequisite completion from
a recorded timestamp. `DeadlineSound` records the retained timestamp and
elapsed clock bound of every actual timeout. Both invariants hold throughout
arbitrary native policy runs; newly created timestamps equal the actual
invocation's resulting clock. Concrete tests check both a real elapsed timeout
and an inclusion that makes a dependent rule newly ready.

`SealedFragment.no_timeout_of_poll_service` combines these facts: if enough
actual compiled-player polls receive bounded service and their last pre-state
is before the target's recorded deadline, that target never times out at any
later checkpoint. Later arbitrary traffic cannot append a timeout for an
already completed site whose timeout record is clear. No absence of earlier
defaults or acceptance of honest submissions is assumed. Its per-trace polling
and service premises are instantiated uniformly by the periodic round results:

- `tracePolicies_periodic_pending_empty` maintains empty queues at all
  period boundaries, including the backlog invariant between successive drains.
- `tracePolicies_periodic_service` supplies a real queue-drain checkpoint
  within one period of every roster poll.
- `periodicFinalReservation_range_count` and
  `exists_periodicFinalReservation_service` witness the service class: reserve
  the last round of each period, with enough slots for the period's roster
  opportunities, and retain arbitrary adaptive wire choices elsewhere.
- `tracePolicies_poll_clock` identifies each actual pre-player snapshot's
  clock. `runPolicies_firstReady?_of_lt_clock` recovers an already-past
  readiness timestamp at that snapshot; it cannot be created retroactively.
- `SealedFragment.tracePolicies_no_timeout` derives timeout exclusion from
  roster coverage, capacity, and the window. `runRounds_no_timeout` transports
  it to the actual early-stopping readout, retaining all histories and traffic.
- `runRounds_timeout_owner` identifies every failed site's source owner and
  proves that it lies outside the set of roster-covered compiled players.
  This permits arbitrary replacements outside that set; it is an operational
  statement, not a coalition equilibrium theorem.
- `runRounds_timeouts_eq_nil` excludes all operational defaults at an
  all-compiled profile. The multistage checked-source regression uses arbitrary
  original source kernels and arbitrary unreserved wire policies, a two-round
  service period, and a sufficient window. It proves that a completed
  execution with an empty timeout record exists, including for kernels that
  choose source-level null values.

For period `b+1`, the coarse sufficient window is `n*(b+2)+2`. These statements
do not assume immediate inclusion: messages can remain pending across player
calls. The finite trace horizon used by the periodic proof is a multiple of
the period. Choosing it large enough supplies termination as well as service.
The all-compiled probability law uses a separate all-player calculation.
`WFProgram.sourceRealization` retains the original source profile in the
canonical graph execution, with its exact written-source law.
`resolvingAssignedReplay` is the existing native runner with every choice
fixed by that realization; it is proof data, not another runtime. Selected-owner
registration restrictions characterize its cylinders, and
`sourceRealization_replay_prob_eq_product` counts every original source draw.
`sourceRealization_native_prefix_law` identifies the same cylinder product
with the actual native prefix law through first timeout.

For honest play only the environment is predrawn. Its response mixture retains
the same original source marginal in every term. Under actual timeout
exclusion, `exists_honest_replay_mixture` identifies the full native trace law.
`exists_honest_round_source_coupling` then has the original written-source
denotation as its source marginal and the actual early-stopping driver as its
native marginal. Every supported pair completes without timeout and native
event decoding recovers its retained source realization. Roster coverage,
periodic capacity, the sufficient window, and a whole-period horizon at least
`n*(window+1)` discharge completion and timeout exclusion; these are not
assumed in the coupling's conclusion. The checked multistage regression
instantiates all of these premises for arbitrary original source kernels and
arbitrary unreserved wire policies. This is honest outcome preservation, not
an equilibrium theorem.

The concrete strategic edge is
`SealedCompilation.RoundModel.utilitySimulation`. `RoundModel.game` is the
actual driver with unrestricted native player policies and a fixed adaptive
randomized wire policy. `Timely` packages the service, roster, window, and
whole-period hypotheses above. `NormalUtilityAgreement` requires equal utility
on completed, invariant-respecting native states decoding to a terminal source
configuration. Source and native utilities remain separate parameters.

For the checked sufficient condition, each player's entire native terminal
utility is at most `b_i` when any of its own commitments or reveals times out,
and every source outcome gives it at least `b_i`. Timely service proves that
all timeouts under a unilateral replacement belong to the deviator. Normal
branches use exact decoding; timeout branches use the cap. Finite averaging
then yields one legal source deviation with at least the native deviation's
utility. `RoundModel.isεNash_iff`, audited as
`Vegas.Paper.pending_round_approximate_nash_iff`, combines this bound with the
original honest law. A source lower bound `b_i + delta` yields the stronger
`RoundModel.deviation_utility_margin_bound`, audited as
`Vegas.Paper.pending_round_deviation_margin`: the source deviation's expected
utility exceeds the native one by at least `delta * Pr(timeout)`.

`RoundModel.stoppingCoupling` retains `(source configuration, J, native result)`.
`stoppingCoupling_information` identifies the joint `(J, native result)` law
with the actual shared-runner trace readout. On a timeout branch,
`SealedResolution.firstTimeout_before_roundReadout` places that checkpoint no
later than the selected round result; it is not taken from an unused suffix.
`stoppingCoupling_source` has the ordinary legal source-deviation mixture as
its marginal. `stoppingCoupling_locked` proves that every focal registration
in the actual local history is retained by its paired source configuration.
Neither the source policy nor its ex-ante mixture is selected using `J`.

`TimeoutCheckpointDominance` states (5) in unnormalized form, with separate
source and native utilities. `checkpoint_deviation_utility_bound` integrates
it and selects a legal source alternative attaining at least the mixture's
mean. `isεNash_iff_of_checkpointDominance` needs comparisons only against the
profile under analysis. `checkpointUtilitySimulation` provides a composable
certificate if they hold at every profile. `deviation_timeout_cost` bounds a
native deviation's payoff plus `delta * Pr(timeout)` by the compiled payoff
plus the source equilibrium error. These are checked compiler instances, not
just generic expectation lemmas.

The conditional hypothesis is a substantive remaining incentive obligation,
not a proof of program-specific quitting incentives. One sufficient test,
`timeoutCheckpointDominance_of_locked_cap`, separates a native cap `b(J)`
from a source lower bound `b(J)+delta` on **all** terminal reachable source
configurations satisfying `LockedAt`. That predicate uses only the focal
player's cached registrations, so it describes a larger set than `K(h)` in
(6). The source-bound premise does not mention the constructed coupling.
Compatibility with that larger set is checked by the compiler. Native
settlement still needs its independent cap proof.

The global cap is stronger than (5). It allows zero-valued own defaults with
nonnegative source utilities, but ordinary source quit dominance does not
imply it. The concrete four-node regression instantiates the actual driver and
Nash theorem with simple supplied utilities; it does not establish that those
utilities are the payout interpretation of that source. Independently,
`publicSealedStore_agrees` reconstructs typed public fields from public initial
data and opening events, ignoring opaque commitments; `publicPayout?` evaluates
the compiled payout on that public store. `publicPayout?_eq_source_of_terminal`
proves equality with the decoded written-source payout on normal runs.
`public_store_source_of_complete` identifies every completed public store with
the public projection of a legal source realization, including after defaults;
`publicPayout?_eq_source_of_complete` supplies an actual written-source
small-step execution and the same payout. `RoundModel.play_publicPayout_source`
instantiates completion and event provenance for every supported outcome of
the actual game, with arbitrary player and wire policies and no service
assumption. Source accounting supplies reveal uniqueness. The timeout
regression retains an accepted private `some true`, publishes `none` on expiry,
and evaluates a public-value-dependent source payout to `-3` rather than `7`.
The source settlement witness need not retain the locked private value and is
distinct from the source witness used in the incentive coupling.
`publicPayout_source_choice_of_timeout` also proves that a timeout owned by `i`
has a settlement witness recording a default at one of `i`'s actual source
decisions. The runtime settlement invariant makes every associated public
opening equal to that default; source accounting ensures reveal uniqueness.

For any valuation of the written payout, `VegasCore.QuitPayoutBound` asks that
every legal source outcome give `i` at least `b_i`, and every legal source
outcome recording `i`'s default give it at most `b_i`. On a native timeout,
the settlement witness gives the upper bound. The causal coupling's different,
commitment-preserving completion gives the lower bound. These pointwise bounds
imply (5) on every information fiber. Normal utility agreement follows from
the compiled payout evaluator and independent written-source execution.
`RoundModel.isεNash_iff_of_sourcePayoutBound` therefore has only the source
certificate and timely-service premises; no native utility inequality is
supplied. This uniform test is sufficient, not necessary, and stronger than
an ex-ante comparison of quitting with continuation.
The finite-fiber regression also verifies a conditional comparison
that holds despite pointwise comparison failing; the native-driver regression
instantiates the checkpoint-cap route and its positive timeout margin.

The remaining implementation work is specific:

1. Derive less restrictive, commitment-dependent or conditional source tests
   for (5). The uniform payout-bound theorem discharges one source-only case,
   not arbitrary source incentive analysis. A commitment-compatible lower
   bound must retain actual registered values, even when the public-settlement
   witness replaces them.
2. Extend admission and its proofs to further source features. The public
   settlement construction currently relies on unrestricted guards and a
   common value type, and the strategic coupling excludes samples.

No persistent role-bail rule, subgame handler, raw Ethereum transaction format,
or cryptographic verifier is silently included here. Further runtime features
must preserve the information and service facts used above, or establish their
appropriate weaker strategic bounds. Samples need a correctly realized chance
kernel and a publication barrier; heterogeneous values need typed codecs;
nontrivial guards need an account of invalid resolutions and legal
counterfactual continuations. These remain part of the larger compiler goal.
