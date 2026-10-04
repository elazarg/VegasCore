# Public rejected openings and the exact theorem boundary

## The issue

An ideal EventGraph resolution retains two different facts:

- the owner's original action is a private `Bool`, preserved in its own action
  history; and
- the public output is the accepted `PublicationResult`, which is `failure`
  when guards reject the proposed opening.

If a public pending protocol broadcasts the raw proposed value before applying
those guards, its transcript contains strictly more semantic information than
the EventGraph output. This is not merely a different schedule or harmless
metadata. A later deviator can use the rejected value even though no source or
ideal-graph observation contains it.

## Minimal counterexample

Use Boolean payloads and three source commitments.

1. `B` commits a fair choice `x = b` under an unsatisfiable guard.
2. `B` chooses `true` when resolving `x`. The accepted result is failure for
   both values of `b`.
3. After that resolution, `A` commits `y`.
4. Using its retained own action history, `B` commits `z = b` under a valid
   guard.
5. The program resolves `y` and `z` successfully, publicly revealing both.

In the source and ideal EventGraph, `A` sees only failure at step 2. Before
choosing `y`, it has no information about `b`. A strategy chosen before the
run therefore cannot make `y = b` surely; neither can a finite mixture of such
strategies, because the mixture draw is independent of the later random choice
made by unchanged `B`.

In a protocol that publicly transmits the attempted opening of `x`, a native
replacement for `A` reads the rejected raw bit and chooses `y` equal to it.
The terminal public pair `(y, z)` then satisfies `y = z` with probability one.
No source-policy mixture has that law. The utility `1[y = z]` also gives native
value one and source value at most one half.

This yields an explicit Nash counterexample, not merely a law mismatch. Give
`B` constant utility and give `A` utility `1[y = z]`. At source, any fixed or
random successful guess by `A` has value one half, and no source deviation can
observe `b`, so the prescribed profile is Nash. In the raw-broadcast native
protocol, `A` deviates as above and obtains value one.

Thus exact unilateral backtranslation, arbitrary source-outcome guarantees,
and ordinary Nash preservation all fail for this protocol. A
failure-disincentive condition on `A` does not repair the problem: `A` did not
create the rejected failure and simply exploits information disclosed by the
unchanged player `B`. Repair would require a direct restriction on preferences
for using leaked information, which is not the intended source theorem.

The example needs no empty payload type and no clairvoyant scheduler. An
unsatisfiable guard is already part of the full source language.

## Compiled emission and the checked theorem

The prescribed pending-message policies prevalidate openings.
`Vegas.EventGraphRuntime.resolutionPayload` calls
`Vegas.EventGraph.EventCode.resolveOutput?` before constructing a public
payload. It sends an opening only for a successful result with an accepted
handle belonging to the player; otherwise it sends the canonical withholding
packet. The theorems `Vegas.EventGraphRuntime.resolutionSubmission_false` and
`Vegas.EventGraphRuntime.resolutionSubmission_rejected` check the two failure
cases. Both dependency modes use this policy compiler.

The emission rule is:

```text
before public submission, evaluate the prospective EventGraph resolve step;
if its accepted output is failure, emit one value-oblivious failure packet;
if it is success v, emit the typed verified opening of v.
```

The failure packet is independent of the raw candidate, of whether the
retained Boolean was false or rejected true, and of which guard rejected it.
The prescribed player's private command history retains the original Boolean,
so later own decisions retain source recall. The graph transition records the
accepted publication result separately from this private action. No ledger is
required to store the private decision.

This restriction applies only to prescribed unchanged policies. The native
policy space still admits arbitrary focal packets, premature disclosures,
malformed data, silence, and replays. A focal player revealing its own hidden
value does not learn new information by doing so; its packets and the public
environment's reactions must remain in the deviation coupling.

The checked theorem
`Vegas.SourceProgram.Setup.eventPendingGame_deviation_law` gives an exact
finite-mixture law for decoded terminal source states. It quantifies over
arbitrary focal policies and the concrete public service's wire and event-order
policies, with opponents using the prescribed compiler. Prevalidation is part
of this compiler, not an extra premise about arbitrary runtime policies.
The result concerns outcomes, not equality of transcripts or completion histories.
See the [pending-message proof](event-pending-deviation.md) and
[service model](event-service.md).

A host with public failed calldata does not by itself violate the contract:
the compiled policy can prevalidate and submit the canonical withholding
packet, so the raw candidate never becomes calldata. The counterexample applies
only when the host or protocol forces a prescribed raw candidate to be
broadcast before the compiler has the information or authority to normalize
it—for example, when validation is available only after mandatory raw
submission. Such a target requires a concealment layer that restores the
emission rule or a richer source game whose observations include attempted raw
values. A utility condition about failure alone is insufficient.

## Scheduling-only information

Opaque completion identities by themselves do not reproduce the
counterexample. Under public-barrier dependencies, simultaneously ready events
are foreign-owner binds, and their public completion metadata contains no bind
meaning. A public scheduler's randomness and its reactions to already public
source results can be jointly predrawn with the focal response before setup;
the resulting order signal is independent of hidden opponent meanings and can
be absorbed into the source-policy mixture.

Scheduling becomes a leak if the scheduler first observes a rejected raw
opponent value and then encodes it into order. For example, after `B`'s rejected
opening, it can choose whether `A` or another ready event completes next, and
`A` can read that order. This is the same raw-opening counterexample through an
indirect channel, not a scheduling-only obstruction. The coupling invariant
must therefore state that the scheduler-visible state before event selection
is independent of unchanged players' failed candidate meanings.
