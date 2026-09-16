# Public rejected openings and the exact theorem boundary

## The issue

An ideal EventGraph resolution retains two different facts:

- the owner's original action is a private `Bool`, preserved in its own action
  history; and
- the public output is the accepted `PublicationResult`, which is `failure`
  when deferred guards reject the proposed opening.

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

## What the checked sequential runtime does

The existing pending compiler does **not** expose this rejected candidate.
`Vegas.Pending.Policies.compileAt` computes
`acceptedProposal checks publicValues proposal` before constructing the wire
command. `disclosureCommand` sends an opening only for an accepted success and
sends the uniform `withhold` packet for failure. The original disclosure
Boolean remains in authenticated private command history. Consequently a
source action `true` whose guards reject it has the same public packet shape as
intentional withholding.

This normalization is a proved property of the checked compiler used in the
proof of `pendingGame_deviation_law`, not an external hypothesis of that
theorem. It is also not a consequence of ideal commitment soundness or of the
handler rejecting invalid data.

## Exact boundary for the EventGraph backend

The initial strong theorem should require the compiled unchanged-player
emission rule:

```text
before public submission, evaluate the prospective EventGraph resolve step;
if its accepted output is failure, emit one value-oblivious failure packet;
if it is success v, emit the typed verified opening of v.
```

The failure packet may be a canonical withholding command or an opaque packet
with a fixed public distribution. Its distribution must not depend on the raw
candidate, on whether the retained Boolean was `false` or rejected `true`, or
on which guard rejected it. The prescribed player's policy execution retains
the original Bool in its private history, so later own decisions retain exact
source recall. The simulation must relate the public transition to
`Config.step`; it must not require a ledger to store that private decision.

This restriction applies only to prescribed unchanged policies. The native
policy space still admits arbitrary focal packets, premature disclosures,
malformed data, silence, and replays. A focal player revealing its own hidden
value does not learn new information by doing so; its packets and the public
environment's reactions must remain in the deviation coupling.

Under this emission rule, the intended graph-relative statement can remain an
exact finite-mixture law after mapping terminal native executions to
`g.Outcome`. It should quantify over arbitrary focal policies and the admitted
public environment, while opponents use the normalized compiler. It must not
claim equality of transcripts or completion histories.

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
