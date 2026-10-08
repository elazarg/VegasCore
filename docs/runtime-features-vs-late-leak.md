# Runtime features versus the late-leak obstruction

The counterexample `G*` of the
[late-turn note](open-problem-late-turn-equilibria.md) shows that no
sequential equilibrium (SE) of a late-leak game realizes the outcome of its
intended game. The result is checked in Lean as
`Vegas.Paper.late_leak_not_preserved_when_deferral_pays`. `G*` is a finite
comparison game, and the actual asynchronous runtime gives its players more
options. This note asks whether any of these options creates a preserving SE.
The answer bears on the open question in the
[standard-runtime status](standard-runtime-se-status.md). If no option does,
then an actual-runtime embedding of `G*` would be a genuine counterexample
to SE preservation for the standard contract.

All verdicts below are exact. They come from
[`runtime_features_late_leak.py`](../scripts/experiments/runtime_features_late_leak.py),
which uses rational arithmetic, an assert for every claim, and negative
controls. They are not Lean theorems.

## Summary

At the parameters of `G*` (`R = 2`, `D = 6`, `c = 3`, `q = 99/100`), three
features restore preservation:

1. **An informed retry.** Suppose the builder settles the first late opening
   before the sender's next activation. A dropped opening is then known to be
   dropped, and resending is free because the escrow charge is already sunk.
   This gives every type the same large preference for the first late turn,
   so the leak no longer splits the types.
2. **Free talk that reaches the listener after a dropped opening that did not
   leak.** Each type steers the listener's failure answer its own way. As a
   result, no type strictly prefers the leaking turn.
3. **Listener jamming.** This needs a builder that lets a listener's packet
   addressed to the sender's event compete for inclusion, and a listener
   charge `c_L <= (3/5) q^2/(1+q)`. The listener then jams a pending opening,
   which makes the leaking turn unattractive for every type.

The following leave the obstruction intact. Each has an exact certificate,
and some hold only above a stated charge.

- A blind retry, which is a double send when the drop is not yet known. This
  holds for `c > (R(1 - q/2) + (1 - q)D)/(1 + q)`, which is `107/199` at
  `G*`. At `c = 0` the blind retry restores preservation instead.
- Free talk after the leaked drop.
- Charged raw signals before the first late turn.
- Charged raw signals at the first late turn when `c > R/2 + (1 - q)R/q`
  (`101/99` at `G*`) or `c < qR/2 - (1 - q)D`. A window between these bounds
  is undecided.
- Listener packets that are only messages, or jamming packets with
  `c_L > (3/5) q^2/(1+q)`.
- The contract constraints. The schedulers used here satisfy all of them.
- A symmetric stateless leak with probability `lambda` in
  `((1 - q)(R + 2(D + c))/(qR), 1)`, which is `(10/99, 1)` at `G*`.
- These options combined.

The verdicts depend on the builder and the network, not on the escrow rules
alone. A genuine counterexample must use a builder that does not reveal a
late opening's fate before the sender's next late activation. It must also
deny the sender a channel to the listener after the no-leak drop, and must
not let non-owner packets displace the owner's late opening. The analyzed
features permit such a builder, and it satisfies `AsyncContract`,
`AsyncTimely` and `BlindToLatePackets`.

## The model

The model has one sender `B` with type `(v, s)`, using the prior, payoffs and
listener of `G*`. There is one late slot, with deadline 2, reaction delay 0
and inclusion bound 1. The commands, in order:

- clock 0: `B` is activated at the protected turn `P`, followed by the
  protected inclusion step;
- clock 1: `B` is activated at `L1`, then the listener `A` is activated. `A`
  only observes, because its answer event becomes ready only once the reveal
  completes. Under T1 an inclusion step follows;
- `B` is activated at `L2`, followed by the final inclusion step, optionally
  followed by a `post` activation of `B`;
- clock 2: the reveal expires and `A` answers.

**Builders.** Both builders are blind to late packets. The coin of a sole
late owner opening is content-blind with probability `q`.

- **T1** can include a late packet only at the first inclusion step after it
  was sent. The `L1` result is therefore known at `L2`, and an `L1` opening
  that was not included is dropped.
- **T2** has one inclusion step after `L2`.

If several late packets are fresh at one step, blindness forces the Luce law:
each packet has weight `q/(1 - q)` against weight 1 for no inclusion. Two
fresh openings therefore succeed with probability `2q/(1 + q)`.

**Packets and charges.** Each activation emits at most one packet. A packet
without an accepting receipt is forbidden. This covers a dropped opening, an
extra opening and any raw signal. The audit charges the owner `c` at most
once, and the failure forfeit is `D`. The listener pays c_L for its own raw
packet.

**Leak.** As in `G*`, the listener's observe-only activation shows a pending
`L1` opening and nothing else. A variant uses a stateless symmetric rule
instead, described in the last feature section.

**Method.** The check is Kreps-Wilson consistency. Fully mixed families are
polynomials in `eps` with tremble rates that may depend on the type and the
node. Sequential rationality is checked by one-shot deviations at every
information set; the game has perfect recall. The on-path law must equal the
intended one: every type opens at `P` and the listener plays the safe answer
`m`.

Positive verdicts are explicit assessments that pass this check.

Negative verdicts combine a reduction certificate with the four steps of the
`G*` argument. The certificate has two parts:

- **Extra options.** Every extra sender option below a silent deferral must be
  either
  - strictly dominated by a core plan for every listener behaviour, checked by
    bounds that relax information sets or by exact vertex enumeration where
    sites are shared; or
  - payoff-equivalent through sites where the listener's answer is pinned.
    For example, after a failure in which `v` is known, the answer f(v) is
    strictly best at every belief.
- **The core is `G*`.** At every pure listener behaviour, the values of the
  four core plans (open at `P`, `L1`, `L2`, or never) equal those of the
  independent encoding of `G*` in
  [`late_turn_search.py`](../scripts/experiments/late_turn_search.py). The
  values are multi-affine in the listener's behaviour, so agreement at the
  vertices proves the identity everywhere.

Given the certificate, the `G*` argument runs in the subtree after a silent
deferral, with arbitrary reach weights. The steps are: one reward direction,
opposite strict preferences, a face of the simplex by the cross ratio, then a
guess and a profitable deferral. Some features need a variant of these steps;
each variant's premises are asserted.

As negative controls, the uniform assessment is rejected in `G*` itself, and
every positive construction fails once its feature is removed. A tilted
completion of the retry construction is also rejected.

## The features

### 1. Retries

**Informed (T1).** After a known `L1` drop, the charge is sunk and a retry at
`L2` succeeds with probability `q`. Write `F_k` and `F_0` for a type's value
at the failure site where `v` is known and where it is unknown. For every
type,

```
V(L1) - V(L2) = (1-q)[q(D + R/2) + (1-q)F_k - F_0]
              >= (1-q)(q(D + R/2) - R) > 0
```

when the listener plays `m` after every success. At `G*` this is
`0.0493 > 0`, and the leak-driven gap is only `(1 - q)R`. All types therefore
send at `L1`, and type-independent trembles keep the prior at every success
site. The assessment is:

- the listener plays `m` at every success site, f(v) when it knows `v`, and
  `f0` at the uninformative failure;
- the sender opens at `P`, at `L1`, retries, and opens at `L2` when it holds.

This assessment is an SE with the intended outcome at every grid point.

**Blind (T2).** The sender's only option is a double send: an `L1` opening,
then a second opening at `L2`. It succeeds with probability `2q/(1+q)`
instead of `q`, and the second packet is surely charged. Its largest gain
over sending only at `L1`, over all listener behaviours, is
`q(R(1 - q/2) + (1 - q)D)/(1 + q) - qc`.

- For `c > (R(1 - q/2) + (1 - q)D)/(1 + q)` the double send is strictly
  dominated, and the reduction gives no preserving SE. The script checks that
  the threshold is exact.
- At `c = 0`, `D = 6`, `q = 999/1000` a preserving SE exists, by the
  mechanism of the informed retry.
- Values of `c` in between were not decided.

### 2. Raw messages and the capped escrow

**Free talk after the leaked drop.** Under T1, after a dropped `L1` opening
the sender may talk at `L2` for free, since the charge is certain. The talk
reaches only sites where `v` is already known and f(v) is strictly best. It
is therefore payoff-equivalent to silence, and the reduction applies. This
holds for binary and ternary alphabets.

**Free talk after the no-leak drop restores preservation.** Give the sender a
`post` activation after the final inclusion step, with a message visible at
the listener's answer. The message is free once a charge is certain and
charged otherwise.

| Who | Prescribed behaviour |
| --- | --- |
| Types `(v, A)` | Hold at `L1`, open at `L2`. After a drop, send message 1. |
| Types `(v, B)` | Hold at `L1`, open at `L2`. After a drop, send message 0. |
| Types `(v, C)` | Hold at `L1`, open at `L2`. After a drop, report `v`. |
| Listener, no-leak failure after message 1 | Answer `f1`. |
| Listener, no-leak failure otherwise | Answer `f0`. |
| Listener, any success | Answer `m`. |

All trembles are type independent. The beliefs that support this are:

- after message 1, `P(v = 1) = 18/29 > 1/2`;
- after message 0, `P(v = 1) = 9/31`.

Every type's value at the no-leak failure is then at least its value at the
leaked failure. The `L1`-minus-`L2` gaps are `(0, -(1-q)R, 0)` in class
`v = 1` and `(-(1-q)R, 0, 0)` in class `v = 0`, so no type strictly prefers
`L1` and the cross-ratio step has nothing to act on. The assessment is a
verified SE at every grid point, with binary or ternary messages, and also
combined with blind retries and listener messages.

This variant leaves the dropped `L2` opening invisible while making later
talk visible. Under a propagation lag that would be inconsistent, because
the talk is sent after the `L2` opening. Under a lag that delivers the talk
before the answer, the dropped `L2` opening also arrives. That is the
complete-observation family, which is
[already preserving](actual-runtime-late-opening-analysis.md).

**Charged raw signals before any charge.** A raw signal is forbidden, so it
is charged `c` and uses up the cap.

- **At `P`, by deferring with a signal.** This never helps, for any
  `c >= 0`. The subtree after a silent deferral is a copy of `G*` with its
  own listener sites. The `G*` argument applies there with an arbitrary reach
  weight, and the profitable deviation stays inside that copy.
- **At `L1`, a signal instead of the opening, then `L2`.** The outcome
  depends on `c`:
  - For `c > R/2 + (1 - q)R/q` the signal plans are strictly dominated, and
    the reduction applies. The script checks that the threshold is exact.
  - For `c < qR/2 - (1 - q)D` a face-or-chain argument excludes preservation.
    Let `N_t` be the options a type uses with positive limit probability.
    - **Face case.** If two types' sets `N_t` are not nested, the cross ratio
      puts some success site on a face of the simplex, where the listener
      guesses. A face at a core site is the `G*` contradiction. At a signal
      site, the better of types `(v, A)` and `(v, B)` gains exactly when
      `c < qR/2 - (1 - q)D`, and the script checks this boundary.
    - **Chain case.** If the sets are nested, some option is optimal for all
      three types of a class. Comparing the types `C` with `A` or `B` shows
      that for `c > 0` this option is a core option. Equal costs at `c = 0`
      force the same conclusion. Both core options must then give the same
      answer at the uninformative failure as at the leaked failure, f(v).
      That cannot hold for both values of `v`.

    This chain-case argument is a paper argument; the script asserts its
    deviation step and thresholds.
  - Between the two bounds the variant is undecided. At `D = 6`,
    `q = 99/100` the undecided window is `[93/100, 101/99]`.

### 3. Contract constraints

The script's contract check enumerates explicit traces. These cover every raw sender
emission (nothing, an opening, or a signal at `P`, `L1` and `L2`, including
after completion), the listener's raw packet, and every scheduler outcome.
It checks the following for T1 and T2, with owner-only and author-blind
inclusion:

- `AsyncTimely` (`0 + 1 < 2`), `Opportunity`, and sole-identifier
  `ProtectedInclusion` with a strict clock. The clock-0 opening is included
  at the protected step. Clock-1 sends are late, since `1 + 1 >= 2`, so they
  carry no inclusion obligation.
- `CompletesPlay`.
- `BlindToLatePackets`: at every inclusion step, the erasure identity holds
  for every pending late packet.
- The listener answers only once the reveal has completed. Off path, its
  `L1`-`L2` activation is observe-only.
- The inclusion probabilities used in the game trees: `q`, `2q/(1+q)` under
  T2, `1 - (1-q)^2` under T1, and `q/(1+q)` against a jam.

These constraints add nothing to `G*`. Both schedulers reproduce its
information structure, so the obstruction is unchanged.

One constraint is not met by `G*`'s leak. The selective leak is not a
stateless `ObservationRule`. On the hold path, the dropped `L2` opening is
the same message as an `L1` opening: same sender, serial 0 and payload. It
is pending in the same pool at the listener's answer, yet `G*` hides it. See
[MessageNetwork](../Interaction/MessageNetwork.lean): the rule depends only
on the observer and the pending pool. The symmetric leak below is a valid
stateless rule.

### 4. Listener raw packets

**Messages.** These are packets the sender sees before `L2` but that never
affect inclusion. They do not matter. The listener's choice is the same at
every type of a class, so the core sites split by message, with a common,
type-independent factor. The averaging lemma holds: core plan values equal
the `G*` values at the listener's averaged behaviour, checked at all
vertices. Opening at `L2` beats never after every message. The cross ratio
then puts every success site of one turn on a face, so step 5 goes through.
The positive constructions survive as well: the listener stays quiet and the
sender ignores its packets.

**Jamming (author-blind builder).** A listener packet addressed to the
sender's event competes for inclusion under the Luce law. A jammed `L1`
opening succeeds with probability `q_J = q/(1+q)`. Consistency makes the
listener's beliefs equal at the jammed and the unjammed success sites, so
the gain from jamming is exactly

```
(q - q_J)(1 - s) - c_L,    s >= 2/5,
```

where `s` is the listener's value at those success sites. The script checks
this identity in T1 and T2.

- For `c_L <= (3/5) q^2/(1+q)`, which is `29403/99500 ≈ 0.2955` at `G*`, the
  listener jams a pending `L1` opening. Every type then strictly prefers `L2`.
  The assessment where everyone holds at `L1` and the listener plays `m` is an
  SE with the intended outcome. It is verified at `c_L = 0`, at half the
  threshold, and at the threshold, in T1 and T2.
- Above the threshold, jamming is strictly worse at every consistent
  assessment, and the message argument applies.

A builder that never includes non-owner packets for an owned event is also
blind, and it removes the jamming channel.

### A symmetric stateless leak

The runtime's observation rule can express the following leak. Each pending
opening is seen with probability `lambda` at every listener activation. Take
builder T2. A dropped `L1` opening is exposed twice, at the observe-only
activation and at the answer, so it is seen with probability
`1 - (1 - lambda)^2`. A dropped `L2` opening is seen with probability
`lambda`. The `L1`-minus-`L2` gap is the `G*` gap with `kappa` scaled by
`lambda(1 - lambda)`, checked as an identity at all vertices. The `G*` case
analysis therefore yields opposite strict preferences.

An `L1` success whose opening was not seen at the observe-only activation is
indistinguishable from an `L2` success, so the two share one site. The cross
ratio between the leaked-success site and this shared site still tends to
zero. If the face is at the shared site, deferring to `L2` pays as in `G*`.
If it is at the leaked-success site, deferring to `L1` pays exactly when
`lambda > (1 - q)(R + 2(D + c))/(qR)`. Hence there is no preserving SE for
`lambda` in `(10/99, 1)` at `G*`. At `lambda = 1` (complete observation) a
preserving SE is found, which serves as the positive control. The range
`lambda <= 10/99` is undecided, and the leak was not combined with the other
features.

## Parameter points

All points have `R = 2` and satisfy the hypothesis of the `G*` theorem. In
the table, "no" means no preserving SE (certified), "SE" means a verified
preserving SE, and "?" means undecided.

| D, c, q | informed retry | blind retry | talk, leaked drop | talk, post | L1 signals | listener messages | jam threshold | leak bound | all non-restoring combined |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 6, 3, 99/100 | SE | no | no | SE | no | no | 0.2955 | 10/99 | no |
| 6, 3, 999/1000 | SE | no | no | SE | no | no | 0.2996 | 10/999 | no |
| 6, 3, 9999/10000 | SE | no | no | SE | no | no | 0.29996 | 10/9999 | no |
| 12, 6, 999/1000 | SE | no | no | SE | no | no | 0.2996 | 19/999 | no |
| 24, 12, 9999/10000 | SE | no | no | SE | no | no | 0.29996 | 37/9999 | no |
| 12, 3, 99/100 | SE | no | no | SE | no | no | 0.2955 | 16/99 | no |
| 6, 1, 99/100 | SE | no | no | SE | ? (window) | no | 0.2955 | 8/99 | ? |
| 6, 0, 999/1000 | SE | SE | no | SE | no | no | 0.2996 | 7/999 | SE (blind retry) |

The combined column uses builder T2, no `post` activation, the blind retry,
signals at `P` and `L1`, and listener messages. With a restoring feature
added, verified SEs also exist at `G*`:

- the informed retry with signals, talk and listener messages;
- `post` talk with the blind retry and listener messages.

## What this implies for the open question

None of the four features defeats the obstruction by itself, provided it
takes a suitable form. An actual-runtime embedding of `G*` with these
features is a candidate genuine counterexample under the following
conditions:

- the builder decides late inclusions only after the sender's last late
  activation (T2);
- `c` exceeds `max((R(1 - q/2) + (1 - q)D)/(1 + q), R/2 + (1 - q)R/q)`, or
  `c < qR/2 - (1 - q)D` for the signals;
- the sender has no channel that reaches the listener after a dropped
  opening that did not leak;
- non-owner packets cannot displace the owner's late opening, or listener
  packets cost more than `(3/5) q^2/(1+q)`.

`G*`'s parameters meet all of these.

Two points remain before this becomes a counterexample:

- **The leak.** `G*`'s selective leak is not a stateless observation rule. A
  symmetric stateless leak with `lambda` above a small bound reproduces the
  obstruction under builder T2, so this gap is closed for the leak itself.
  The check is a finite comparison: it is not combined with the other
  features, and it is not in Lean.
- **Native branches not modeled here.** These are wrong-event and malformed
  packets, aliases, several listener activations, and a native embedding into
  the compiled source program with its typed readout, such as
  [CommittedResolutionService](../Vegas/Examples/CommittedResolutionService.lean).

The positive mechanisms show what a preservation theorem would have to use.
It could require a builder that reveals each late opening's fate before the
owner's next opportunity, which makes retries informed. Alternatively, it
could guarantee that public evidence of any dropped opening reaches every
later decision maker. A theorem stated for every blind builder with a finite
deposit cannot hold if the native embedding goes through.
