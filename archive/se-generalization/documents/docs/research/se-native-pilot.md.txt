# Ordinary-source pilot for passive enforcement

## Theorem target and checked status

**Checked:** every SE of the fixed Vegas game below has an SE in the existing
bounded native runtime, preserving the joint law of initial secret, public
results and actual net payoff vector. The native game and charge are fixed
before choosing the source SE. One fixed playerwise policy translation preserves
every source SE: Bob's native policy depends only on his own source policy;
Alice's and Watcher's policies are fixed. See `compiled_source_equilibrium` in
[MonitoredGuessingCompilation](../../Vegas/Examples/MonitoredGuessing/Compilation.lean).
This mathematical translation uses classical choice for Bob's optimal off-path
completion; it is not an executable synthesis procedure.
This is forward preservation for one game, not reflection or a result for a
general Vegas source class or arbitrary blockchain service.

## Actual source program

[MonitoredGuessingGame](../../Vegas/Examples/MonitoredGuessing/Game.lean) defines three
principals: Alice, Bob and Watcher. Its ordinary `Setup` contains Alice's initial
commitment to a fair Boolean `x` and Bob's initial commitment to `true`, with
ordinary disclosure obligations. Watcher has no source action.

```text
reveal Bob's initial true commitment as guessResult;
reveal Alice's initial bit commitment as secretResult;
return correctness to Bob;
return correctness − 4·isFailure(secretResult) to Alice;
return 0 to Watcher.
```

Bob's guess is `isSuccess(guessResult)`: lawful withholding means `false` and
is unpunished. Correctness is one exactly when Alice successfully opens and her
bit equals that guess. These are literal integer payoff expressions. Checked
[source SE results](../../Vegas/Examples/MonitoredGuessing/SourceEquilibrium.lean)
show that every Boolean guess distribution `q` extends to a source SE, and every
source SE has Alice open at all final sites and the joint law fair bit × `q`.

Initialization uses `Vegas.SourceProgram.Setup.eventInputs` and production
`Vegas.EventGraphRuntime.State.initial`, including accepted initial handles. The theorem starts with
these ideal bindings; an earlier cryptographic commitment protocol, key sharing
and setup incentives are outside this model.

## Actual native service and report

[MonitoredGuessingNative](../../Vegas/Examples/MonitoredGuessing/Native.lean) uses the
existing compiled graph, reactive application and complete bounded raw menu.
The value alphabet is `{false, true, integer 0}` with one prepared slot per owner;
all bounded submissions, wrong event/type/value combinations, independent
evidence requests, silence and known-envelope replays remain available.

The 14-command service gives Alice one early response, Watcher one activation,
and a report-inclusion turn, followed by reserved Bob and Alice visits with
grant, response, inclusion, ticks and expiry. Watcher samples all pending IDs or
none with probability one half through the ordinary passive observation rule.
Its prescribed response replays the first observed Alice envelope. The wire
checks the public Watcher rebroadcast; it does not inspect the private sample.
Replay preserves Alice's authorship and original envelope identifier. Bob
observes all pending messages at his sole decision; Alice observes none.

The production public-event barrier blocks Alice's reveal before Bob's reveal.
Checked [prelude laws](../../Vegas/Examples/MonitoredGuessing/NativePrelude.lean)
show that every possible Alice/Watcher prelude packet is rejected on inclusion
and leaves the application unchanged. Ordinary final opening and withholding
remain accepted. The single prelude excludes delayed reporting after a lawful
event has settled; no historical packet-authoring timestamp is assumed.

## Enforcement and genuine sequential incentives

Alice incurs an additional terminal charge `D ≥ 2` when an Alice rejection
receipt exists. It is separate from the source's four-unit failure payoff.
Receipt persistence is proved; **collectibility is an explicit utility/backend
assumption, not an implemented escrow mechanism**. Withholding later cannot
erase an existing charge.

- [Monitoring](../../Vegas/Examples/MonitoredGuessing/NativeMonitoring.lean) gives
  rejection probability exactly one half for every raw initial submission.
- [Sanctions](../../Vegas/Examples/MonitoredGuessing/NativeSanctions.lean) bound its
  expected utility by `1 − D/2`, for arbitrary entire subsequent Alice policies.
- [Initial rationality](../../Vegas/Examples/MonitoredGuessing/NativeInitialRationality.lean)
  proves silence optimal at each private type, against whole-policy deviations.
- [Final rationality](../../Vegas/Examples/MonitoredGuessing/NativeResolutionFinal.lean)
  proves truthful opening optimal at every final native site, including those
  reached after malformed traffic and existing liability.
- [Receiver completion](../../Vegas/Examples/MonitoredGuessing/Assessment.lean)
  constructs one common fully mixed consistency sequence and makes Bob rational
  at every nonquiet site. Raw messages, report outcomes and receipts remain in
  his information; no quiet-or-authentic-bit partition is assumed.
- [Quiet receiver rationality](../../Vegas/Examples/MonitoredGuessing/NativeReceiverRationality.lean)
  covers every raw Bob deviation at the quiet site using its fair posterior.
- [Initialized laws](../../Vegas/Examples/MonitoredGuessing/NativeLaw.lean) match
  fair bit × `q`, public results and absence of extra charges under the prescribed
  Alice/Watcher policies and Bob's quiet response. The checked capstone includes
  actual net payoffs in this joint law.

Watcher is a genuine player with every raw deviation and zero utility at every
history. Reporting is rational by indifference. This supports an SE extension;
it does not guarantee reporting, uniqueness, coalition resistance or preservation
in every target equilibrium. The fixed playerwise translation chooses Bob's
off-path completion from his own source distribution `q`. The proof uses native
continuations directly; the finite disclosure experiment supplies intuition.

## Declared payoff tables and inferred charges

[MonitoredGuessingPayoffs](../../Vegas/Examples/MonitoredGuessing/Payoffs.lean)
replaces the literal return expressions by an arbitrary integer table over both
publication results and players. It checks the actual source returns and common
compiled operational graph. The production
[payoff transport](../../Vegas/EventGraph/PayoffTransport.lean) preserves adaptive
execution and public/player observations when changing a graph's settlement list.

[MonitoredGuessingPayoffInference](../../Vegas/Examples/MonitoredGuessing/PayoffInference.lean)
computes sender payoff extrema and calls the rational deposit checker with the
proved collection coefficient one half. The result deters every raw early
submission followed by any continuation policy or service plan; the original
sender table computes charge two.
[MonitoredGuessingPayoffLaw](../../Vegas/Examples/MonitoredGuessing/PayoffLaw.lean)
preserves the exact initialized type/result/net-payoff law under the prescribed
policies, including zero collected charge.

These table-parametric results do not assert SE for arbitrary returns. A table
can change Alice's incentive to open or Bob's optimal quiet guess. A family-wide
SE theorem additionally needs these incentive proofs and source-assessment
transport. It requires no new runtime representation. The general restriction
theorem also does not automatically subsume this native proof: its arbitrary-
continuation collection premise does not follow from a watcher's reporting by
indifference, and its source/target decision clocks must align.
