# Smallest ordinary-source pilot for passive enforcement

## Proposed theorem and scope

Prove forward SE preservation for a fixed two-decision Vegas game in the
existing bounded runtime with a strategic zero-payoff watcher. Quantify over
every source SE with one playerwise translation; preserve initial secret,
public results and net-payoff laws. All native bridges below remain unproved.

## Actual source program

Use three principals: Alice, Bob and Watcher. The `Setup` context contains an
initial Alice commitment to a fair Boolean `x` and Bob commitment to `true`,
both with ordinary disclosure obligations. Watcher has no source action.

```text
reveal Bob's initial true commitment as guessResult;
reveal Alice's initial bit commitment as secretResult;
return correctness to Bob;
return correctness − 4·isFailure(secretResult) to Alice.
```

Decode Bob's guess as `isSuccess(guessResult)`: withholding means `false` and
is never punished. Correctness is one exactly when Alice successfully opens
and her bit equals that guess; otherwise zero. These are literal public-result
integer payoff expressions. Watcher's utility is identically zero.

Reuse the setup of [SequentialValidationSource](../../VegasTests/SequentialValidationSource.lean)
and the payoff expressions of
[SelectiveAssociationGame](../../VegasTests/SelectiveAssociationGame.lean).
The setup is part of the theorem: compile its actual initial law through
`Setup.eventInputs` and `Vegas.EventGraphRuntime.State.initial`, including accepted initial handles.
Manually installed native bindings alone do not give an initialized result.
An earlier cryptographic commitment protocol is outside this setup model.

## Native service, observation and report

Instantiate the existing raw bounded menus, including wrong types, prepared
candidates, arbitrary evidence requests, malformed calls, silence and replay.
Use the actual compiled two-event graph. Before ordinary reserved service:
activate Alice once; activate Watcher once; include a reported envelope if any.
Then visit Bob's event and Alice's event using grant, owner response, protected
inclusion, ticks and expiry as in [SelectiveAssociationNative](../../VegasTests/SelectiveAssociationNative.lean).
No further Watcher activation or Alice prelude is available. Watcher samples
pending traffic through the ordinary observation interface.
Its prescribed policy replays an observed Alice envelope, otherwise stays
silent. [`MessageNetwork.replay`](../../Interaction/MessageNetwork.lean) copies
the original envelope and identifier: Alice remains its author; Watcher is
the separately recorded broadcaster. The service must gate report inclusion
on that actual public Watcher rebroadcast, not inspect all pending traffic as
though Watcher had observed it. Source-compatible Watcher traffic is silent.

Candidate useful gate: before Bob's publication, Alice's publication is blocked,
and Alice cannot execute Bob's event. Prove every reported Alice packet is then
rejected. Its existing `(messageId, false)` receipt supplies accountable report
material without a private arrival timestamp. Prove ordinary final Alice
opening and withholding packets are accepted. A receipt-based sanction can
then distinguish the reported early attempt from these legal source choices.
No late Watcher activation can manufacture rejection of a lawful settled packet.

## Charge and watcher assumptions

Specify an additional native terminal debit `D ≥ 0` for Alice when an included
Alice envelope has a rejection receipt. It is separate from the source's
four-unit opening-failure penalty. Collection cannot depend on Alice's later
successful opening: existing liability remains if she withholds or times out.
The current application has receipts but no escrow debiting implementation;
prepaid, collectible receipt-based liability is an explicit backend assumption.

Require a sender-conditional lower bound `p > 0` for observation followed by
the prescribed timely report inclusion. Try `p·D ≥ 1`: after successful final
opening, correctness ranges from zero to one. This sufficiency bound still
needs its actual native continuation proof, including failed openings.
Watcher is a genuine player with all raw deviations and zero utility at every
history; reporting can be rational by indifference. This constructs one target
SE, not guaranteed reporting or preservation in every target equilibrium.

## Exact bridges and fatal shortcuts

1. **Source reduction:** prove Alice's final opening optimal at every source
   information set; characterize all source SE receiver laws `q`. For the fair
   prior every Boolean `q` is the candidate class. With other priors retain only
   prior-optimal `q`; generalization is secondary to closing the fair instance.
2. **Native terminal decisions:** classify every raw Bob response as true or
   false after actual inclusion/expiry; prove no third profitable result.
   Prove Alice's final opening optimal for net utility, including old liability
   and arbitrary preceding responses. It is not an automatic opening action.
3. **Information and consistency:** initial-bit certificates are authentic;
   unrelated certificates, claims and rejected packets are additional signals.
   Early report inclusion also informs Bob even though debit is terminal.
   Construct one common fully mixed sequence and prove Bob's posterior/optimal
   response for every resulting observation. The finite disclosure theorem's
   quiet-or-authentic-bit partition cannot simply be assumed for these raw menus.
4. **Sender and monitor:** prove report soundness, conditional collection and
   the full Alice prelude deviation bound; preserve all legitimate withholding.
5. **Compose:** connect actual source assessments, native information sites,
   consistent repaired responses and exact initialized/net-payoff laws to
   [DisclosureEnforcement](../../GameTheoryExtensions/Analysis/Protocol/DisclosureEnforcementEquilibrium.lean).
   Extra sender actions, raw observations and the third strategic player need
   explicit adapters. This first pilot does not require an ambient source.
