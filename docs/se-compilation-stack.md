# Checked SE compilation stack

The [calendar capstone](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/SourceServiceCompilation.lean) fixes the
native service, authentic partial audit and deposit before selecting a source
SE. It preserves the joint initial-parameter, public-result and realized-net-payoff
law in the bounded raw runtime. Its service is a fixed roster calendar.

The proof has two edges:

1. [SourceServiceEquilibrium](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/SourceServiceEquilibrium.lean)
   constructs a retained native SE from an original source assessment, using
   source/traffic factorization, Bayes beliefs and local continuation comparisons.
2. [SourceServiceRawExtension](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/SourceServiceRawExtension.lean)
   extends that assessment to bounded raw responses with actual audit and
   whole-continuation comparisons. One legal repair policy must work across the
   hidden histories of its information set.

[SourceServiceAudit](../Vegas/Game/SourceServiceAudit.lean) judges authentic
packet evidence against the final record and separately checks public binding
omissions. Packet monitoring can be partial. Positive conditional collection
and collectible collateral are backend assumptions, not consequences of
packet authenticity. Runtime utilities depend on initial parameters and public
results. Cryptographic and EVM realization require separate refinement proofs.

The [checklist](https://github.com/elazarg/VegasCore/blob/research-tree/docs/se-proof-checklist.md) validates this calendar chain.
The [asynchronous design and plan](se-schedule-generalization.md) states the
unchanged runtime semantics, concrete unresolved issues and general proof road.
General exact SE preservation under the existing asynchronous contract is
refuted by the [checked native obstruction](commit-reveal-research/native-se-obstruction.md).
The [protected timely execution theorem](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/SourceServiceReactiveLaw.lean)
and [authentic settled-audit theorem](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/SourceServiceReactiveAudit.lean)
preserve the initialized joint source-state and realized net-payoff law in
sequential and concurrent-binding modes, for every authentic standard audit
sampler and deposit. Equilibrium preservation requires separate evidence.
A faithful operational watcher adapter remains open.
