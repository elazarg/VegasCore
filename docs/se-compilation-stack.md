# Checked SE compilation stack

The [calendar capstone](../Vegas/Game/SourceServiceCompilation.lean) fixes the
native service, authentic partial audit and deposit before selecting a source
SE. It preserves the joint initial-parameter, public-result and realized-net-payoff
law in the bounded raw runtime. Its service is a fixed roster calendar.

The proof has two edges:

1. [SourceServiceEquilibrium](../Vegas/Game/SourceServiceEquilibrium.lean)
   constructs a retained native SE from an original source assessment, using
   source/traffic factorization, Bayes beliefs and local continuation comparisons.
2. [SourceServiceRawExtension](../Vegas/Game/SourceServiceRawExtension.lean)
   extends that assessment to bounded raw responses with actual audit and
   whole-continuation comparisons. One legal repair policy must work across the
   hidden histories of its information set.

[SourceServiceAudit](../Vegas/Game/SourceServiceAudit.lean) judges authentic
packet evidence against the final record and separately checks public binding
omissions. Packet monitoring can be partial. Positive conditional collection
and collectible collateral are backend assumptions, not consequences of
packet authenticity. Runtime utilities depend on initial parameters and public
results. Cryptographic and EVM realization require separate refinement proofs.

The [checklist](se-proof-checklist.md) validates this calendar chain.
The [asynchronous design and plan](se-schedule-generalization.md) states the
unchanged runtime semantics, concrete unresolved issues and general proof road.
The arbitrary-builder capstone and faithful operational watcher adapter are open.
