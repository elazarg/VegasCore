# Ideal commitment and readiness capabilities

The runtime uses immutable candidate meanings and authentic opening evidence.
A public binding handle does not disclose its private value. An opening must
match the accepted owned handle and the relevant source guards. Private inputs
are not fresh binding handles and cannot be opened through that interface.

[CommitmentCandidates](../Interaction/CommitmentCandidates.lean) owns the ideal
candidate catalogue. [EventCommitmentBinding](../Vegas/Pending/EventCommitmentBinding.lean)
connects accepted handles to source binding values. These are ideal semantic
interfaces; concrete hashing, signatures, hiding and binding need refinement.

The emitter also attaches causal readiness evidence. A sender can emit an early
claim, but cannot choose a valid credential for an event whose prerequisites
have not completed. The [final-record verdict](../Vegas/Pending/ReactiveSettledVerdict.lean)
checks that evidence without access to transmission time. Historical credential
validity is distinct from whether an event is currently ready.

A concrete realization must bind credentials to the session and event and make
them publicly verifiable after the prerequisite checkpoint. It must preserve
the modeled owner and immutable-body authenticity. A sender-written identifier
or client assertion alone does not establish that refinement.

Partial observation and accepted reporting are separate from authenticity.
The [SE plan](se-schedule-generalization.md) states their remaining operational
proof obligations. Neither ideal evidence nor a long reporting window implies
that a watcher learns every packet.
