# Ledger expansion design

A ledger realization is a future refinement of the native public-message
application, not part of its present semantics.

The ledger layer must make at least these facts explicit:

- transaction identity, sender authentication, and replay rules;
- pending submission, inclusion order, receipts, and finality;
- clock and deadline advancement;
- malformed, late, conflicting, and reverted calls;
- balances, fees, logs, and external effects when they affect utility;
- the observation available to every strategic actor.

Progress requires a named service assumption. Permissionless expiration means
that someone may submit an expiry transaction; it does not mean a transaction
will be included. Likewise, deterministic handler correctness does not realize
an exact source sampling law.

For strategic preservation, the service policy must be measurable from its
declared public observation. Delivery and receipt metadata visible to a player
must be reconstructible causally from that player's source history, or included
as a source-level signal. Deadline fairness must distinguish a request that was
never submitted, one censored after submission, and one that lost a permitted
competition with another valid request.

Source fallbacks remain language choices. The ledger can execute a compiled
expiration handler only when the checked application contains a legal source
continuation for that deadline. Silence, malformed input, and infrastructure
failure are not silently identified with that source choice.

A useful target chain is:

```text
native application
  -> ledger transactions and observations
  -> linked VM artifact
  -> named deployed-ledger semantics
```

Each arrow needs artifact identity and an execution theorem. Strategic results
add causal observation simulation and deviation translation; they cannot be
inferred from functional execution alone.
