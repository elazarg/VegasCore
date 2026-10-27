# Ideal authenticated commitments

The retained runtime uses ideal immutable candidate meanings and authentic
opening evidence. An opaque binding handle carries no observable candidate
value; an opening must match the accepted owned handle and the relevant guards.
Persistent private inputs are distinct from fresh commitment handles.

These are semantic interfaces, not implementations of signatures, cryptographic
hiding or binding. A concrete refinement must preserve authentication, opaque
observations, session/event binding and the modeled readiness evidence. A
sender-written identifier alone is not a proof of historical readiness.

Authentication and evidence delivery are distinct assumptions. The SE audit
coverage premises require conditional availability; public verifiability does
not supply that property. See the [open-problems guide](sequential-se-open-problems.md).
