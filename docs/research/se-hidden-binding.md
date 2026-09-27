# Hidden unusability: audit limitation, conditional simulation, SE obligation

## Decisive checked facts

An unusable binding is not publicly identifiable in general.
`VegasTests.UnusableBindingAudit.auditTrace_eq` compares actual reactive binding,
inclusion, granted revelation and withholding steps. Valid binding followed by
legal withholding and unusable binding followed by withholding have identical
public snapshots, including phase, input authors, pending packets and receipts.
Their private meanings remain different and fixed. `no_sound_detection` rules
out charging the latter while an audit is silent on the former.

That fact is **not** an SE impossibility. There is now a stronger positive result
than initial Nash simulation, in `Vegas/Source/ValueBindingContinuation.lean`:

- `bindValues_runFrom_publicOutcome_eq` repairs a pure continuation from any
  residual source configuration, preserving its registry, revelations and own
  action histories rather than resetting them.
- `exists_valueBinding_continuation_mixture` repairs every behavioral
  continuation, using one mixture for every configuration in a finite list.
- `exists_valueBinding_belief_mixture` preserves the joint law of any parameter
  of the starting configuration and the public result, for an arbitrary finite
  belief over configurations. The mixture is chosen before the hidden state.
- `exists_valueBinding_continuation_ge` gives a value-only continuation with
  conditional utility at least as high as the original continuation.
- `ValueBinding.admitted` makes every repaired policy legal under every existing
  commitment interface, including value-only admission.

These results cover the full existing source syntax: public chance, subsequent
bindings, deferred guards, disclosure, and withholding. They impose no equilibrium
or reachability premise on the starting belief. Opponents keep the same source
policies and observations. Utility may depend on persistent private parameters
and public results; it may not reward the hidden representation of a future
commitment that the repair deliberately changes.

## Why the repair is local enough, and why the current comparator is too strong

At the start of a continuation, replace any future failed binding with a
canonical valid value. At that binding's later disclosure, withhold instead.
The existing `Patched` invariant reconstructs the deviator's original view and
own actions; every other player's view and own history stays unchanged.
`bindValues_publicOutcome_eq` already proves this for arbitrary related residual
configurations, not only for initial execution.

The transformation edits a whole future policy. It is local to a continuation
and uniform across its hidden states, but it is not a replacement of only the
current action followed by unchanged play. In particular, replacing a failed
binding with a valid value and then leaving a later opening unchanged can alter
the public result. Failure of that one-action comparator is not strategic gain.

Sequential rationality already compares every whole continuation policy. The
required generic relaxation therefore allows an extra target action's future
behavior to be simulated by a mixture of whole source continuation policies,
instead of requiring one legal source action with the old continuation unchanged.
Every mixture component is bounded by source sequential rationality.

## Exact remaining native obligations

The conditional source result does not yet prove native SE preservation. The
native adapter must establish the following facts, rather than assume them:

1. From a retained native prefix, a privately unusable binding and the repaired
   source continuation give every **other** player corresponding future views.
   This includes accepted handles, response recall, pending observations and
   deferred-guard effects. The sender's own extra private information is mapped,
   not incorrectly identified with the source information state.
2. Opponents' prescribed policies must continue to agree at those corresponding
   views after the hidden departure. Agreement merely on the originally
   embedded execution histories is insufficient by itself.
3. A later observable departure is handled by the audit/collection argument.
   The conditional source simulation does not cover arbitrary leaked certificates,
   new public signaling, or arbitrary native opponents after such traffic.
4. New private information sites need rational continuations in one common
   consistency construction. Existing action-restriction completion supplies
   that mechanism only after its structural embedding and retained-belief
   hypotheses are actually instantiated.

The existing generic restriction proof can retain its consistency-completion and
one-shot-to-whole-policy machinery. Its retained-site comparison should accept
whole continuation mixtures. That change alone does not discharge obligations
1–3, and this note does not claim a completed full-language SE theorem.

## Guards and copying

Deferred guard rejection is not an unavoidable honest disclosure in the current
compiler: `reactiveResolutionPacket` emits withholding when the proposed opening
does not publish successfully. A raw opening that still carries a rejected
secret is extra traffic and may be audited. The source repair preserves guard
results because guard reads use public data and revelation results; its existing
proof covers the whole obligation registry.

In the current ideal runtime, binding acceptance requires ownership of the
candidate handle; a third party cannot bind another player's opaque handle as
its own source commitment. Certificates may be forwarded once known. Copying a
publicly disclosed value is source-representable; additional private certificate
disclosure is an information-flow obligation for the audit adapter.

A cryptographic backend that permits copying an opaque commitment without
knowing its value requires a separate analysis or a knowledge/nonmalleability
assumption. The checked conditional repair concerns unusable binding in the
existing ideal semantics and does not establish preservation for that larger
cryptographic action space.

**Conclusion:** no forward-SE counterexample from hidden unusability has been
established. We have proved its lack of conditional source best-response gain.
The remaining issue is a native information/continuation simulation and its
consistent extension, not a demonstrated need to expose malformed commitment
values in the source language.
